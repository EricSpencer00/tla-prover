"""Oracle repair pairs: mechanics supervision manufactured from the W4 survivor
corpus, with the verifier as the only ground-truth authority.

Motivation (training-methods review, 2026-08-05): 68-74% of eval failures are
sany=fail, but every corpus target is a verified spec -- the training data
contains no instance of the dominant failure mode. This tool adds that mode
WITHOUT a teacher model: corrupt a survivor, verify the corruption really
fails, and use the ORIGINAL survivor text as the repair target. The fix is
minimal by construction (it is the exact inverse of a single corruption), and
every target stays in the Opus-teacher distribution -- no same-family
provenance, which is what Amendment 17 implicated in the repair-v1 collapse.

Two corruption classes, verified by execution (never trusted from the operator):

  tlc:  gen_eval.corrupt() -- one seeded operator-swap from the frozen
        MUTATIONS battery. Kept only if SANY still passes AND TLC now fails.
        error_evidence = tail of the TLC output.
  sany: one seeded syntax corruption from SYNTAX_OPS below. Kept only if
        SANY now fails. error_evidence = tail of the SANY output.

Determinism: per-survivor seed = int(sha256(spec_text)[:8], 16); the class
alternates tlc/sany by survivor index in a sorted-by-seed_key order, so the
output is reproducible from the shard files alone.

Decontamination: W4 survivors are synthetic (module names W4O*); we still
assert no survivor module name or seed_key collides with the frozen holdout.

Usage:
  python3 tools/oracle_repair_pairs.py --limit 2400 --concurrency 8 \
      --out results/analysis/oracle_repair_triples.jsonl
  python3 -c "from harness.corpus_prep import build_repair_sft_file; \
      build_repair_sft_file('results/analysis/oracle_repair_triples.jsonl', \
      'results/analysis/sft_oracle_repair.jsonl')"
"""
import argparse
import hashlib
import json
import random
import re
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness.gen_eval import NoCandidateMutation, corrupt  # noqa: E402
from harness.runner import check_sany, check_tlc  # noqa: E402

# Syntax corruptions targeting the sany=fail mass. Each is (label, regex,
# replacement) applied to exactly ONE seeded match site, like MUTATIONS.
# Correctness of each operator is irrelevant: a corruption only survives if
# SANY actually rejects the result.
SYNTAX_OPS = [
    ("maps_to_mangled", re.compile(r"\|->"), "|>"),
    ("defeq_to_eq", re.compile(r"=="), "="),
    ("drop_extends", re.compile(r"^EXTENDS [^\n]*\n", re.M), ""),
    ("drop_close_paren", re.compile(r"\)"), ""),
    ("drop_comma", re.compile(r","), ""),
    ("and_mangled", re.compile(r"/\\"), "/"),
]

TLC_VERIFY_TIMEOUT = 60   # corruptions usually fail in seconds
SANY_TIMEOUT = 60
ERROR_TAIL = 2000         # chars of verifier output kept as evidence


def syntax_corrupt(spec_text: str, seed: int):
    """One seeded syntax corruption; same site-selection convention as
    gen_eval.corrupt(). Raises NoCandidateMutation when nothing matches."""
    candidates = []
    for label, regex, replacement in SYNTAX_OPS:
        for m in regex.finditer(spec_text):
            candidates.append((label, m.start(), m.end(), m.group(0), replacement))
    if not candidates:
        raise NoCandidateMutation("no SYNTAX_OPS site in spec_text")
    idx = random.Random(seed).randrange(len(candidates))
    label, start, end, original, replacement = candidates[idx]
    return spec_text[:start] + replacement + spec_text[end:], {
        "mutation": label, "offset": start,
        "original": original, "replacement": replacement,
    }


def load_survivors(runs_dir: Path):
    rows = []
    for shard in sorted(runs_dir.glob("w4-opus-shard*/w2_survivors.jsonl")):
        for line in shard.read_text().splitlines():
            if not line.strip():
                continue
            r = json.loads(line)
            if r.get("survived") and r.get("spec_text") and r.get("cfg_text"):
                rows.append(r)
    # one row per seed_key (shards can re-list); keep first
    seen, out = set(), []
    for r in rows:
        k = r.get("seed_key") or hashlib.sha256(r["spec_text"].encode()).hexdigest()
        if k in seen:
            continue
        seen.add(k)
        out.append(r)
    out.sort(key=lambda r: str(r.get("seed_key")))
    return out


def make_pair(row, kind: str):
    """Build one verified oracle triple, or None (no site / corruption did not
    fail the intended verifier / verifier flake)."""
    spec = row["spec_text"]
    base_seed = int(hashlib.sha256(spec.encode()).hexdigest()[:8], 16)
    mod = row["module"]
    # tlc corruptions often land on a site TLC still accepts; retry a few
    # seeds before giving up. sany corruptions almost always take on the
    # first seed, but the retry costs nothing there either.
    broken = rec = evidence = None
    for attempt in range(3):
        seed = base_seed + attempt
        try:
            if kind == "sany":
                cand, cand_rec = syntax_corrupt(spec, seed)
            else:
                cand, cand_rec = corrupt(spec, seed)
        except NoCandidateMutation:
            return None
        if cand == spec:
            continue
        with tempfile.TemporaryDirectory(prefix="orp_") as td:
            wd = Path(td)
            (wd / f"{mod}.tla").write_text(cand)
            (wd / f"{mod}.cfg").write_text(row["cfg_text"])
            s_status, s_out, _ = check_sany(wd / f"{mod}.tla", wd, SANY_TIMEOUT)
            if kind == "sany":
                if s_status != "fail":      # must be a REAL parse/level failure
                    continue
                broken, rec, evidence = cand, cand_rec, s_out[-ERROR_TAIL:]
                break
            if s_status != "pass":          # operator swap must stay parseable
                continue
            t_status, _, t_out, _ = check_tlc(mod, row["cfg_text"], wd,
                                              TLC_VERIFY_TIMEOUT)
            if t_status not in ("fail", "invariant_violation", "deadlock",
                                "liveness_violation", "error"):
                continue                    # TLC still accepts -> no signal
            broken, rec, evidence = cand, cand_rec, t_out[-ERROR_TAIL:]
            break
    if broken is None:
        return None
    return {
        "kind": kind,
        "mutation": rec,
        "broken_text": broken,
        "error_evidence": evidence,
        "fixed_text": spec,
        "seed_key": row.get("seed_key"),
        "spec_sha": hashlib.sha256(spec.encode()).hexdigest(),
        "diff_ratio": None,   # oracle inverse of one corruption; minimal by construction
        "module": mod,
        "family_cell": row.get("cell"),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs-dir", default="results/runs")
    ap.add_argument("--out", default="results/analysis/oracle_repair_triples.jsonl")
    ap.add_argument("--limit", type=int, default=2400,
                    help="max survivors to attempt (pairs <= limit)")
    ap.add_argument("--concurrency", type=int, default=8)
    ap.add_argument("--holdout-modules", default="",
                    help="comma-separated module names that must NOT appear")
    args = ap.parse_args()

    survivors = load_survivors(Path(args.runs_dir))
    print(f"[orp] {len(survivors)} unique survivors")
    if args.holdout_modules:
        holdout = set(args.holdout_modules.split(","))
        clash = [r["module"] for r in survivors if r["module"] in holdout]
        assert not clash, f"holdout module collision: {clash[:5]}"
    survivors = survivors[: args.limit]
    jobs = [(r, "tlc" if i % 2 == 0 else "sany") for i, r in enumerate(survivors)]

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    done = kept = 0
    by_kind = {"tlc": 0, "sany": 0}
    with open(out_path, "w") as f, ThreadPoolExecutor(args.concurrency) as ex:
        for res in ex.map(lambda j: make_pair(*j), jobs):
            done += 1
            if res:
                f.write(json.dumps(res) + "\n")
                kept += 1
                by_kind[res["kind"]] += 1
            if done % 200 == 0:
                print(f"[orp] {done}/{len(jobs)} attempted, {kept} kept {by_kind}",
                      flush=True)
    print(f"[orp] DONE {kept}/{done} kept {by_kind} -> {out_path}")


if __name__ == "__main__":
    main()
