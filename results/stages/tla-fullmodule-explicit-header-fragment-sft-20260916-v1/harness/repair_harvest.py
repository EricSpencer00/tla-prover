"""W2.6 -- repair-shaped minimal-diff trace harvest (PLAN.md Stage-2 Round 3).

Amendment 16's failure analysis: the v2_sft2 corpus was generation-shaped, and
the fine-tune learned to rewrite specs wholesale instead of minimally repairing
them (B pass@1 12->10, pass@32 21->18). This module harvests the corrective
corpus: (broken spec, error evidence, minimal fix) triples, with a HARD
diff-minimality gate at corpus time so wholesale rewrites can never become
training pairs.

Source specs = the decontaminated W2 survivor corpus (results/runs/*/
w2_survivors.jsonl), NEVER the holdout. Per survivor:

  1. corrupt() -- one deterministic seeded mutation (same operator battery as
     Gate-2 framing B; seed derived from the survivor's spec text, so the
     corruption is reproducible from the ledger alone).
  2. Verify the corruption is REAL: SANY still parses, TLC now fails
     (a corruption TLC still accepts carries no repair signal -- skipped).
  3. Ask the model to repair, k samples, with the TLC error evidence in the
     prompt (harness.gen_eval.build_repair_prompt, unchanged).
  4. Accept a sample only if: SANY pass, TLC pass non-vacuous against the
     survivor's own cfg, AND diff_minimality(broken, repaired) <= threshold.
  5. Ledger every attempt (append-only, resumable); accepted triples go to
     harvest_triples.jsonl ready for harmony SFT rendering.

Zero-spend testing: model is injected (same Model interface as everywhere).
"""
import argparse
import difflib
import os
import hashlib
import json
import re
import time
from pathlib import Path

from .gen_eval import (NoCandidateMutation, build_repair_prompt, corrupt,
                       extract_module)
from .runner import check_sany, check_tlc, module_name

# Accepted repair must change at most this fraction of the broken module's
# lines (unified-diff changed-line ratio). The Gate-2 corruption is a single
# operator swap, so an honest minimal repair touches ~1 line; 0.15 leaves room
# for legitimate multi-line fixes while rejecting wholesale rewrites (baseline
# B wholesale rewrites measured 0.5-1.0 in the 2026-07-14 autopsy).
DIFF_MINIMALITY_THRESHOLD = 0.15
CORRUPTION_TRIES = 10
MAX_TOKENS = 16384
TEMPERATURE = 0.8


def diff_minimality(broken: str, repaired: str) -> float:
    """Fraction of lines changed by the repair: (added + removed) /
    (len(broken_lines) + len(repaired_lines)), via difflib unified diff.
    0.0 = identical; a one-line swap on a 30-line module ~= 0.033; a wholesale
    rewrite OR deletion -> ~1.0 (both sides in the denominator so shrinking
    the module doesn't score as "minimal"). Whitespace-only line changes count
    (format churn is exactly the style drift we're gating out)."""
    b_lines = broken.splitlines()
    r_lines = repaired.splitlines()
    denom = len(b_lines) + len(r_lines)
    if denom == 0:
        return 0.0
    if not b_lines or not r_lines:
        return 1.0
    changed = sum(1 for d in difflib.unified_diff(b_lines, r_lines, lineterm="", n=0)
                  if d[:1] in "+-" and d[:3] not in ("+++", "---"))
    return changed / denom


def corruption_seed_for(spec_text: str) -> int:
    """Deterministic per-survivor corruption seed: a pure function of the spec
    bytes, reproducible from the ledger alone (mirrors Gate-2's holdout-hash
    scheme without touching the holdout)."""
    return int(hashlib.sha256(spec_text.encode()).hexdigest()[:8], 16)


def load_survivor_specs(survivor_dirs):
    """Unique survivor (spec_text, cfg_text, module, seed_key) rows across run
    dirs; dedup by spec sha."""
    seen, out = set(), []
    for d in survivor_dirs:
        f = Path(d) / "w2_survivors.jsonl"
        if not f.exists():
            continue
        for line in f.read_text().splitlines():
            if not line.strip():
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not r.get("survived") or not r.get("spec_text"):
                continue
            sha = hashlib.sha256(r["spec_text"].encode()).hexdigest()
            if sha in seen:
                continue
            seen.add(sha)
            out.append({"spec_text": r["spec_text"], "cfg_text": r.get("cfg_text") or "",
                        "module": r.get("module"), "seed_key": r.get("seed_key"),
                        "spec_sha": sha})
    return out


def _tlc_evidence(mod, cfg_text, workdir, timeout):
    """(verdict, vacuity, log_tail) for a module already written into workdir.
    Writes the cfg alongside (check_tlc reads {mod}.cfg from workdir)."""
    (workdir / f"{mod}.cfg").write_text(cfg_text)
    verdict, vac, out, _ = check_tlc(mod, cfg_text, workdir, timeout)
    tail = out[-6000:] if out else ""
    return verdict, vac, tail


def harvest_one(surv, model, k, workroot, timeout=60):
    """Yield one attempt-ledger row per sample for a single survivor spec.
    Rows with accepted=True carry the full (broken, evidence, fixed) triple."""
    spec, cfg = surv["spec_text"], surv["cfg_text"]
    seed = corruption_seed_for(spec)
    base = {"seed_key": surv["seed_key"], "spec_sha": surv["spec_sha"],
            "corruption_seed": seed, "timestamp": time.time(), "model": model.id}

    # Try up to CORRUPTION_TRIES derived seeds for a VALID corruption (SANY
    # still parses, TLC detects the fault) -- mirrors gen_eval's
    # find_valid_corruption; a single unlucky seed must not discard the spec.
    wd = workroot / surv["spec_sha"][:16]
    wd.mkdir(parents=True, exist_ok=True)
    broken = mrec = evidence = None
    last_reason = "no_corruption_site"
    for attempt in range(CORRUPTION_TRIES):
        try:
            cand, cand_rec = corrupt(spec, seed + attempt)
        except NoCandidateMutation:
            break
        mod = module_name(cand)
        (wd / f"{mod}.tla").write_text(cand)
        sany_v, _, _ = check_sany(wd / f"{mod}.tla", wd, timeout)
        if sany_v != "pass":
            last_reason = "corruption_breaks_sany"
            continue
        tlc_v, _vac, ev = _tlc_evidence(mod, cfg, wd, timeout)
        if tlc_v == "pass":
            last_reason = "corruption_not_detected_by_tlc"
            continue
        broken, mrec, evidence = cand, {**cand_rec, "seed_offset": attempt}, ev
        break
    if broken is None:
        yield {**base, "sample": None, "accepted": False,
               "reject_reason": last_reason}
        return
    mod = module_name(broken)
    (wd / f"{mod}.tla").write_text(broken)

    prompt = build_repair_prompt(broken, evidence)
    # k samples are independent; prefetch them concurrently like gen_eval
    # (the 12.2h-serial-eval lesson, Amendment 16 W2.8)
    conc = int(os.environ.get("GEN_EVAL_CONCURRENCY", "1"))
    temps = [(i, 0.0 if i == 0 else TEMPERATURE) for i in range(k)]
    def _gen(it):
        return it[0], model.generate(prompt, 1, it[1], MAX_TOKENS)[0]
    if conc > 1 and k > 1:
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=min(conc, k)) as pool:
            replies = dict(pool.map(_gen, temps))
    else:
        replies = dict(_gen(t) for t in temps)
    for i, temp in temps:
        reply = replies[i]
        row = {**base, "sample": "greedy" if i == 0 else i, "mutation": mrec,
               "temperature": temp}
        fixed = extract_module(reply)
        if fixed is None:
            err = isinstance(reply, str) and reply.startswith("[api_error")
            yield {**row, "accepted": False,
                   "reject_reason": "api_error" if err else "no_module_extracted"}
            continue
        ratio = round(diff_minimality(broken, fixed), 4)
        row["diff_ratio"] = ratio
        if ratio > DIFF_MINIMALITY_THRESHOLD:
            yield {**row, "accepted": False, "reject_reason": "not_minimal_diff"}
            continue
        fmod = module_name(fixed)
        if fmod != mod:
            yield {**row, "accepted": False, "reject_reason": "module_renamed"}
            continue
        swd = wd / f"s{i}"
        swd.mkdir(exist_ok=True)
        (swd / f"{fmod}.tla").write_text(fixed)
        sv, _, _ = check_sany(swd / f"{fmod}.tla", swd, timeout)
        if sv != "pass":
            yield {**row, "accepted": False, "reject_reason": "repair_fails_sany"}
            continue
        tv, tvac, _ = _tlc_evidence(fmod, cfg, swd, timeout)
        if tv != "pass" or tvac:
            yield {**row, "accepted": False,
                   "reject_reason": f"repair_fails_tlc:{tv}" if tv != "pass"
                   else f"repair_vacuous:{tvac}"}
            continue
        yield {**row, "accepted": True, "broken_text": broken,
               "error_evidence": evidence, "fixed_text": fixed, "cfg_text": cfg}


def run_harvest(model, survivor_dirs, out_dir: Path, k: int, cap=None, timeout=60):
    """Resumable driver: out_dir/harvest_attempts.jsonl (every sample) +
    out_dir/harvest_triples.jsonl (accepted only). Resume key = (spec_sha,
    sample)."""
    # ABSOLUTE paths only: check_sany/check_tlc pass -Djava.io.tmpdir=<workdir>/jtmp
    # while running WITH cwd=workdir, so a relative workroot resolves to a
    # nonexistent nested path and SANY fails "Cannot find source file for module
    # Naturals" on every spec that EXTENDS a standard module (2026-07-16: cost a
    # full harvest pass, 257/260 false rejects).
    out_dir = Path(out_dir).resolve()
    out_dir.mkdir(parents=True, exist_ok=True)
    attempts = out_dir / "harvest_attempts.jsonl"
    triples = out_dir / "harvest_triples.jsonl"
    done = set()
    if attempts.exists():
        for line in attempts.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                done.add(r["spec_sha"])  # spec-level resume: all-or-nothing per spec
    survivors = load_survivor_specs(survivor_dirs)
    if cap:
        survivors = survivors[:cap]
    workroot = out_dir / "work"
    n_acc = n_att = 0
    with open(attempts, "a") as af, open(triples, "a") as tf:
        for idx, surv in enumerate(survivors, 1):
            if surv["spec_sha"] in done:
                continue
            for row in harvest_one(surv, model, k, workroot, timeout):
                af.write(json.dumps(row) + "\n")
                af.flush()
                n_att += 1
                if row.get("accepted"):
                    tf.write(json.dumps(row) + "\n")
                    tf.flush()
                    n_acc += 1
            print(f"[{idx}/{len(survivors)}] {surv['module']}: "
                  f"accepted so far {n_acc}/{n_att} attempts")
    print(f"harvest done: {n_acc} minimal-diff triples from {n_att} attempts -> {triples}")
    return n_acc


def main(argv=None):
    ap = argparse.ArgumentParser(prog="python3 -m harness.repair_harvest")
    ap.add_argument("--survivor-dirs", nargs="+", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--model", required=True, help="openai:<id> (OPENAI_BASE_URL/KEY)")
    ap.add_argument("--k", type=int, default=4)
    ap.add_argument("--cap", type=int, default=None)
    ap.add_argument("--timeout", type=int, default=60)
    a = ap.parse_args(argv)
    from .repair import make_model
    model = make_model(a.model)
    run_harvest(model, a.survivor_dirs, Path(a.out), a.k, a.cap, a.timeout)


if __name__ == "__main__":
    main()
