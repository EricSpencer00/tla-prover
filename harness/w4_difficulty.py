"""W4 difficulty probe: measure the base model's per-cell pass rate `p` on the
existing W4 corpus, WITHOUT regenerating a single cell.

Design: docs/designs/2026-08-03-w4-difficulty-probe.md

Why this exists
---------------
W4 has a quality axis and no difficulty axis. `tier` is "complex" on every
tagged row, `complexity_score` is a static structural metric (LOC / variables /
actions), and diamond/gold/silver/bronze grade *mutation kill-rate*. None of
those answer the question that decides whether a training row is worth its
tokens: can the student already do this?

Sancaktar et al. (arXiv:2603.24202) filter synthetic RL problems on empirical
student pass rate -- keep 0.01 < p < 0.97, drop "student never solved". This
module retro-fits the measurement onto the 5,010-row export so the same filter
can be evaluated here.

Scope note: `p = 0` cells are NOT waste under SFT. The paper's "hard problems
starve the reward signal" caveat is GRPO-specific; imitation learning is
precisely the tool for cells the student cannot reach on its own. The only
transferable rule being tested is "drop the p ~= 1 mass".
"""
from __future__ import annotations

import hashlib
import json
import math
import random
from pathlib import Path

from . import w4_corpus

#: Frozen so a re-run reproduces the same sample. Changing it invalidates every
#: number computed against the old sample_frozen.json -- pick a new run-id
#: instead of editing this.
DEFAULT_SEED = 20260803
DEFAULT_N = 300

#: Stratify on both, so the probe can report `p` per training arm AND test
#: whether the mutation-kill tiers carry any difficulty information at all.
STRATUM_FIELDS = ("arm", "tier_name")


def stratum_of(row: dict) -> tuple:
    """The (arm, tier_name) cell a row belongs to."""
    return tuple(row.get(f) for f in STRATUM_FIELDS)


def _largest_remainder(sizes: dict, n: int) -> dict:
    """Allocate `n` across strata proportionally to `sizes`, summing EXACTLY to
    n, capped by each stratum's own size.

    Hamilton's method (floor + largest fractional remainder), then a
    redistribution pass for strata whose quota exceeds their population. Ties
    break on the stratum key so the result is deterministic, not
    dict-order-dependent.
    """
    total = sum(sizes.values())
    if total == 0 or n <= 0:
        return {s: 0 for s in sizes}
    n = min(n, total)

    keys = sorted(sizes)
    alloc = {}
    fracs = []
    for s in keys:
        exact = n * sizes[s] / total
        alloc[s] = int(math.floor(exact))
        fracs.append((exact - alloc[s], s))

    # Hand out the leftover units to the largest fractional remainders.
    shortfall = n - sum(alloc.values())
    for _, s in sorted(fracs, key=lambda t: (-t[0], t[1]))[:shortfall]:
        alloc[s] += 1

    # A stratum can be allocated more than it has. Cap it and re-home the
    # excess into strata that still have headroom, repeatedly -- one pass is
    # not enough when the receiving strata are small too.
    while True:
        excess = sum(max(0, alloc[s] - sizes[s]) for s in keys)
        if excess == 0:
            return alloc
        for s in keys:
            alloc[s] = min(alloc[s], sizes[s])
        headroom = [s for s in keys if alloc[s] < sizes[s]]
        if not headroom:
            return alloc
        # Deterministic round-robin over the strata that can still absorb rows,
        # largest-population first so the spread stays roughly proportional.
        for s in sorted(headroom, key=lambda k: (-sizes[k], k)):
            if excess == 0:
                break
            take = min(excess, sizes[s] - alloc[s])
            alloc[s] += take
            excess -= take
        if excess == 0:
            return alloc


def select_sample(rows: list[dict], n: int = DEFAULT_N,
                  seed: int = DEFAULT_SEED) -> list[dict]:
    """A deterministic, (arm, tier_name)-stratified sample of `n` corpus rows.

    `rows` must already be graded (w4_corpus.grade_corpus), because the strata
    are the graded fields. Rows are sorted by seed_key before sampling so the
    draw does not depend on shard read order.
    """
    missing = [r.get("seed_key") for r in rows if not r.get("tier_name") or not r.get("arm")]
    if missing:
        raise ValueError(
            f"{len(missing)} row(s) are ungraded (e.g. {missing[:3]}); "
            "call w4_corpus.grade_corpus(rows) first"
        )

    buckets: dict[tuple, list[dict]] = {}
    for r in rows:
        buckets.setdefault(stratum_of(r), []).append(r)
    for s in buckets:
        buckets[s].sort(key=lambda r: r["seed_key"])

    alloc = _largest_remainder({s: len(v) for s, v in buckets.items()}, n)

    picked: list[dict] = []
    for s in sorted(buckets):
        k = alloc[s]
        if k <= 0:
            continue
        # A per-stratum RNG keyed on the stratum name: adding a new tier later
        # does not reshuffle the strata that already existed.
        rng = random.Random(f"{seed}:{s[0]}:{s[1]}")
        picked.extend(rng.sample(buckets[s], k))

    picked.sort(key=lambda r: r["seed_key"])
    return picked


def sample_sha256(seed_keys) -> str:
    """Digest over the SORTED, newline-joined seed_keys. Sorted so the hash is
    a property of the SET, not of the order it happened to be written in."""
    body = "\n".join(sorted(seed_keys))
    return hashlib.sha256(body.encode("utf-8")).hexdigest()


def freeze_sample(picked: list[dict], out_path, n: int = DEFAULT_N,
                  seed: int = DEFAULT_SEED,
                  corpus_rows: list[dict] | None = None) -> dict:
    """Write the frozen sample manifest. Every downstream number cites its
    sha256, so this file is append-once: re-freezing under a changed corpus
    produces a different hash and therefore a different run.

    Passing `corpus_rows` (the full graded corpus the sample was drawn from)
    additionally records which strata rounded to zero -- see
    manifest["strata_unsampled"].
    """
    keys = [r["seed_key"] for r in picked]
    strata = {}
    for r in picked:
        arm, tier = stratum_of(r)
        strata.setdefault(f"{arm}/{tier}", 0)
        strata[f"{arm}/{tier}"] += 1

    manifest = {
        "seed": seed,
        "n_requested": n,
        "n_selected": len(keys),
        "strata_counts": dict(sorted(strata.items())),
        "seed_keys": keys,
        "sha256": sample_sha256(keys),
    }
    if corpus_rows is not None:
        # Strata that exist in the corpus but rounded to zero. Proportional
        # allocation is kept deliberately pure -- forcing a floor of 1-2 rows
        # into a 0.14%-of-corpus stratum would bias the pooled estimate and
        # still yield a `p` with no resolution. Recording the omission keeps it
        # visible instead of silent, which is the part that actually matters.
        present = {f"{a}/{t}" for a, t in (stratum_of(r) for r in corpus_rows)}
        manifest["strata_unsampled"] = sorted(present - set(strata))
    out = Path(out_path)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(manifest, indent=2) + "\n")
    return manifest


def load_sample(path, rows: list[dict] | None = None) -> tuple[dict, list[dict]]:
    """Read a frozen manifest and re-attach the corpus rows it names.

    Verifies the manifest's own sha256 and that every named key is still in the
    corpus -- a key that vanished means the corpus moved under a frozen sample,
    which invalidates the run rather than merely shrinking it.
    """
    manifest = json.loads(Path(path).read_text())
    recomputed = sample_sha256(manifest["seed_keys"])
    if recomputed != manifest["sha256"]:
        raise ValueError(
            f"sample manifest sha256 mismatch: file says {manifest['sha256']}, "
            f"recomputed {recomputed}"
        )
    if rows is None:
        rows = w4_corpus.grade_corpus(w4_corpus.load_effective())
    by_key = {r["seed_key"]: r for r in rows}
    missing = [k for k in manifest["seed_keys"] if k not in by_key]
    if missing:
        raise ValueError(
            f"{len(missing)} frozen seed_key(s) are no longer in the corpus "
            f"(e.g. {missing[:3]}); the corpus moved under the frozen sample"
        )
    return manifest, [by_key[k] for k in manifest["seed_keys"]]


# ------------------------------------------------------------------ prompts

#: The two prompts a W4 row is associated with. They are NOT the same text, and
#: that is a finding, not a convenience:
#:
#:   "generation" -- w2_loop.generation_prompt(nl, module). Names the module,
#:     demands one ```tla block plus one ```cfg block, and requires a trailing
#:     `PROPERTY_INVARIANT: <Name>` line. EVERY survivor in the corpus was
#:     generated and verified under this contract.
#:
#:   "sft_user"   -- the bare `nl`, which is what corpus_prep.to_harmony_sft
#:     puts in the user turn. No module name, no output contract, no
#:     PROPERTY_INVARIANT line. The SFT target drops that line too
#:     (corpus_prep._target_block emits only the two fenced blocks).
#:
#: So the trained model is taught to answer a differently-shaped question with
#: a differently-shaped answer than the one every row was verified under.
#: "generation" is the probe's PRIMARY mode -- p measured there is the honest
#: "can the student clear this cell's own bar". "sft_user" runs on a small
#: secondary arm to size the mismatch as a number.
PROMPT_MODES = ("generation", "sft_user")


def probe_prompt(row: dict, mode: str = "generation") -> str:
    """The prompt shown to the student for one corpus row."""
    if mode not in PROMPT_MODES:
        raise ValueError(f"unknown prompt mode {mode!r}; expected one of {PROMPT_MODES}")
    nl = row.get("nl") or ""
    if not nl:
        raise ValueError(f"row {row.get('seed_key')!r} has no nl text")
    if mode == "sft_user":
        return nl
    module = row.get("module")
    if not module:
        raise ValueError(f"row {row.get('seed_key')!r} has no module name")
    # Imported here so the module stays importable without the w2 loop's own
    # (heavier) dependency chain for callers that only want select_sample.
    from .w2_loop import generation_prompt
    return generation_prompt(nl, module)


def prompt_sha256(prompt: str) -> str:
    """Recorded on every ledger row -- a `p` without its prompt is
    uninterpretable, and prompts have silently drifted here before (the
    required_signature cfg-substitution bug corrupted every framing-A number
    the project had recorded)."""
    return hashlib.sha256(prompt.encode("utf-8")).hexdigest()


# ---------------------------------------------------------------- the probe

#: Matches the eval arms and w2_loop's own internal draw, so `p` is measured
#: under the sampling regime the project already reports pass@k under.
TEMPERATURE = 0.8
MAX_TOKENS = 8192

#: Row fields written to rows.jsonl. Fixed here so a schema change is a visible
#: diff rather than a silent drift (the export/audit pair has drifted twice).
ROW_FIELDS = ("seed_key", "arm", "tier_name", "mode", "sample_id", "temperature",
              "survived", "rejection_reason", "mutation_evidence", "kill_rate",
              "distinct_states", "prompt_sha256", "model", "k", "api_error")


class _OneShot:
    """Feeds one pre-generated reply into the verifier. Same shape as
    w4_verify_cell._OneShot: the verify path builds its own prompt and this
    ignores it, so verification is prompt-mode-independent by construction."""
    id = "probe-candidate"

    def __init__(self, reply):
        self.reply = reply
        self.calls = 0

    def generate(self, prompt, n, temperature, max_tokens):
        self.calls += 1
        if self.calls > 1:
            raise AssertionError("one-shot verifier: no repair iterations here")
        return [self.reply]


def is_api_error(reply: str) -> bool:
    return isinstance(reply, str) and reply.startswith("[api_error")


def verify_reply(reply: str, row: dict, workdir, timeout: int = 60) -> dict:
    """Run one student reply through the corpus's OWN gate stack, once.

    max_iters=1 is load-bearing: repair iterations would measure the loop, not
    the student, and the loop is exactly what this probe must hold fixed.
    Decontam is skipped -- see the design doc; the probe asks "can the student
    produce a passing cell", not "may this row be admitted".
    """
    from .w2_loop import run_loop_for_seed
    wd = Path(workdir).resolve()   # absolute: java.io.tmpdir / SANY path trap
    wd.mkdir(parents=True, exist_ok=True)
    return run_loop_for_seed(
        _OneShot(reply), row["nl"], row["module"], wd,
        timeout=timeout, max_iters=1,
        require_liveness=(row.get("arm") == "liveness"),
    )


def probe_cell(model, row: dict, k: int, mode: str, workroot,
               timeout: int = 60, skip_samples: set | None = None,
               verify=None) -> list[dict]:
    """Draw k samples for one cell and verify each. Returns k ledger rows
    (fewer if `skip_samples` already has some, for resume).

    `verify` defaults to verify_reply (real SANY/TLC/mutation). It is a
    parameter so the loop's bookkeeping -- resume, api_error handling, ledger
    schema -- is testable without Java.
    """
    import shutil

    verify = verify or verify_reply
    skip_samples = skip_samples or set()
    wanted = [i for i in range(k) if i not in skip_samples]
    if not wanted:
        return []

    prompt = probe_prompt(row, mode)
    psha = prompt_sha256(prompt)
    replies = model.generate(prompt, len(wanted), TEMPERATURE, MAX_TOKENS)

    safe_key = row["seed_key"].replace("::", "__").replace("/", "_")
    out = []
    for sample_id, reply in zip(wanted, replies):
        base = {
            "seed_key": row["seed_key"],
            "arm": row.get("arm"),
            "tier_name": row.get("tier_name"),
            "mode": mode,
            "sample_id": sample_id,
            "temperature": TEMPERATURE,
            "prompt_sha256": psha,
            "model": getattr(model, "id", "unknown"),
            "k": k,
            "api_error": False,
        }
        if is_api_error(reply):
            # Never scored as a failure -- an endpoint hiccup that reads as
            # "the student could not do it" is how a p estimate silently
            # becomes a measurement of uptime.
            out.append({**base, "survived": None, "api_error": True,
                        "rejection_reason": reply[:200],
                        "mutation_evidence": None, "kill_rate": None,
                        "distinct_states": None})
            continue
        wd = Path(workroot).resolve() / safe_key / f"s{sample_id}"
        try:
            v = verify(reply, row, wd, timeout=timeout)
            out.append({**base,
                        "survived": bool(v.get("survived")),
                        "rejection_reason": v.get("rejection_reason"),
                        "mutation_evidence": v.get("mutation_evidence"),
                        "kill_rate": v.get("kill_rate"),
                        "distinct_states": v.get("distinct_states")})
        finally:
            shutil.rmtree(wd, ignore_errors=True)   # 2,400 TLC workdirs otherwise
    return out


def load_done(rows_path) -> dict:
    """{seed_key: {sample_id, ...}} already in the ledger, for resume."""
    p = Path(rows_path)
    done: dict[str, set] = {}
    if not p.exists():
        return done
    for line in p.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        # An api_error row is NOT done -- it carries no measurement, so a
        # resume must re-draw it rather than inherit the outage.
        if r.get("api_error"):
            continue
        done.setdefault(r.get("seed_key"), set()).add(r.get("sample_id"))
    return done


def run_probe(model, rows: list[dict], k: int, mode: str, rundir,
              timeout: int = 60, concurrency: int = 1, verify=None) -> dict:
    """Probe every row, appending to <rundir>/rows.jsonl as results land.

    The ledger is append-only and is the only source of truth; the returned
    summary is advisory and must never be the source of a reported number.
    """
    import threading
    from concurrent.futures import ThreadPoolExecutor

    rundir = Path(rundir)
    rundir.mkdir(parents=True, exist_ok=True)
    rows_path = rundir / "rows.jsonl"
    done = load_done(rows_path)

    write_lock = threading.Lock()
    counts = {"written": 0, "api_error": 0, "survived": 0}

    def work(row):
        got = probe_cell(model, row, k, mode, rundir / "work", timeout=timeout,
                         skip_samples=done.get(row["seed_key"], set()),
                         verify=verify)
        with write_lock:
            with rows_path.open("a") as fh:
                for r in got:
                    fh.write(json.dumps({f: r.get(f) for f in ROW_FIELDS}) + "\n")
                    counts["written"] += 1
                    counts["api_error"] += bool(r.get("api_error"))
                    counts["survived"] += bool(r.get("survived"))
        return len(got)

    todo = [r for r in rows if len(done.get(r["seed_key"], set())) < k]
    if concurrency > 1:
        with ThreadPoolExecutor(max_workers=concurrency) as ex:
            list(ex.map(work, todo))
    else:
        for r in todo:
            work(r)

    return {"cells": len(todo), "rows_written": counts["written"],
            "api_errors": counts["api_error"], "survived": counts["survived"],
            "rows_path": str(rows_path)}


# --------------------------------------------------------------------- CLI

def _cmd_probe(a) -> int:
    from .repair import make_model

    manifest, rows = load_sample(a.sample)
    if a.limit:
        rows = rows[:a.limit]
    model = make_model(a.model)
    rundir = Path(a.rundir)
    rundir.mkdir(parents=True, exist_ok=True)

    # Rule 8: the run must carry its own provenance.
    (rundir / "config.json").write_text(json.dumps({
        "sample": str(a.sample),
        "sample_sha256": manifest["sha256"],
        "n_cells": len(rows),
        "k": a.k,
        "mode": a.mode,
        "model": a.model,
        "temperature": TEMPERATURE,
        "max_tokens": MAX_TOKENS,
        "timeout_s": a.timeout,
        "max_iters": 1,
        "skip_decontam": True,
        "repro": (f"python3 -m harness.w4_difficulty probe --sample {a.sample} "
                  f"--model {a.model} --k {a.k} --mode {a.mode} "
                  f"--rundir {a.rundir}"),
    }, indent=2) + "\n")

    print(f"probing {len(rows)} cells x k={a.k} mode={a.mode} model={a.model}")
    s = run_probe(model, rows, a.k, a.mode, rundir,
                  timeout=a.timeout, concurrency=a.concurrency)
    print(f"cells={s['cells']} rows={s['rows_written']} "
          f"survived={s['survived']} api_errors={s['api_errors']}")
    print(f"ledger: {s['rows_path']}")
    if s["api_errors"]:
        print(f"\nFAIL: {s['api_errors']} api_error row(s). They carry no "
              f"measurement and are NOT scored as failures -- re-run to resume "
              f"and re-draw them before reporting any number.")
        return 1
    return 0


def _cmd_freeze(a) -> int:
    rows = w4_corpus.grade_corpus(w4_corpus.load_effective())
    if not rows:
        print("FAIL: no corpus rows found (run from the repo root)")
        return 1
    picked = select_sample(rows, n=a.n, seed=a.seed)
    out = Path(a.out)
    if out.exists() and not a.force:
        print(f"FAIL: {out} already exists; a frozen sample is append-once. "
              f"Use a new --run-id, or --force only to regenerate a sample no "
              f"run has cited yet.")
        return 1
    m = freeze_sample(picked, out, n=a.n, seed=a.seed, corpus_rows=rows)
    print(f"corpus {len(rows)} rows -> sample {m['n_selected']}  seed={m['seed']}")
    for s, c in m["strata_counts"].items():
        print(f"  {s:22s} {c}")
    if m.get("strata_unsampled"):
        print(f"  unsampled (rounded to zero): {', '.join(m['strata_unsampled'])}")
    print(f"sha256 {m['sha256']}")
    print(f"wrote {out}")
    return 0


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(prog="python3 -m harness.w4_difficulty")
    sub = ap.add_subparsers(dest="cmd", required=True)

    f = sub.add_parser("freeze", help="draw and freeze the stratified sample")
    f.add_argument("--out", default="results/runs/w4-difficulty-v1/sample_frozen.json")
    f.add_argument("--n", type=int, default=DEFAULT_N)
    f.add_argument("--seed", type=int, default=DEFAULT_SEED)
    f.add_argument("--force", action="store_true",
                   help="overwrite an existing manifest (only safe before any "
                        "run has cited its sha256)")
    f.set_defaults(fn=_cmd_freeze)

    p = sub.add_parser("probe", help="draw k samples per cell and verify each")
    p.add_argument("--sample", default="results/runs/w4-difficulty-v1/sample_frozen.json")
    p.add_argument("--model", required=True, help="openai:<id> | stub")
    p.add_argument("--k", type=int, default=8)
    p.add_argument("--mode", choices=PROMPT_MODES, default="generation")
    p.add_argument("--rundir", default="results/runs/w4-difficulty-v1")
    p.add_argument("--timeout", type=int, default=60)
    p.add_argument("--concurrency", type=int, default=1,
                   help="TLC is the bottleneck, not the model")
    p.add_argument("--limit", type=int, default=0, help="first N cells (smoke)")
    p.set_defaults(fn=_cmd_probe)

    a = ap.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    raise SystemExit(main())
