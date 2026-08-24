"""Score a framing-L arm against its open-loop framing-A control.

Implements the analysis rule pre-registered in
docs/designs/2026-08-24-framing-L-verifier-in-the-loop.md:

  L counts as a win only at >= +5 specs, or paired McNemar exact p < 0.05.
  A smaller gain is reported as null -- the measured single-run noise floor for
  spec-level pass@32 is +/-1-2 specs (docs/W4DG_GATE2_SESSION_2026-07-29.md S2).

Both arms are re-scored from rows.jsonl with keep-first dedup. summary.json is
never read: the base arm's committed summary says 1/30 and the ledger says 12/30.

Usage: python3 tools/loop_vs_open.py results/runs/<loop-run> results/runs/<open-run>
"""
import collections
import json
import math
import sys
from pathlib import Path


def ledger(run_dir):
    """spec -> (passed, rows) with keep-first dedup on (spec, sample)."""
    seen = {}
    for line in (Path(run_dir) / "rows.jsonl").read_text().splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        if str(r.get("sample")) == "corruption":
            continue
        seen.setdefault((r.get("spec"), str(r.get("sample"))), r)
    by = collections.defaultdict(list)
    for r in seen.values():
        by[r["spec"]].append(r)
    return by


def mcnemar_exact(b, c):
    """Two-sided exact binomial on the discordant pairs (b gains, c losses)."""
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    tail = sum(math.comb(n, i) for i in range(0, k + 1)) / (2 ** n)
    return min(1.0, 2 * tail)


def main(loop_dir, open_dir):
    L, A = ledger(loop_dir), ledger(open_dir)
    specs = sorted(set(L) | set(A), key=lambda s: int(s) if s.isdigit() else 0)

    def solved(by, s):
        return any(r.get("verdict") == "pass" for r in by.get(s, []))

    gains = [s for s in specs if solved(L, s) and not solved(A, s)]
    losses = [s for s in specs if solved(A, s) and not solved(L, s)]
    nL = sum(1 for s in specs if solved(L, s))
    nA = sum(1 for s in specs if solved(A, s))
    p = mcnemar_exact(len(gains), len(losses))

    print(f"specs                 : {len(specs)}")
    print(f"open-loop (control)   : {nA}/{len(specs)}   {Path(open_dir).name}")
    print(f"closed-loop (framing L): {nL}/{len(specs)}   {Path(loop_dir).name}")
    print(f"delta                 : {nL - nA:+d}  (gained {len(gains)}: {gains}; "
          f"lost {len(losses)}: {losses})")
    print(f"McNemar exact 2-sided : p = {p:.4f}")
    win = (nL - nA) >= 5 or p < 0.05
    print(f"\nPRE-REGISTERED VERDICT: {'WIN' if win else 'NULL'} "
          f"(rule: >= +5 specs OR p < 0.05)")

    calls, rungs = [], collections.Counter()
    for s in specs:
        for r in L.get(s, []):
            if r.get("verdict") == "pass":
                calls.append((s, r.get("calls_used"), r.get("round"), r.get("rung_in")))
                rungs[r.get("rung_in")] += 1
    budget = json.loads((Path(loop_dir) / "config.json").read_text()) \
        .get("budget", {}).get("model_calls_per_spec", "?")
    print(f"\ncalls to solve (framing L), budget {budget}:")
    for s, c, rnd, rung in sorted(calls, key=lambda x: (x[1] or 0)):
        print(f"  spec {s:>4}  {str(c):>3} calls  round {rnd}  entered as {rung}")
    solved_by_repair = sum(1 for _s, _c, rnd, _r in calls if rnd and rnd > 0)
    print(f"\nsolved on a REPAIR round (not a fresh generation): "
          f"{solved_by_repair}/{len(calls)}")
    print("rung the solving call was entered as:", dict(rungs))

    # per-sample rates, for comparability with every prior arm
    for name, by in (("open-loop", A), ("framing L", L)):
        rows = [r for s in specs for r in by.get(s, [])]
        n = len(rows)
        sany = sum(1 for r in rows if r.get("sany") == "pass")
        tlc = sum(1 for r in rows if r.get("tlc") in ("pass", "pass_expected_violation"))
        print(f"{name:>10}: {n:4d} rows  per-sample SANY {sany/max(n,1):5.1%}  "
              f"TLC {tlc/max(n,1):5.1%}")
    return 0 if win else 0


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], sys.argv[2]))
