"""Estimate GRPO group reward variance from an existing Gate-2 ledger.

GRPO produces a gradient only when a sampled group of G completions scores
non-uniformly; when every member scores the same the advantage is zero and the
update is zero. The RL era (2026-03/04) died with `frac_reward_zero_std` at
0.72-0.78 on every run.

Because Gate-2 draws k=32 samples per spec, that statistic is estimable offline
from a ledger: resample groups of size G from the 32 recorded outcomes and count
how often the group is uniform. This is the go/no-go gate for restarting RL
(docs/designs/2026-08-12-sany-tlc-grpo.md) and costs no compute.

Two caveats the number carries:
  * Ledger draws are at the Gate-2 sampling temperature (0.8); rollouts would run
    hotter, which should raise diversity and lower zero-variance. The estimate is
    therefore likely conservative, but it IS an extrapolation.
  * Sampling is without replacement from 32 recorded draws, which slightly
    understates the variance an unbounded sampler would produce.

Usage:
  python3 tools/group_variance.py                       # default arms
  python3 tools/group_variance.py --runs gate2-w4dgm-120b-A --groups 8,16
"""
import argparse
import collections
import json
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

REPO = Path(__file__).resolve().parent.parent

# SANY->TLC staircase. Tier 3 requires a non-vacuous TLC pass; verdict_of already
# demotes a vacuous pass to fail:vacuous:*, so it lands in tier 2 here.
TIERS = {3: "pass", 2: "TLC rejects", 1: "SANY fails", 0: "no module"}


def tier(verdict: str) -> int:
    if verdict == "pass":
        return 3
    if verdict.startswith("fail:tlc") or verdict.startswith("fail:vacuous"):
        return 2
    if verdict.startswith("fail:sany"):
        return 1
    return 0


def binary(verdict: str) -> int:
    return 1 if verdict == "pass" else 0


def load(run: str):
    """(spec -> [verdict]) with keep-first dedup, corruption rows dropped, and
    api_error excluded (an unmeasured draw, not an outcome)."""
    path = REPO / "results/runs" / run / "rows.jsonl"
    seen, by_spec = set(), collections.defaultdict(list)
    for line in path.read_text(errors="replace").splitlines():
        if not line.strip():
            continue
        try:
            d = json.loads(line)
        except json.JSONDecodeError:
            continue
        if d.get("sample") == "corruption":
            continue
        key = (d.get("spec"), d.get("sample"))
        if key in seen:
            continue
        seen.add(key)
        if d.get("verdict") == "api_error":
            continue
        by_spec[str(d.get("spec"))].append(d.get("verdict", ""))
    return by_spec


def zero_var_frac(by_spec, G, reward, per_spec_trials, rng):
    zero = tot = 0
    for verdicts in by_spec.values():
        if len(verdicts) < G:
            continue
        scored = [reward(v) for v in verdicts]
        for _ in range(per_spec_trials):
            if len(set(rng.sample(scored, G))) == 1:
                zero += 1
            tot += 1
    return (zero / tot) if tot else float("nan")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", default="e2c-baseline-120b-a,gate2-w4dg-120b-A3,"
                                      "gate2-w4dgp-120b-A")
    ap.add_argument("--groups", default="4,8,16")
    ap.add_argument("--trials", type=int, default=200, help="resamples per spec")
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()

    groups = [int(g) for g in args.groups.split(",")]
    rng = random.Random(args.seed)

    print(f"{'arm':26} {'G':>3} {'binary':>8} {'staircase':>10}   "
          f"(abort floor 0.55; historical failure band 0.72-0.78)")
    for run in args.runs.split(","):
        by_spec = load(run)
        if not by_spec:
            print(f"{run:26}  no rows")
            continue
        for G in groups:
            b = zero_var_frac(by_spec, G, binary, args.trials, rng)
            s = zero_var_frac(by_spec, G, tier, args.trials, rng)
            flag = "  <-- viable" if s < 0.55 else ""
            print(f"{run:26} {G:>3} {b:>7.1%} {s:>10.1%}{flag}")
        counts = collections.Counter(tier(v) for vs in by_spec.values() for v in vs)
        n = sum(counts.values())
        hist = ", ".join(f"{TIERS[t]} {counts[t]/n:.1%}" for t in (0, 1, 2, 3))
        print(f"{'':26}     tiers: {hist}  (n={n})")


if __name__ == "__main__":
    main()
