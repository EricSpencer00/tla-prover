#!/usr/bin/env python3
"""Row-level re-analysis and power projection for framing-A Gate-2 arms.

Motivation
----------
pass@32 collapses 32 Bernoulli draws per spec into one bit, then sums 30 bits.
That discards almost all the evidence and makes the headline a threshold
statistic on a binomial, which is why it swung 11 -> 15 -> 16 across arms and
why W4DG_GATE2_SESSION_2026-07-29.md measured spec 30 going 5 -> 1 between two
runs of the SAME model on a byte-identical prompt.

The per-sample pass rate uses all 990 rows instead of 30 bits. This script
reports it, tests differences with a two-level bootstrap that reproduces the
observed noise floor, and projects what it would take to reach significance.

Comparisons are only formed between specs whose prompt_sha256 matches, so the
required_signature fix (which changed 13/30 framing-A prompts) cannot silently
contaminate a cross-arm delta.

Usage
-----
    python3 tools/rowlevel_power.py                     # default arm set
    python3 tools/rowlevel_power.py RUN_A RUN_B ...     # explicit runs
"""
import json
import math
import pathlib
import random
import sys
from collections import defaultdict

ROOT = pathlib.Path(__file__).resolve().parent.parent / "results" / "runs"
ITERS = 20000

DEFAULT_RUNS = ["e2c-baseline-120b-a", "gate2-v2-120b-A",
                "gate2-w4dg-120b-A", "gate2-w4dg-120b-A3"]

# (baseline, candidate, label). The first entry is a control: same model, same
# prompts, different run. It MUST come out null -- if it does not, the method is
# overstating significance and nothing below it can be trusted.
DEFAULT_PAIRS = [
    ("gate2-w4dg-120b-A", "gate2-w4dg-120b-A3", "CONTROL same model/prompts"),
    ("e2c-baseline-120b-a", "gate2-v2-120b-A", "v2 SFT vs untuned base"),
    ("e2c-baseline-120b-a", "gate2-w4dg-120b-A", "W4-diamond-gold vs untuned base"),
    ("gate2-v2-120b-A", "gate2-w4dg-120b-A", "W4-diamond-gold vs v2 SFT"),
]


def load(run):
    """{spec: {"o": [0/1 per sample], "prompt": sha}} for framing-A temp>0 rows.

    The greedy row is dropped: it is the pass@1 arm at temperature 0 and is not
    exchangeable with the k=32 temperature-0.8 samples.
    """
    path = ROOT / run / "rows.jsonl"
    if not path.exists():
        return None
    per = defaultdict(lambda: {"o": [], "prompt": None})
    for line in path.open():
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        if r.get("framing") != "A" or r.get("sample") == "greedy":
            continue
        per[r["spec"]]["o"].append(
            1 if str(r.get("verdict", "")).startswith("pass") else 0)
        per[r["spec"]]["prompt"] = r.get("prompt_sha256")
    return dict(per)


def wilson(k, n, z=1.96):
    if not n:
        return 0.0, 0.0
    p = k / n
    d = 1 + z * z / n
    c = (p + z * z / (2 * n)) / d
    h = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d
    return max(0.0, c - h), min(1.0, c + h)


def comparable(a, b):
    """Specs present in both arms under a byte-identical prompt."""
    return [s for s in a
            if s in b and a[s]["prompt"] == b[s]["prompt"]
            and a[s]["o"] and b[s]["o"]]


def rate(arm, s):
    return sum(arm[s]["o"]) / len(arm[s]["o"])


def bootstrap(a, b, specs, resample_specs=True, resample_rows=True,
              iters=ITERS, seed=0):
    """Paired bootstrap of mean(b) - mean(a) over specs.

    resample_rows is what makes this honest: holding each spec's measured rate
    fixed would ignore the within-spec binomial noise that the session doc
    observed directly.
    """
    rng = random.Random(seed)
    draws = []
    for _ in range(iters):
        picks = ([specs[rng.randrange(len(specs))] for _ in specs]
                 if resample_specs else specs)
        acc = 0.0
        for s in picks:
            if resample_rows:
                for arm, sign in ((b, 1.0), (a, -1.0)):
                    o = arm[s]["o"]
                    acc += sign * sum(o[rng.randrange(len(o))] for _ in o) / len(o)
            else:
                acc += rate(b, s) - rate(a, s)
        draws.append(acc / len(picks))
    draws.sort()
    lo, hi = draws[int(.025 * iters)], draws[int(.975 * iters)]
    below = sum(1 for d in draws if d <= 0) / iters
    mean = sum(draws) / len(draws)
    var = sum((d - mean) ** 2 for d in draws) / (len(draws) - 1)
    return lo, hi, 2 * min(below, 1 - below), var


def main(argv):
    runs = argv[1:] or DEFAULT_RUNS
    arms = {}
    for r in runs:
        d = load(r)
        if d is None:
            print(f"  ! skipping {r}: no rows.jsonl", file=sys.stderr)
            continue
        arms[r] = d
    if len(arms) < 2:
        print("need at least two runs with rows.jsonl", file=sys.stderr)
        return 1

    print("=" * 78)
    print("PER-SAMPLE PASS RATE (framing A, temp-0.8 samples, 95% Wilson CI)")
    print("=" * 78)
    for r, d in arms.items():
        k = sum(sum(v["o"]) for v in d.values())
        n = sum(len(v["o"]) for v in d.values())
        lo, hi = wilson(k, n)
        at_k = sum(1 for v in d.values() if sum(v["o"]) > 0)
        print(f"{r:<26} {k:>4}/{n:<4} = {k/n:.4f}  CI [{lo:.4f},{hi:.4f}]"
              f"   pass@32 {at_k}/{len(d)}")

    pairs = [p for p in DEFAULT_PAIRS if p[0] in arms and p[1] in arms]
    if not pairs:
        pairs = [(runs[0], r, f"{r} vs {runs[0]}") for r in runs[1:]]

    print()
    print("=" * 78)
    print("TWO-LEVEL PAIRED BOOTSTRAP (resamples specs AND rows within spec)")
    print("=" * 78)
    print(f"{'comparison':<34} {'n':>3} {'delta':>9} {'95% CI':>21} {'p':>7}")
    print("-" * 78)
    results = {}
    for a_name, b_name, label in pairs:
        a, b = arms[a_name], arms[b_name]
        specs = comparable(a, b)
        if len(specs) < 5:
            print(f"{label:<34} {len(specs):>3}  too few comparable prompts")
            continue
        obs = sum(rate(b, s) - rate(a, s) for s in specs) / len(specs)
        lo, hi, p, _ = bootstrap(a, b, specs)
        star = " *" if (lo > 0 or hi < 0) else ""
        print(f"{label:<34} {len(specs):>3} {obs:>+9.4f} "
              f"[{lo:>+7.4f},{hi:>+7.4f}] {p:>7.4f}{star}")
        results[label] = (a, b, specs, obs)

    # Power projection on the last non-control comparison that is not already
    # significant -- that is the one where "should I spend more compute?" bites.
    target = None
    for label, payload in results.items():
        if not label.startswith("CONTROL"):
            lo, hi, p, _ = bootstrap(*payload[:3])
            if lo <= 0:
                target = (label, payload)
    if target is None:
        return 0

    label, (a, b, specs, obs) = target
    _, _, _, v_total = bootstrap(a, b, specs, True, True)
    _, _, _, v_spec = bootstrap(a, b, specs, True, False)
    v_rows = max(v_total - v_spec, 1e-12)

    print()
    print("=" * 78)
    print(f"VARIANCE DECOMPOSITION — {label}")
    print("=" * 78)
    print(f"spec-level heterogeneity  sd = {math.sqrt(v_spec):.4f}  "
          f"{100*v_spec/v_total:5.1f}%  fixed by holdout size, NOT by more runs")
    print(f"within-spec binomial      sd = {math.sqrt(v_rows):.4f}  "
          f"{100*v_rows/v_total:5.1f}%  shrinks as 1/R with R replicate runs")

    print()
    print("Projected 95% CI lower bound (assumes the observed delta is the true one):")
    print(f"{'R runs':>8} {'sd':>9} {'CI lower':>11}   verdict")
    for R in (1, 2, 3, 5, 10, 10 ** 6):
        sd = math.sqrt(v_spec + v_rows / R)
        lo = obs - 1.96 * sd
        print(f"{'inf' if R == 10**6 else R:>8} {sd:>9.4f} {lo:>+11.4f}   "
              f"{'SIGNIFICANT' if lo > 0 else 'still null'}")

    print()
    print(f"{'specs':>8} {'sd':>9} {'CI lower':>11}   verdict  (R=1, wider holdout)")
    n0 = len(specs)
    for n in (30, 45, 60, 90, 120):
        sd = math.sqrt((v_spec + v_rows) * n0 / n)
        lo = obs - 1.96 * sd
        print(f"{n:>8} {sd:>9.4f} {lo:>+11.4f}   "
              f"{'SIGNIFICANT' if lo > 0 else 'still null'}")
    print()
    print("Caveat: the wider-holdout projection assumes new specs are drawn from")
    print("the same difficulty distribution and that the delta holds. Enlarging a")
    print("frozen holdout is a goalpost change and needs an amendment + decontam.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
