"""Unbiased pass@k curves with bootstrap CIs, from rows we already have.

Why this exists: the arms generate 33 samples per spec but report pass@32, which
is very nearly "did ANY of the 33 samples pass". That is the highest-variance,
lowest-resolution statistic available from the data -- one lucky sample flips a
spec -- and it is why the 2026-07-29 session could not distinguish 15/30 from
16/30 (McNemar p=1.000) or 11/30 from 15/30 (p=0.22).

The same rows support the standard unbiased estimator (Chen et al., Codex):

    pass@k for a spec with n samples and c passes  =  1 - C(n-c, k) / C(n, k)

At k << n this is a smooth, low-variance per-spec quantity, so the benchmark mean
resolves differences the k=32 endpoint cannot. No new generation required.

Usage:
    python3 tools/passk_curve.py RUN_ID [RUN_ID ...]
"""
import json
import sys
from collections import defaultdict
from math import comb
from pathlib import Path
from random import Random

REPO = Path(__file__).resolve().parents[1]
KS = (1, 2, 4, 8, 16, 32)


def pass_at_k(n, c, k):
    """Unbiased P(at least one of k random draws from the n samples passes)."""
    if k > n:
        raise ValueError(f"k={k} > n={n}")
    if n - c < k:
        return 1.0
    return 1.0 - comb(n - c, k) / comb(n, k)


def load(run_id):
    p = REPO / "results" / "runs" / run_id / "rows.jsonl"
    by = defaultdict(lambda: [0, 0])  # spec -> [n, c]
    for line in p.open():
        r = json.loads(line)
        by[r["spec"]][0] += 1
        by[r["spec"]][1] += 1 if r["verdict"] == "pass" else 0
    return dict(by)


def curve(by, k):
    return [pass_at_k(n, c, k) for n, c in by.values()]


def boot_ci(vals, iters=10000, seed=0, alpha=0.05):
    """Percentile bootstrap over SPECS (the unit of resampling)."""
    rng = Random(seed)
    m = len(vals)
    means = []
    for _ in range(iters):
        means.append(sum(vals[rng.randrange(m)] for _ in range(m)) / m)
    means.sort()
    lo = means[int(alpha / 2 * iters)]
    hi = means[int((1 - alpha / 2) * iters)]
    return lo, hi


def paired_diff(a, b, k, iters=10000, seed=0):
    """Bootstrap the PAIRED difference (b - a) on specs present in both."""
    common = sorted(set(a) & set(b), key=int)
    da = [pass_at_k(*a[s], k) for s in common]
    db = [pass_at_k(*b[s], k) for s in common]
    diffs = [y - x for x, y in zip(da, db)]
    rng = Random(seed)
    m = len(diffs)
    means = []
    for _ in range(iters):
        means.append(sum(diffs[rng.randrange(m)] for _ in range(m)) / m)
    means.sort()
    obs = sum(diffs) / m
    return obs, means[int(0.025 * iters)], means[int(0.975 * iters)], len(common)


def main():
    runs = sys.argv[1:]
    if not runs:
        sys.exit(__doc__)
    data = {r: load(r) for r in runs}
    for r, by in data.items():
        ns = {n for n, _ in by.values()}
        print(f"{r}: {len(by)} specs, samples/spec={sorted(ns)}")
    print()
    hdr = "  k  " + "".join(f"{r[-14:]:>26}" for r in runs)
    print(hdr)
    print("  " + "-" * (len(hdr) - 2))
    for k in KS:
        cells = []
        for r in runs:
            vals = curve(data[r], k)
            m = sum(vals) / len(vals)
            lo, hi = boot_ci(vals)
            cells.append(f"{m*100:8.1f}%  [{lo*100:4.1f},{hi*100:5.1f}]")
        print(f"  {k:<3}" + "".join(f"{c:>26}" for c in cells))

    if len(runs) >= 2:
        print("\nPaired differences (later run minus first), bootstrap 95% CI over specs:")
        base = runs[0]
        for r in runs[1:]:
            print(f"\n  {r}  vs  {base}")
            for k in KS:
                obs, lo, hi, ncommon = paired_diff(data[base], data[r], k)
                sig = "" if lo <= 0 <= hi else "   <-- CI excludes 0"
                print(f"    k={k:<3} diff={obs*100:+6.2f}pp  95% CI [{lo*100:+6.2f},{hi*100:+6.2f}]"
                      f"  n={ncommon}{sig}")


if __name__ == "__main__":
    main()
