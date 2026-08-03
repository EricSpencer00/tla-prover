#!/usr/bin/env python3
"""Re-score the W4 difficulty probe from its append-only ledger.

    python3 tools/w4_difficulty_report.py --rundir results/runs/w4-difficulty-v1

Reads rows.jsonl and NOTHING else. summary.json is advisory in this project by
policy and is never the source of a reported number.

WHAT k CAN AND CANNOT CERTIFY
-----------------------------
The design doc originally said a cell counts as "saturated" when its k=32
Clopper-Pearson lower bound clears 0.97. That criterion is unsatisfiable, and
the arithmetic says why: for a cell that passes every draw, the exact CP lower
bound is (alpha/2)^(1/k). At k=32 and alpha=0.05 that is 0.891 -- so a perfect
32/32 does NOT certify p > 0.97. Reaching 0.97 needs

    k >= ln(0.025) / ln(0.97) ~= 122

consecutive passes per cell, which at 300 cells is 36,600 samples: not a
triage sweep, a second project.

So the criterion here is the honest operational one:

    SATURATED := the cell passed on every one of its k draws,

reported WITH its exact CP interval so the reader can see what that does and
does not pin down. The headline number is not any single cell's p -- it is the
FRACTION of corpus rows that are all-pass, and that proportion over ~300 cells
has a tight interval of its own. That is the quantity the decision rule needs.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from collections import defaultdict
from pathlib import Path

ALPHA = 0.05


# ------------------------------------------------------- exact interval math
# Stdlib only. The harness has no numpy/scipy dependency and gains none here:
# "keeping the runtime dependency-free is what lets a reviewer reproduce a
# number without resolving an environment" (requirements-dev.txt).

def _betacf(a: float, b: float, x: float) -> float:
    """Continued fraction for the incomplete beta (modified Lentz)."""
    TINY, EPS, ITMAX = 1e-30, 3e-16, 400
    qab, qap, qam = a + b, a + 1.0, a - 1.0
    c = 1.0
    d = 1.0 - qab * x / qap
    if abs(d) < TINY:
        d = TINY
    d = 1.0 / d
    h = d
    for m in range(1, ITMAX + 1):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        if abs(d) < TINY:
            d = TINY
        c = 1.0 + aa / c
        if abs(c) < TINY:
            c = TINY
        d = 1.0 / d
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        if abs(d) < TINY:
            d = TINY
        c = 1.0 + aa / c
        if abs(c) < TINY:
            c = TINY
        d = 1.0 / d
        delta = d * c
        h *= delta
        if abs(delta - 1.0) < EPS:
            break
    return h


def betainc(a: float, b: float, x: float) -> float:
    """Regularized incomplete beta I_x(a, b)."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    lbeta = (math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
             + a * math.log(x) + b * math.log1p(-x))
    front = math.exp(lbeta)
    if x < (a + 1.0) / (a + b + 2.0):
        return front * _betacf(a, b, x) / a
    return 1.0 - math.exp(
        math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
        + b * math.log1p(-x) + a * math.log(x)
    ) * _betacf(b, a, 1.0 - x) / b


def _beta_ppf(q: float, a: float, b: float) -> float:
    """Inverse of I_x(a, b) by bisection. 200 halvings is ~1e-60 -- far past
    the precision anyone reads off this table, and immune to the convergence
    failures a Newton step has near the 0/1 boundaries."""
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2.0
        if betainc(a, b, mid) < q:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def clopper_pearson(k: int, n: int, alpha: float = ALPHA) -> tuple:
    """Exact two-sided binomial interval. k successes of n."""
    if n == 0:
        return (0.0, 1.0)
    lo = 0.0 if k == 0 else _beta_ppf(alpha / 2.0, k, n - k + 1)
    hi = 1.0 if k == n else _beta_ppf(1.0 - alpha / 2.0, k + 1, n - k)
    return (lo, hi)


def saturation_certifiable_k(threshold: float = 0.97, alpha: float = ALPHA) -> int:
    """Draws needed for an all-pass cell's CP lower bound to clear `threshold`."""
    return math.ceil(math.log(alpha / 2.0) / math.log(threshold))


def fisher_exact_two_sided(a: int, b: int, c: int, d: int) -> float:
    """Two-sided Fisher exact p for [[a, b], [c, d]]. Exact via math.comb --
    no normal approximation, which matters because several strata here are
    small enough that chi-square would be untrustworthy."""
    n = a + b + c + d
    r1, r2, c1 = a + b, c + d, a + c

    def prob(x):
        return (math.comb(r1, x) * math.comb(r2, c1 - x)) / math.comb(n, c1)

    lo = max(0, c1 - r2)
    hi = min(r1, c1)
    obs = prob(a)
    return min(1.0, sum(prob(x) for x in range(lo, hi + 1)
                        if prob(x) <= obs * (1 + 1e-9)))


# ---------------------------------------------------------------- re-scoring

def load_rows(rows_path: Path) -> list[dict]:
    rows = []
    for line in rows_path.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return rows


def cells_from_rows(rows: list[dict]) -> dict:
    """{(mode, seed_key): {n, passes, arm, tier_name, api_errors}}.

    api_error rows are excluded from BOTH numerator and denominator -- they
    carry no measurement. Counting them as failures would turn endpoint uptime
    into a difficulty signal.
    """
    cells: dict = defaultdict(lambda: {"n": 0, "passes": 0, "api_errors": 0,
                                       "arm": None, "tier_name": None})
    for r in rows:
        c = cells[(r.get("mode"), r.get("seed_key"))]
        c["arm"] = r.get("arm")
        c["tier_name"] = r.get("tier_name")
        if r.get("api_error"):
            c["api_errors"] += 1
            continue
        c["n"] += 1
        c["passes"] += 1 if r.get("survived") else 0
    return dict(cells)


def bin_of(c: dict) -> str:
    if c["n"] == 0:
        return "unmeasured"
    if c["passes"] == 0:
        return "p=0 (never solved)"
    if c["passes"] == c["n"]:
        return "all-pass (saturated)"
    return "0<p<1 (partial)"


BIN_ORDER = ("p=0 (never solved)", "0<p<1 (partial)", "all-pass (saturated)",
             "unmeasured")


def _pct(k, n):
    return f"{100.0 * k / n:5.1f}%" if n else "    --"


def summarize(cells: dict, alpha: float = ALPHA) -> dict:
    by_mode: dict = defaultdict(list)
    for (mode, _key), c in cells.items():
        by_mode[mode].append(c)
    return {m: v for m, v in by_mode.items()}


def report(rundir: Path, alpha: float = ALPHA) -> int:
    rows_path = rundir / "rows.jsonl"
    if not rows_path.exists():
        print(f"FAIL: no ledger at {rows_path}")
        return 1
    rows = load_rows(rows_path)
    if not rows:
        print(f"FAIL: ledger {rows_path} is empty")
        return 1
    cells = cells_from_rows(rows)
    by_mode = summarize(cells, alpha)

    n_api = sum(c["api_errors"] for c in cells.values())
    print(f"ledger: {rows_path}  ({len(rows)} rows, {len(cells)} cell-modes)")
    if n_api:
        print(f"\n!! {n_api} api_error row(s) present. They are excluded from "
              f"every number below. Re-run to resume and re-draw them before "
              f"reporting anything.")

    need = saturation_certifiable_k(0.97, alpha)
    print(f"\nSATURATED := passed on every draw. Note the exact arithmetic: an "
          f"all-pass cell's\nCP lower bound is (alpha/2)^(1/k), so certifying "
          f"p>0.97 would need k>={need}.\nAt k=8 an all-pass cell certifies "
          f"only p>{(alpha/2)**(1/8):.3f}; at k=32, p>{(alpha/2)**(1/32):.3f}.")

    for mode in sorted(by_mode):
        cs = by_mode[mode]
        print(f"\n{'='*66}\nMODE: {mode}   ({len(cs)} cells)\n{'='*66}")

        bins = defaultdict(int)
        for c in cs:
            bins[bin_of(c)] += 1
        n = len(cs)
        print(f"\n{'bin':24s} {'cells':>6s} {'share':>7s}  95% CI on the share")
        for b in BIN_ORDER:
            if not bins[b]:
                continue
            lo, hi = clopper_pearson(bins[b], n, alpha)
            print(f"{b:24s} {bins[b]:6d} {_pct(bins[b], n)}  "
                  f"[{lo:.3f}, {hi:.3f}]")

        # The headline: saturated share of the arm that was actually trained.
        trained = [c for c in cs if c["tier_name"] in ("diamond", "gold")]
        if trained:
            sat = sum(1 for c in trained if bin_of(c) == "all-pass (saturated)")
            lo, hi = clopper_pearson(sat, len(trained), alpha)
            print(f"\nHEADLINE -- saturated share of diamond+gold (the trained arm):")
            print(f"  {sat}/{len(trained)} = {_pct(sat, len(trained))}  "
                  f"95% CI [{lo:.3f}, {hi:.3f}]")
            print(f"  decision rule: >0.30 re-export and retrain | "
                  f"0.10-0.30 filter the next wave | <0.10 drop this axis")

        print(f"\n{'stratum':22s} {'cells':>6s} {'p=0':>6s} {'part':>6s} "
              f"{'sat':>6s}  mean p")
        strata = defaultdict(list)
        for c in cs:
            strata[f"{c['arm']}/{c['tier_name']}"].append(c)
        for s in sorted(strata):
            g = strata[s]
            z = sum(1 for c in g if bin_of(c) == "p=0 (never solved)")
            pa = sum(1 for c in g if bin_of(c) == "0<p<1 (partial)")
            sa = sum(1 for c in g if bin_of(c) == "all-pass (saturated)")
            meas = [c for c in g if c["n"]]
            mp = (sum(c["passes"] / c["n"] for c in meas) / len(meas)) if meas else 0.0
            print(f"{s:22s} {len(g):6d} {z:6d} {pa:6d} {sa:6d}  {mp:.3f}")

        # Secondary: do the mutation-kill tiers carry difficulty information?
        dia = [c for c in cs if c["tier_name"] == "diamond" and c["n"]]
        gol = [c for c in cs if c["tier_name"] == "gold" and c["n"]]
        if dia and gol:
            ds = sum(1 for c in dia if bin_of(c) == "all-pass (saturated)")
            gs = sum(1 for c in gol if bin_of(c) == "all-pass (saturated)")
            p = fisher_exact_two_sided(ds, len(dia) - ds, gs, len(gol) - gs)
            dlo, dhi = clopper_pearson(ds, len(dia), alpha)
            glo, ghi = clopper_pearson(gs, len(gol), alpha)
            print(f"\nDIAMOND vs GOLD (do the mutation-kill tiers carry "
                  f"difficulty information?)")
            print(f"  diamond saturated {ds}/{len(dia)} = {_pct(ds, len(dia))} "
                  f"[{dlo:.3f}, {dhi:.3f}]")
            print(f"  gold    saturated {gs}/{len(gol)} = {_pct(gs, len(gol))} "
                  f"[{glo:.3f}, {ghi:.3f}]")
            print(f"  Fisher exact two-sided p = {p:.4f}"
                  + ("  -- indistinguishable; the tiers grade invariant "
                     "strength, not difficulty" if p > 0.05 else
                     "  -- the tiers do carry difficulty signal"))

    # Cross-mode: how much does the train/serve prompt mismatch cost?
    if len(by_mode) > 1 and "generation" in by_mode and "sft_user" in by_mode:
        common = {k for (m, k) in cells if m == "generation"} & \
                 {k for (m, k) in cells if m == "sft_user"}
        if common:
            g = [cells[("generation", k)] for k in sorted(common)]
            s = [cells[("sft_user", k)] for k in sorted(common)]
            gp = sum(c["passes"] for c in g)
            gn = sum(c["n"] for c in g)
            sp = sum(c["passes"] for c in s)
            sn = sum(c["n"] for c in s)
            glo, ghi = clopper_pearson(gp, gn, alpha)
            slo, shi = clopper_pearson(sp, sn, alpha)
            pv = fisher_exact_two_sided(gp, gn - gp, sp, sn - sp)
            print(f"\n{'='*66}\nPROMPT MISMATCH ({len(common)} cells in both modes, "
                  f"per-sample yield)\n{'='*66}")
            print(f"  generation (the contract the corpus was verified under): "
                  f"{gp}/{gn} = {_pct(gp, gn)} [{glo:.3f}, {ghi:.3f}]")
            print(f"  sft_user   (what the training pair actually shows):      "
                  f"{sp}/{sn} = {_pct(sp, sn)} [{slo:.3f}, {shi:.3f}]")
            print(f"  Fisher exact two-sided p = {pv:.4f}")
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="tools/w4_difficulty_report.py")
    ap.add_argument("--rundir", default="results/runs/w4-difficulty-v1")
    ap.add_argument("--alpha", type=float, default=ALPHA)
    a = ap.parse_args(argv)
    return report(Path(a.rundir), a.alpha)


if __name__ == "__main__":
    sys.exit(main())
