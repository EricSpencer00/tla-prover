"""Figures for docs/FINETUNING_BRIEF.md.

Every number is computed from a ledger or log in-repo; nothing is hand-entered
except the RL-era training metrics, which are read from the TLA-Prove logs that
survive only in git history (cited per figure).

Palette: dataviz reference instance, light mode, validated
(`validate_palette.js "#2a78d6,#eb6834,#1baf7a,#eda100" --mode light` -> ALL PASS,
with a contrast WARN on aqua/yellow that obliges visible direct labels; every
figure below direct-labels its marks).

Usage: python3 tools/brief_figures.py [--out docs/figures]
"""
import argparse
import collections
import json
import sys
from datetime import datetime
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

SURFACE = "#fcfcfb"
INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#8a8880"
GRID = "#e2e1dc"
S1, S2, S3, S4 = "#2a78d6", "#eb6834", "#1baf7a", "#eda100"

plt.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE,
    "savefig.facecolor": SURFACE,
    "font.family": "DejaVu Sans", "font.size": 9,
    "text.color": INK, "axes.labelcolor": INK2, "axes.edgecolor": GRID,
    "xtick.color": INK2, "ytick.color": INK2,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.grid": False, "figure.dpi": 200,
})
REPO = Path(__file__).resolve().parent.parent


def recessive_grid(ax, axis="y"):
    ax.grid(axis=axis, color=GRID, linewidth=0.8, zorder=0)
    ax.set_axisbelow(True)


# --------------------------------------------------------------- ledger stats
def arm_stats(run, full=False):
    """Per-sample pass rate + verdict composition from a Gate-2 ledger.
    Dedups (spec,sample) keep-first, drops corruption rows, excludes api_error
    from the denominator (an api_error is an unmeasured draw, not a failure).
    full=True additionally returns SANY / TLC / vacuity counts."""
    p = REPO / "results/runs" / run / "rows.jsonl"
    seen, rows = set(), []
    for line in p.read_text(errors="replace").splitlines():
        if not line.strip():
            continue
        try:
            d = json.loads(line)
        except json.JSONDecodeError:
            continue
        if d.get("sample") == "corruption":
            continue
        k = (d.get("spec"), d.get("sample"))
        if k in seen:
            continue
        seen.add(k)
        rows.append(d)
    clean = [d for d in rows if d.get("verdict") != "api_error"]
    buckets = collections.Counter()
    for d in clean:
        v = d.get("verdict", "")
        if v == "pass":
            buckets["pass"] += 1
        elif v.startswith("fail:sany"):
            buckets["parse"] += 1
        elif v.startswith("fail:tlc=error") or v.startswith("fail:tlc=timeout"):
            buckets["tlc_error"] += 1
        elif v.startswith("fail:tlc="):
            buckets["semantic"] += 1
        else:
            buckets["other"] += 1
    specs = collections.defaultdict(list)
    for d in clean:
        specs[d.get("spec")].append(d.get("verdict") == "pass")
    out = dict(n=len(clean), npass=buckets["pass"],
               rate=buckets["pass"] / len(clean) if clean else 0.0,
               passk=sum(1 for v in specs.values() if any(v)),
               nspecs=len(specs), buckets=buckets,
               api_error=len(rows) - len(clean))
    if full:
        from harness.repair import LIBRARIES, PROOF_MODULES
        tlc_pop = [d for d in clean
                   if str(d.get("spec")) not in LIBRARIES
                   and str(d.get("spec")) not in PROOF_MODULES]
        checked = [d for d in clean if d.get("tlc_vacuity")]
        out.update(
            sany_ok=sum(1 for d in clean if d.get("sany") == "pass"),
            tlc_pop=len(tlc_pop),
            tlc_ok=sum(1 for d in tlc_pop
                       if d.get("tlc") in ("pass", "pass_expected_violation")),
            vac_checked=len(checked),
            vacuous=sum(1 for d in checked if d.get("tlc_vacuity") != "clean"))
    return out


# ------------------------------------------------------------------ figure 0
def fig_performance(out, arms):
    """Four metrics per arm on the frozen 30-spec holdout. Separate panels
    because pass rates and parameter counts cannot share an axis.

    SANY  = sany == "pass" over all measured draws.
    TLC   = tlc in (pass, pass_expected_violation) over the TLC-criterion
            population only. verdict_of is population-aware: specs 41/86/105/183
            are LIBRARIES (SANY alone is the criterion) and 131/142 are
            PROOF_MODULES (TLAPS), so 6 of 30 specs never run a TLC criterion
            and are excluded from this panel's denominator.
    vacuity = share of TLC-passing draws whose tlc_vacuity is not "clean".
            Rule 5 counts a vacuous pass as a failure; n is small, so counts
            are printed.
    params  = trainable parameters reported at LoRA attach time.
    """
    from harness.repair import LIBRARIES, PROOF_MODULES
    labels, sany, tlc, vac, vacn, params = [], [], [], [], [], []
    for lab, run, ntrain in arms:
        s = arm_stats(run, full=True)
        labels.append(lab)
        n = s["n"]
        sany.append(100 * s["sany_ok"] / n)
        tlc.append(100 * s["tlc_ok"] / s["tlc_pop"])
        vac.append(100 * s["vacuous"] / s["vac_checked"] if s["vac_checked"] else 0)
        vacn.append((s["vacuous"], s["vac_checked"]))
        params.append(ntrain / 1e6)

    fig, axes = plt.subplots(2, 2, figsize=(10.4, 6.6))
    panels = [
        (axes[0][0], sany, "SANY pass rate (%)", "parses and type-checks", S1,
         [f"{v:.1f}%" for v in sany]),
        (axes[0][1], tlc, "TLC pass rate (%)", "24 TLC-criterion specs", S2,
         [f"{v:.1f}%" for v in tlc]),
        (axes[1][0], vac, "vacuous share of TLC passes (%)", "Rule 5: vacuous = fail", S4,
         [f"{a}/{b}" for a, b in vacn]),
        (axes[1][1], params, "trainable params (M)", "at LoRA attach", S3,
         [f"{v:.0f}M" if v else "untuned" for v in params]),
    ]
    for ax, vals, title, sub, col, marks in panels:
        cols = [MUTED if i == 0 else col for i in range(len(vals))]
        bars = ax.bar(labels, vals, color=cols, width=0.62, zorder=3)
        for b, v, m in zip(bars, vals, marks):
            ax.annotate(m, (b.get_x() + b.get_width() / 2, v), ha="center",
                        va="bottom", fontsize=7.8, color=INK)
        ax.set_ylim(0, max(vals) * 1.30 if max(vals) else 1)
        ax.set_title(title, loc="left", fontsize=9.6, color=INK, pad=14)
        ax.annotate(sub, (0, 1.015), xycoords="axes fraction", fontsize=7.4,
                    color=MUTED, va="bottom")
        ax.tick_params(axis="x", labelrotation=22, labelsize=7.6)
        for t in ax.get_xticklabels():
            t.set_ha("right")
        recessive_grid(ax)
    fig.suptitle("Performance by arm, frozen 30-spec holdout (framing A, k=32)",
                 x=0.008, ha="left", fontsize=11.5, color=INK)
    fig.tight_layout(rect=(0, 0, 1, 0.955))
    fig.savefig(out / "fig0_performance.png", bbox_inches="tight")
    plt.close(fig)


# ------------------------------------------------------------------ figure 1
def fig_timeline(out):
    """Every training run, in order, over the six months. Two eras use
    different holdouts and different metrics, so outcomes are printed as text
    rather than plotted on a shared numeric axis."""
    runs = [
        ("2026-03-22", "rl_loop (266 cycles)", "SFT loop", "SANY 80%->65%, TLC 10%->25%"),
        ("2026-04-03", "DPO v13", "DPO", "9/20 SANY, 5/20 TLC (17 pairs)"),
        ("2026-04-10", "piecewise DPO", "DPO", "loss 0.6661 vs ln2, acc 0.60"),
        ("2026-04-11", "full-spec GRPO", "GRPO", "172 steps, holdout 4/30 (1/30 1-shot)"),
        ("2026-04-12", "repair GRPO R1", "GRPO", "965 steps, holdout 9/30 (3/30 1-shot)"),
        ("2026-04-13", "repair GRPO R2", "GRPO", "600 steps, holdout 6/30 (1/30 1-shot)"),
        ("2026-04-14", "repair GRPO R3", "GRPO", "aborted: 152 pairs vs floor 300"),
        ("2026-07-01", "repair GRPO retry", "GRPO", "89 steps zero reward; reverted"),
        ("2026-07-12", "v2_sft1 20b (39 rows)", "SFT", "0/10; 82% unextractable"),
        ("2026-07-13", "v2_sft2 20b (260)", "SFT", "2/30 pass@4 (first passes)"),
        ("2026-07-14", "v2_sft2 120b", "SFT", "A 5.1% per-sample, 11/30"),
        ("2026-07-25", "W2.6 repair-v1 20b (508)", "SFT", "B 9/23 pass@1 vs base 8/23"),
        ("2026-07-29", "W4-diamond-gold 120b", "SFT", "A 11.1% -> 13.6% after prompt fix"),
        ("2026-08-04", "W4DG-genprompt 120b", "SFT", "A 8.1% per-sample, 12/30"),
        ("2026-08-12", "mech composition 120b", "SFT", "6,906 rows; eval pending"),
    ]
    colors = {"SFT": S1, "GRPO": S2, "DPO": S3, "SFT loop": S4}
    fig, ax = plt.subplots(figsize=(11.4, 5.4))
    ys = list(range(len(runs)))[::-1]
    for y, (d, name, meth, outcome) in zip(ys, runs):
        x = datetime.strptime(d, "%Y-%m-%d")
        ax.scatter([x], [y], s=78, color=colors[meth], zorder=3,
                   edgecolor=SURFACE, linewidth=1.5)
        ax.annotate(outcome, (1.02, y), xycoords=("axes fraction", "data"),
                    va="center", ha="left", fontsize=7.8, color=INK2,
                    annotation_clip=False)
    # run names live in the tick column, so they can never collide with the dots
    ax.set_yticks(ys)
    ax.set_yticklabels([r[1] for r in runs], fontsize=8.4, color=INK)
    ax.tick_params(axis="y", length=0, pad=6)
    ax.set_ylim(-0.8, len(runs) - 0.2)
    ax.set_xlim(datetime(2026, 3, 10), datetime(2026, 8, 25))
    ax.spines["left"].set_visible(False)
    recessive_grid(ax, "x")
    handles = [Line2D([], [], marker="o", linestyle="", markersize=7,
                      color=colors[m], label=m) for m in ["SFT", "SFT loop", "DPO", "GRPO"]]
    ax.legend(handles=handles, loc="upper left", frameon=False, ncol=4,
              fontsize=8.5, bbox_to_anchor=(0, -0.09))
    ax.set_title("Every training run, 2026-03 to 2026-08", loc="left",
                 fontsize=11, color=INK, pad=12)
    fig.subplots_adjust(left=0.16, right=0.55, top=0.93, bottom=0.14)
    fig.savefig(out / "fig1_timeline.png", bbox_inches="tight")
    plt.close(fig)


# ------------------------------------------------------------------ figure 2
def fig_rlloop(out):
    """rl_loop SANY and TLC pass rates, computed from all 97 full-suite CSVs
    (n=20 each) in TLA-Prove outputs/benchmark_results."""
    src = Path("/private/tmp/claude-501/-Users-eric-GitHub-prove-TLA/"
               "daacf04d-24ac-4677-a4e0-4c1136967efe/scratchpad/rlloop_series.json")
    if not src.exists():
        print("  fig2 skipped: rlloop_series.json not found")
        return
    rows = [r for r in json.load(open(src)) if r["kind"] == "full"]
    rows.sort(key=lambda r: r["ts"])
    # The loop did not run continuously; joining across an idle stretch would
    # draw a trend that was never measured. Break the line on gaps > 24h.
    xs, series = [], {"sany": [], "tlc": []}
    prev = None
    for r in rows:
        t = datetime.fromtimestamp(r["ts"])
        if prev is not None and (r["ts"] - prev) > 86400:
            xs.append(t)
            for k in series:
                series[k].append(float("nan"))
        xs.append(t)
        for k in series:
            series[k].append(r[k] * 100)
        prev = r["ts"]
    fig, ax = plt.subplots(figsize=(9.2, 3.9))
    for key, col, lab in (("sany", S1, "SANY pass"), ("tlc", S2, "TLC pass")):
        ax.plot(xs, series[key], color=col, linewidth=1.6, marker="o",
                markersize=3.2, markeredgecolor=SURFACE, markeredgewidth=0.4,
                label=lab, zorder=3)
        last = [v for v in series[key] if v == v][-1]
        ax.annotate(f" {lab}", (xs[-1], last), fontsize=8.5,
                    color=INK2, va="center", ha="left", annotation_clip=False)
    ax.set_ylim(0, 100)
    ax.set_ylabel("pass rate, 20-problem suite (%)")
    ax.xaxis.set_major_locator(matplotlib.dates.DayLocator(interval=3))
    ax.xaxis.set_major_formatter(matplotlib.dates.DateFormatter("%b %d"))
    recessive_grid(ax)
    ax.legend(frameon=False, fontsize=8.5, loc="upper left", ncol=2)
    ax.set_title("rl_loop: 97 full-suite evaluations (n=20 each), "
                 "2026-03-22 to 2026-04-06", loc="left", fontsize=11,
                 color=INK, pad=10)
    ax.annotate("gaps = loop idle\n(line broken)", (0.34, 0.46),
                xycoords="axes fraction", fontsize=7.5, color=MUTED, ha="center")
    fig.subplots_adjust(right=0.86)
    fig.savefig(out / "fig2_rlloop.png", bbox_inches="tight")
    plt.close(fig)


# ------------------------------------------------------------ figures 3 and 5
def fig_arm_rates(out, runs, fname, title, ylab):
    labels, rates, notes = [], [], []
    for lab, run in runs:
        s = arm_stats(run)
        labels.append(lab)
        rates.append(s["rate"] * 100)
        notes.append(f"{s['npass']}/{s['n']}")
    base = rates[0]
    fig, ax = plt.subplots(figsize=(8.6, 3.7))
    cols = [MUTED] + [S1] * (len(rates) - 1)
    bars = ax.bar(labels, rates, color=cols, width=0.6, zorder=3)
    # Reference line only: the gray bar at position 0 is the base and is
    # labelled on the x axis, so a text callout on the line is redundant.
    ax.axhline(base, color=MUTED, linewidth=1.4, linestyle=(0, (4, 3)), zorder=2)
    for b, r, n in zip(bars, rates, notes):
        ax.annotate(f"{r:.1f}%\n{n}", (b.get_x() + b.get_width() / 2, r),
                    ha="center", va="bottom", fontsize=8.2, color=INK)
    ax.set_ylim(0, max(rates) * 1.32)
    ax.set_ylabel(ylab)
    recessive_grid(ax)
    ax.set_title(title, loc="left", fontsize=11, color=INK, pad=10)
    fig.savefig(out / fname, bbox_inches="tight")
    plt.close(fig)


# ------------------------------------------------------------------ figure 4
def fig_verdicts(out, runs):
    """Verdict composition per arm. Direct-labelled because two palette slots
    sit below 3:1 on this surface (relief rule)."""
    order = [("parse", "parse fail (SANY)", S2), ("tlc_error", "TLC error", S4),
             ("semantic", "semantic fail", S3), ("pass", "pass", S1)]
    labels, data = [], {k: [] for k, _, _ in order}
    for lab, run in runs:
        s = arm_stats(run)
        labels.append(lab)
        for k, _, _ in order:
            data[k].append(100 * s["buckets"][k] / s["n"])
    fig, ax = plt.subplots(figsize=(9.2, 3.4))
    left = [0.0] * len(labels)
    for k, name, col in order:
        vals = data[k]
        ax.barh(labels, vals, left=left, color=col, height=0.62, zorder=3,
                edgecolor=SURFACE, linewidth=2, label=name)
        for i, (v, l0) in enumerate(zip(vals, left)):
            if v >= 6:
                ax.annotate(f"{v:.0f}%", (l0 + v / 2, i), ha="center",
                            va="center", fontsize=8, color="#ffffff" if k != "tlc_error" else INK)
        left = [a + b for a, b in zip(left, vals)]
    ax.set_xlim(0, 100)
    ax.set_xlabel("share of measured draws (%)")
    ax.invert_yaxis()
    recessive_grid(ax, "x")
    ax.legend(frameon=False, fontsize=8.3, ncol=4, loc="lower left",
              bbox_to_anchor=(0, -0.42))
    ax.set_title("Where framing-A draws fail, by arm", loc="left",
                 fontsize=11, color=INK, pad=10)
    fig.savefig(out / "fig4_verdicts.png", bbox_inches="tight")
    plt.close(fig)


# ------------------------------------------------------------------ figure 6
def fig_grpo(out):
    """Share of logged GRPO steps whose sampled group had zero reward variance
    (frac_reward_zero_std == 1). Source: TLA-Prove training logs at git
    e79a250 / 511a492; full-spec is derived as 1 - 37/172 nonzero-reward steps."""
    runs = ["full-spec\n(172 steps)", "repair R1\n(965 steps)", "repair R2\n(600 steps)"]
    vals = [100 * (1 - 37 / 172), 100 * 703 / 965, 100 * 430 / 600]
    fig, ax = plt.subplots(figsize=(6.4, 3.4))
    bars = ax.bar(runs, vals, color=S2, width=0.55, zorder=3)
    for b, v in zip(bars, vals):
        ax.annotate(f"{v:.0f}%", (b.get_x() + b.get_width() / 2, v), ha="center",
                    va="bottom", fontsize=9, color=INK)
    ax.set_ylim(0, 100)
    ax.set_ylabel("steps with zero reward variance (%)")
    recessive_grid(ax)
    ax.set_title("GRPO: share of steps producing no gradient", loc="left",
                 fontsize=11, color=INK, pad=10)
    fig.savefig(out / "fig6_grpo.png", bbox_inches="tight")
    plt.close(fig)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="docs/figures")
    args = ap.parse_args()
    out = REPO / args.out
    out.mkdir(parents=True, exist_ok=True)

    arms_a = [("untuned base", "e2c-baseline-120b-a"), ("v2 SFT", "gate2-v2-120b-A"),
              ("W4DG", "gate2-w4dg-120b-A"), ("W4DG post-fix", "gate2-w4dg-120b-A3"),
              ("W4DG-genprompt", "gate2-w4dgp-120b-A")]
    arms_b = [("untuned base", "e2c-baseline-120b-b"), ("v2 SFT", "gate2-v2-120b-B"),
              ("W4DG-genprompt", "gate2-w4dgp-120b-B")]

    # trainable params at attach time, from each run's training log on Sophia
    perf_arms = [("untuned base", "e2c-baseline-120b-a", 0),
                 ("v2 SFT", "gate2-v2-120b-A", 536_813_568),
                 ("W4DG", "gate2-w4dg-120b-A", 536_813_568),
                 ("W4DG post-fix", "gate2-w4dg-120b-A3", 536_813_568),
                 ("W4DG-genprompt", "gate2-w4dgp-120b-A", 536_813_568)]
    fig_performance(out, perf_arms)
    fig_timeline(out)
    fig_rlloop(out)
    fig_arm_rates(out, arms_a, "fig3_framingA.png",
                  "Framing A (generate from description): per-sample pass rate",
                  "per-sample pass rate (%)")
    fig_verdicts(out, arms_a)
    fig_arm_rates(out, arms_b, "fig5_framingB.png",
                  "Framing B (repair a corrupted spec): per-sample pass rate",
                  "per-sample pass rate (%)")
    fig_grpo(out)

    print("wrote:", *(p.name for p in sorted(out.glob("*.png"))))
    for lab, run in arms_a + arms_b:
        s = arm_stats(run)
        print(f"  {run:24} n={s['n']:4} pass={s['npass']:4} "
              f"rate={s['rate']:.4f} pass@k={s['passk']}/{s['nspecs']} "
              f"api_err={s['api_error']}")


if __name__ == "__main__":
    main()
