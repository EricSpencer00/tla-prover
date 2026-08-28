"""Render every figure in the addendum from docs/addendum/data.json.

One entry point per figure, all writing PDF into figures/. No number is typed
here: everything is read from the JSON the collector emits.
"""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Patch

HERE = Path(__file__).resolve().parent
FIG = HERE / "figures"
FIG.mkdir(exist_ok=True)
D = json.loads((HERE / "data.json").read_text())

plt.rcParams.update({
    "font.family": "serif",
    "font.serif": ["Times New Roman", "DejaVu Serif"],
    "font.size": 8,
    "axes.linewidth": 0.6,
    "axes.edgecolor": "#444444",
    "xtick.major.width": 0.6,
    "ytick.major.width": 0.6,
    "figure.dpi": 200,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.02,
})
LOOP_C, OPEN_C, MUTE = "#1b3a6b", "#b8b8b8", "#8a8a8a"


def fig_seeds():
    """Solved specs per seed, with the call budget each arm spent."""
    fig, (ax, ax2) = plt.subplots(1, 2, figsize=(6.6, 2.3),
                                  gridspec_kw={"width_ratios": [2.1, 1]})
    ls, os_ = D["loop_solved"], D["open_solved"]
    xs = range(len(ls))
    ax.bar([x - 0.19 for x in xs], ls, 0.36, color=LOOP_C, label="framing L (closed loop)")
    ax.bar([x + 0.19 for x in xs], os_, 0.36, color=OPEN_C, edgecolor="#777", linewidth=0.5,
           label="framing A (open loop)")
    for x, v in zip(xs, ls):
        ax.text(x - 0.19, v + 0.35, str(v), ha="center", fontsize=7.5, color=LOOP_C)
    for x, v in zip(xs, os_):
        ax.text(x + 0.19, v + 0.35, str(v), ha="center", fontsize=7.5, color="#555")
    ax.axhspan(min(ls), max(ls), color=LOOP_C, alpha=0.07, zorder=0)
    ax.axhspan(min(os_), max(os_), color="#000000", alpha=0.05, zorder=0)
    ax.set_xticks(list(xs)); ax.set_xticklabels([f"seed {i+1}" for i in xs])
    ax.set_ylabel("specs solved (of 30)"); ax.set_ylim(0, 24)
    ax.legend(frameon=False, fontsize=7, loc="upper center", ncol=2,
              bbox_to_anchor=(0.5, 1.22))
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)

    ax2.bar([0, 1], [sum(D["loop_calls"]) / 3, sum(D["open_calls"]) / 3],
            0.55, color=[LOOP_C, OPEN_C], edgecolor="#777", linewidth=0.5)
    for x, v in zip([0, 1], [sum(D["loop_calls"]) / 3, sum(D["open_calls"]) / 3]):
        ax2.text(x, v + 18, f"{v:.0f}", ha="center", fontsize=7.5)
    ax2.set_xticks([0, 1]); ax2.set_xticklabels(["L", "A"])
    ax2.set_ylabel("mean model calls / arm"); ax2.set_ylim(0, 1150)
    for s in ("top", "right"):
        ax2.spines[s].set_visible(False)
    fig.savefig(FIG / "fig_seeds.pdf"); plt.close(fig)


def fig_funnel():
    """Where the draws go, and what a spec can reach given the pooled budget."""
    t = D["reach_totals"]
    fig, (a, b) = plt.subplots(1, 2, figsize=(6.6, 2.1))
    stages = ["draws", "SANY\nparse", "+ .cfg\nsignature", "TLC\npass"]
    vals = [t["draws"], t["parse"], t["signature_complete"], t["tlc"]]
    a.bar(stages, vals, color=[MUTE, LOOP_C, LOOP_C, LOOP_C], width=0.6)
    for i, v in enumerate(vals):
        a.text(i, v + t["draws"] * 0.02, f"{v}\n{v/t['draws']:.0%}", ha="center", fontsize=7)
    a.set_ylabel("candidates"); a.set_ylim(0, t["draws"] * 1.22)
    a.set_title("per draw", fontsize=8, pad=3)

    sv = [t["n_specs"], t["specs_any_parse"], t["specs_any_sig"], t["specs_any_tlc"]]
    b.bar(stages, sv, color=[MUTE, LOOP_C, LOOP_C, LOOP_C], width=0.6)
    for i, v in enumerate(sv):
        b.text(i, v + 0.5, f"{v}/30", ha="center", fontsize=7)
    b.set_ylabel("specs with at least one"); b.set_ylim(0, 36)
    b.set_title("per spec, pooled over all arms", fontsize=8, pad=3)
    for ax in (a, b):
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
    fig.savefig(FIG / "fig_funnel.pdf"); plt.close(fig)


def fig_taxonomy():
    """What SANY actually rejects, and what the unknown-operator mass is made of."""
    tax, unk = D["sany_taxonomy"], D["unknown_operator_taxonomy"]
    tot = D["sany_failures_total"]
    labels = {"parse": "grammar (module does not parse)",
              "unknown_operator": "unknown operator",
              "other": "other", "duplicate_definition": "duplicate definition",
              "arity": "wrong arity", "level": "level error",
              "substitution": "missing substitution"}
    ul = {"invented_operator": "invented operator",
          "qualified_against_unqualified_instance": "$M!op$, unqualified INSTANCE",
          "bound_var_escaped_scope": "bound var out of scope",
          "defined_earlier_recursive_or_scope": "RECURSIVE / scope",
          "forward_reference": "forward reference"}
    fig, (a, b) = plt.subplots(1, 2, figsize=(7.0, 2.2))
    fig.subplots_adjust(wspace=0.75)
    items = sorted(tax.items(), key=lambda kv: -kv[1])
    a.barh([labels.get(k, k) for k, _ in items][::-1], [v for _, v in items][::-1],
           color=LOOP_C, height=0.6)
    for i, (_, v) in enumerate(items[::-1]):
        a.text(v + tot * 0.012, i, f"{v}  ({v/tot:.0%})", va="center", fontsize=7)
    a.set_xlim(0, max(tax.values()) * 1.30)
    a.set_xlabel(f"SANY failures (n={tot})")

    ui = sorted(unk.items(), key=lambda kv: -kv[1])
    ut = sum(unk.values())
    b.barh([ul.get(k, k) for k, _ in ui][::-1], [v for _, v in ui][::-1],
           color="#4a6fa5", height=0.6)
    for i, (_, v) in enumerate(ui[::-1]):
        b.text(v + ut * 0.012, i, f"{v}  ({v/ut:.0%})", va="center", fontsize=7)
    b.set_xlim(0, max(unk.values()) * 1.38)
    b.set_xlabel(f"unknown-operator errors (n={ut})")
    for ax in (a, b):
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
        ax.tick_params(axis="y", length=0)
    fig.savefig(FIG / "fig_taxonomy.pdf"); plt.close(fig)


def fig_perspec():
    """Per-spec solve rate over seeds: which gains are stable and which are not."""
    rows = [r for r in D["per_spec"] if r["loop"] or r["open"]]
    rows.sort(key=lambda r: (r["loop"] / 3 - r["open"] / 3, r["loop"]), reverse=True)
    fig, ax = plt.subplots(figsize=(6.6, 2.6))
    xs = range(len(rows))
    ax.bar([x - 0.19 for x in xs], [r["loop"] for r in rows], 0.36, color=LOOP_C)
    ax.bar([x + 0.19 for x in xs], [r["open"] for r in rows], 0.36, color=OPEN_C,
           edgecolor="#777", linewidth=0.5)
    ax.set_xticks(list(xs)); ax.set_xticklabels([r["spec"] for r in rows], fontsize=6.5)
    ax.set_ylabel("seeds solving (of 3)"); ax.set_yticks([0, 1, 2, 3])
    ax.set_ylim(0, 3.35)
    ax.set_xlabel("holdout spec")
    ax.legend(handles=[Patch(facecolor=LOOP_C, label="framing L"),
                       Patch(facecolor=OPEN_C, edgecolor="#777", label="framing A")],
              frameon=False, fontsize=7, ncol=2, loc="lower center",
              bbox_to_anchor=(0.5, 1.01))
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    fig.savefig(FIG / "fig_perspec.pdf"); plt.close(fig)


def fig_grammar():
    """The decode-time gate: false rejects against catch rate, v0 against v1."""
    g = D.get("grammar", {})
    fig, ax = plt.subplots(figsize=(3.3, 2.2))
    names = ["v0 (structural)", "v1 (expression)"]
    fr = [g.get("v0_false_reject", 0.050), g.get("v1_false_reject", 0.0)]
    tr = [g.get("v0_catch", 0.032), g.get("v1_catch", 0.867)]
    xs = [0, 1]
    ax.bar([x - 0.18 for x in xs], [v * 100 for v in fr], 0.34,
           color="#a33", label="false reject (valid specs)")
    ax.bar([x + 0.18 for x in xs], [v * 100 for v in tr], 0.34,
           color=LOOP_C, label="caught (real parse failures)")
    for x, v in zip(xs, fr):
        ax.text(x - 0.18, v * 100 + 2.5, f"{v:.1%}", ha="center", fontsize=7)
    for x, v in zip(xs, tr):
        ax.text(x + 0.18, v * 100 + 2.5, f"{v:.1%}", ha="center", fontsize=7)
    ax.set_xticks(xs); ax.set_xticklabels(names, fontsize=7.5)
    ax.set_ylabel("percent"); ax.set_ylim(0, 105)
    ax.legend(frameon=False, fontsize=6.8, loc="upper left")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    fig.savefig(FIG / "fig_grammar.pdf"); plt.close(fig)


def _png_copies():
    """PNG twins of every figure, for eyeballing that they render. LaTeX uses the
    PDFs; these exist so a broken figure is caught before the build, not after."""
    import subprocess
    for pdf in sorted(FIG.glob("*.pdf")):
        subprocess.run(["sips", "-s", "format", "png", "-Z", "1400", str(pdf),
                        "--out", str(pdf.with_suffix(".png"))],
                       capture_output=True)


if __name__ == "__main__":
    for f in (fig_seeds, fig_funnel, fig_taxonomy, fig_perspec, fig_grammar):
        f()
        print("wrote", f.__name__)
    _png_copies()
