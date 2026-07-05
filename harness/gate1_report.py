"""Assemble the Gate-1 evidence: per-method 206-row matrix, pass@1 vs pass@N
(Rule 3), semantic-audit rejections (Rule 5), residue by failure class, and the
G1 status line (oracle union model = system closure; model-only = X/206).

An "arm" is one model's sweep. An arm may be split across multiple run dirs (a
crashed run + its --resume-from continuation); they are unioned per spec. A spec
counts as a model PASS only if some model method passed AND that pass is not on
the arm's semaudit reject list (SEMAUDIT_FINDINGS.md / manual verdicts) -- a pass
won by weakening the spec is not a pass.

Usage: python3 -m harness gate1-report --arms <name=run1+run2,...> [--out FILE]
Each arm: label=rundir[+rundir2...]; reject list read from REJECTS below (the
manually-adjudicated false passes) keyed by arm label.
"""
import json
from collections import defaultdict
from pathlib import Path

from .runner import REPO

# manually-adjudicated false passes per arm (SEMAUDIT_FINDINGS.md). A model pass
# on these is a gamed/weakened pass -> excluded from the model-only count.
REJECTS = {
    "gpt-oss-120b": {"57", "91", "92", "178"},
}


def load_arm(rundirs):
    rows = []
    for rd in rundirs:
        p = REPO / "results" / "runs" / rd / "rows.jsonl"
        if p.exists():
            rows += [json.loads(l) for l in p.read_text().splitlines() if l]
    by = defaultdict(list)
    for r in rows:
        by[r["spec"]].append(r)
    return by


def classify(last_verdict):
    v = last_verdict
    if "no_source" in v:
        return "orphan"
    if "sany" in v:
        return "parse"
    if "timeout" in v:
        return "state-explosion"
    if "api_error" in v:
        return "endpoint-blocked"
    if "vacuous" in v:
        return "vacuous"
    return "tlc-reject"


def arm_summary(label, by, all_nums):
    rejects = REJECTS.get(label, set())
    baseline_pass, model_pass, p1, residue = [], [], [], defaultdict(list)
    for num in all_nums:
        rs = by.get(num, [])
        if not rs:
            residue["not-attempted"].append(num)
            continue
        base_ok = any(r["method"] == "repair-baseline" and r["verdict"] == "pass"
                      for r in rs)
        model_ok = any(r["verdict"] == "pass" and r["method"] != "repair-baseline"
                       for r in rs)
        if num in rejects:  # audit-rejected: pass does not count
            model_ok = base_ok = False
        p1_ok = any(r["verdict"] == "pass" and
                    r["method"] in ("repair-baseline", "repair-r1") for r in rs) \
            and num not in rejects
        if base_ok:
            baseline_pass.append(num)
        elif model_ok:
            model_pass.append(num)
        else:
            residue[classify(rs[-1]["verdict"]) if num not in rejects
                    else "false-pass-rejected"].append(num)
        if p1_ok:
            p1.append(num)
    passN = baseline_pass + model_pass
    return {"label": label, "baseline_pass": baseline_pass,
            "model_repaired": model_pass, "pass_at_1": p1, "pass_at_N": passN,
            "residue": {k: sorted(v, key=int) for k, v in residue.items()}}


def render(arms, all_nums, oracle_repro, signoff, gap):
    """oracle_repro = reproducible Gate-0 closed set (167). signoff = documented
    Gate-0 figure (171). gap = unreconciled (4)."""
    n = len(all_nums)
    oracle_set = set(oracle_repro)
    lines = ["# GATE 1 STATUS -- Stage 1 repair sweep\n",
             "Evidence for Eric's sign-off (mirrors GATE0_STATUS.md style). Numbers "
             "trace to `results/runs/` ledger rows; model-only counts exclude "
             "semantic-audit rejects (Rule 5, SEMAUDIT_FINDINGS.md). Oracle set from "
             "`corpus/gate0_closed.json` (frozen at Gate-0 Amendment-4), not inferred "
             "from model/baseline (PLAN 4).\n",
             f"Denominator: {n}/206 (Amendment 2 reporting rule).",
             f"Oracle (retrieval, no model): **{signoff}/206** at Gate-0 sign-off; "
             f"**{len(oracle_repro)}/206 reproducible now** (local re-run + HPC "
             f"supplement); **{gap}-spec unreconciled gap** -- see gate0_closed.json.\n",
             "## Per-method matrix\n",
             "| method | baseline pass | model-repaired | pass@1 | pass@N (model-only) | residue |",
             "|---|---|---|---|---|---|"]
    model_new_all = set()
    for a in arms:
        res_n = sum(len(v) for v in a["residue"].values())
        lines.append(f"| {a['label']} | {len(a['baseline_pass'])} | "
                     f"{len(a['model_repaired'])} | {len(a['pass_at_1'])} | "
                     f"**{len(a['pass_at_N'])}** | {res_n} |")
    lines.append("")
    for a in arms:
        # model-new = specs THIS arm closed that the oracle did NOT (these move the
        # union); the rest are re-closures of already-oracle-closed specs
        mnew = sorted(set(a["model_repaired"]) - oracle_set, key=int)
        model_new_all |= set(mnew)
        recl = sorted(set(a["model_repaired"]) & oracle_set, key=int)
        lines.append(f"### {a['label']}")
        lines.append(f"- model-repaired (genuine): "
                     f"{', '.join(sorted(a['model_repaired'], key=int)) or 'none'}")
        lines.append(f"- of which **oracle-open (move the union)**: "
                     f"{', '.join(mnew) or 'none'}; re-closures: {', '.join(recl) or 'none'}")
        lines.append("- residue by class:")
        for cls, specs in sorted(a["residue"].items(), key=lambda x: -len(x[1])):
            lines.append(f"  - **{cls}** ({len(specs)}): {', '.join(specs)}")
        lines.append("")
    union_repro = oracle_set | model_new_all
    union_signoff = signoff + len(model_new_all)  # sign-off oracle + model-new
    lines += ["## G1 status line (Rule 7: oracle and model reported separately)\n",
              f"- **oracle = {signoff}/206** (Gate-0 sign-off; {len(oracle_repro)} "
              f"reproducible-now + {gap} unreconciled)",
              f"- **model-only = {max(len(a['pass_at_N']) for a in arms)}/206** "
              f"(best arm; baseline + audited repairs)",
              f"- **model-new (oracle-open specs the model closed) = "
              f"{len(model_new_all)}**: {', '.join(sorted(model_new_all, key=int))}",
              f"- **oracle union model = {union_signoff}/206** (system closure) "
              f"[= {signoff} oracle + {len(model_new_all)} model-new]; "
              f"reproducible floor **{len(union_repro)}/206**",
              "", f"Remaining gap to 206 ({206 - union_signoff} specs, system-open):",
              f"{', '.join(sorted(set(all_nums) - oracle_set - model_new_all, key=int))}",
              "", "*(The remaining gap list uses the reproducible oracle set; the "
              f"{gap} unreconciled Gate-0 closures, once identified, would remove up "
              "to that many from it.)*"]
    return "\n".join(lines)


def load_gate0_closed():
    """Authoritative Gate-0 oracle closure (corpus/gate0_closed.json), NOT inferred
    from model/baseline behavior (that would be self-certifying, PLAN 4). Returns
    (reproducible_closed_set, documented_signoff_count, gap)."""
    art = json.loads((REPO / "corpus" / "gate0_closed.json").read_text())
    closed = set(art["closed_local"]["specs"]) | set(art["closed_hpc"]["specs"])
    return closed, art["reconciliation"]["documented_gate0_closed"], \
        art["reconciliation"]["UNRECONCILED_GAP"]


def run_report(arms_spec: str, out: str):
    corpus = Path("/Users/eric/GitHub/tla_benchmark/data")
    all_nums = sorted({p.stem for p in (corpus / "descriptions").glob("*.json")},
                      key=int)
    arms = []
    for chunk in arms_spec.split(","):
        label, dirs = chunk.split("=")
        arms.append(arm_summary(label, load_arm(dirs.split("+")), all_nums))
    oracle_closed, signoff, gap = load_gate0_closed()
    text = render(arms, all_nums, sorted(oracle_closed, key=int), signoff, gap)
    Path(out).write_text(text)
    print(text)
    print(f"\n[written to {out}]")
