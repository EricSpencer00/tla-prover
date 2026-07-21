#!/usr/bin/env python3
"""LEWM full-corpus KILL confirmation (docs/designs/2026-07-20-lewm-tlc-requirements.md,
"Scoping result / disposition" section).

The KILL is already ratified by Eric (2026-07-21) off `results/runs/lewm-scoping/`
(tools/lewm_scoping.py), a 400-mutant-attempt sample over 150 of ~1839 eligible W4
Opus survivor specs. This script CONFIRMS (or refutes) that result at full-corpus
scale: EVERY eligible survivor (not a 150-spec sample), all 4 harness/mutation.py
operators that have a real match site per spec, plain BFS TLC exactly as before.

Standalone: does not modify harness/ or tools/lewm_scoping.py. Imports the proven
helpers directly from tools.lewm_scoping (which itself only reads harness/mutation.py
and harness/runner.py, read-only) -- load_survivors/load_exclusions (corpus +
exclusion handling), run_bfs_mutant/run_simulate_mutant (TLC invocation), MUTATIONS/
apply_mutation (mutation operators), classify_simulate, pct, load_existing_rows,
append_row (resumable-row plumbing).

Local CPU only. Never SSHes anywhere. Never calls any model/LLM API. The only
subprocess this script runs is `java ... tlc2.TLC` (BFS and -simulate modes), same
as tools/lewm_scoping.py.

Usage:
    python3 tools/lewm_confirm_fullcorpus.py --smoke     # 3-mutant smoke test
    python3 tools/lewm_confirm_fullcorpus.py             # full sweep (resumable)
    python3 tools/lewm_confirm_fullcorpus.py --report     # regenerate SUMMARY.md from rows.jsonl only
"""
import argparse
import json
import random
import statistics
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from tools.lewm_scoping import (  # noqa: E402  (read-only imports; do not fork lewm_scoping.py)
    MUTATIONS, apply_mutation, module_name,
    load_survivors, load_existing_rows, append_row,
    run_bfs_mutant, run_simulate_mutant, classify_simulate, pct,
    BFS_CAP_S, SIM_CAP_S, SIM_SEEDS, SIM_NUM_STATES, SIM_DEPTH, SLOW_THRESHOLD_S,
)

OUTDIR = REPO / "results" / "runs" / "lewm-confirm"
ROWS_PATH = OUTDIR / "rows.jsonl"
SIM_ROWS_PATH = OUTDIR / "sim_rows.jsonl"
SUMMARY_PATH = OUTDIR / "SUMMARY.md"
WORKROOT = OUTDIR / "work"

RNG_SEED = 99720721  # distinct from lewm_scoping's RNG_SEED (20260721) -- independent shuffle
# Restricted-operator subset per task: and_to_or structurally hits the temporal
# Spec def (SANY-valid, TLC-uncheckable "error"); in_to_notin structurally hits
# quantifier bindings (SANY reject). Both are run anyway (reflects the real
# pipeline) but excluded from the "(b) restricted" headline reading.
CHECKABLE_OPERATORS = {"cup_to_cap", "plus_to_minus"}
# Soft budget on the BFS sweep loop only, leaving headroom in the 5h task budget
# for -simulate-on-slow-tail + SUMMARY.md + doc append + commit.
SWEEP_BUDGET_S = 4.5 * 3600


def build_full_plan():
    """Every eligible survivor (load_survivors() already honors
    w4_exclusions.json's excluded_seed_keys + the shard-59/shard-70 mutation-trust
    carve-outs, unmodified), deduped by seed_key keeping the LAST occurrence in
    shard-file append order (matches w4_exclusions.json's own dedup_overrides
    "keep-last" convention for correction rows -- avoids double-mutating a spec
    whose only difference is corrected NL prose), paired with every mutation
    operator that has a real regex match site, in a deterministic shuffled order
    (so a time-budget cutoff still yields an unbiased partial sample)."""
    seen = {}
    for shard_dir, r in load_survivors():
        seen[r["seed_key"]] = (shard_dir, r)
    survivors = list(seen.values())
    rng = random.Random(RNG_SEED)
    rng.shuffle(survivors)
    plan = []
    for shard_dir, r in survivors:
        spec_text = r["spec_text"]
        mod = r.get("module") or module_name(spec_text)
        if not mod:
            continue
        for label, regex, repl in MUTATIONS:
            mutant_text, n = apply_mutation(spec_text, regex, repl)
            if mutant_text is None:
                continue  # operator not applicable to this spec, not counted
            key = f"{r['seed_key']}::{label}"
            plan.append({
                "key": key, "shard": shard_dir, "seed_key": r["seed_key"],
                "cell": r.get("cell"), "module": mod, "mutation": label,
                "spec_text": spec_text, "mutant_text": mutant_text,
                "cfg_text": r["cfg_text"],
            })
    return plan, len(survivors)


def run_sweep(plan, log=print, budget_seconds=None):
    done = load_existing_rows(ROWS_PATH)
    start = time.time()
    total = len(plan)
    n_run_this_session = 0
    stopped_early = False
    for i, item in enumerate(plan, 1):
        if item["key"] in done:
            continue
        if budget_seconds is not None and (time.time() - start) > budget_seconds:
            log(f"[lewm-confirm] BUDGET EXCEEDED ({budget_seconds/3600:.1f}h) at "
                f"plan item {i}/{total}; stopping cleanly (resumable on restart)")
            stopped_early = True
            break
        workdir = WORKROOT / f"bfs-{i}"
        t0 = time.time()
        res = run_bfs_mutant(item["module"], item["mutant_text"], item["cfg_text"],
                              workdir, BFS_CAP_S)
        row = {
            "key": item["key"], "shard": item["shard"], "seed_key": item["seed_key"],
            "cell": item["cell"], "spec_module": item["module"], "mutation": item["mutation"],
            "sany": res["sany"], "tlc": res["tlc"], "wall_s": res["wall_s"],
            "note": res["note"], "timestamp": time.time(),
        }
        append_row(ROWS_PATH, row)
        done.add(item["key"])
        n_run_this_session += 1
        if n_run_this_session % 50 == 0 or res["tlc"] == "timeout":
            elapsed_min = (time.time() - start) / 60
            log(f"[{i}/{total}] this_session={n_run_this_session} "
                f"elapsed={elapsed_min:.1f}min last={item['seed_key']} x "
                f"{item['mutation']}: sany={res['sany']} tlc={res['tlc']} "
                f"wall={res['wall_s']} ({time.time()-t0:.1f}s)")
    if not stopped_early:
        log(f"[lewm-confirm] BFS sweep complete: {len(done)}/{total} total rows "
            f"({n_run_this_session} run this session)")
    return stopped_early


def run_simulate_on_slow_tail(plan, log=print):
    """Same protocol as lewm_scoping.run_simulate_on_slow_tail (which is not
    reused directly because it is hardwired to lewm-scoping's own OUTDIR/paths)
    -- TLC invocation itself (run_simulate_mutant, classify_simulate) IS reused."""
    if not ROWS_PATH.exists():
        return
    rows = [json.loads(l) for l in ROWS_PATH.read_text().splitlines() if l.strip()]
    by_key = {r["key"]: r for r in rows}
    slow_keys = []
    for r in rows:
        if r["tlc"] in ("fail_invariant", "fail_deadlock", "fail_liveness") and \
                r["wall_s"] is not None and r["wall_s"] > SLOW_THRESHOLD_S:
            slow_keys.append(r["key"])
        elif r["tlc"] == "timeout":
            slow_keys.append(r["key"])
    plan_by_key = {p["key"]: p for p in plan}
    done = load_existing_rows(SIM_ROWS_PATH)
    log(f"[lewm-confirm] {len(slow_keys)} confirmed-broken BFS-slow/timeout mutants "
        f"queued for -simulate head-to-head")
    for key in slow_keys:
        item = plan_by_key.get(key)
        if item is None:
            continue
        for seed in SIM_SEEDS:
            sim_key = f"{key}::seed{seed}"
            if sim_key in done:
                continue
            workdir = WORKROOT / f"sim-{key[:40].replace('/', '_')}-{seed}"
            status, dt = run_simulate_mutant(item["module"], item["mutant_text"],
                                              item["cfg_text"], workdir, seed, SIM_CAP_S)
            row = {"key": sim_key, "bfs_key": key, "seed": seed, "status": status,
                   "wall_s": dt, "bfs_wall_s": by_key[key]["wall_s"],
                   "bfs_tlc": by_key[key]["tlc"], "timestamp": time.time()}
            append_row(SIM_ROWS_PATH, row)
            done.add(sim_key)
            log(f"  {key} seed={seed}: {status} ({dt:.1f}s) [bfs was "
                f"{by_key[key]['tlc']} {by_key[key]['wall_s']}s]")
    log("[lewm-confirm] -simulate slow-tail sweep complete")


def _bucket_counts(rows):
    invalid = [r for r in rows if r["sany"] != "pass"]
    valid = [r for r in rows if r["sany"] == "pass"]
    vacuous = [r for r in valid if r["tlc"] == "pass"]
    errored = [r for r in valid if r["tlc"] == "error"]
    confirmed_broken = [r for r in valid if r["tlc"] in
                        ("fail_invariant", "fail_deadlock", "fail_liveness", "timeout")]
    return invalid, vacuous, errored, confirmed_broken


def _addressable_stats(confirmed_broken):
    violations = [r for r in confirmed_broken if r["tlc"] != "timeout" and r["wall_s"] is not None]
    timeouts = [r for r in confirmed_broken if r["tlc"] == "timeout"]
    ttv = sorted(r["wall_s"] for r in violations)
    n_slow_violations = sum(1 for t in ttv if t > SLOW_THRESHOLD_S)
    n_addressable = n_slow_violations + len(timeouts)
    n_confirmed = len(confirmed_broken)
    frac_of_confirmed = (n_addressable / n_confirmed) if n_confirmed else None
    return {
        "ttv": ttv, "n_violations": len(violations), "n_timeouts": len(timeouts),
        "n_addressable": n_addressable, "n_confirmed": n_confirmed,
        "frac_of_confirmed": frac_of_confirmed,
    }


def write_summary(coverage_note=""):
    rows = [json.loads(l) for l in ROWS_PATH.read_text().splitlines() if l.strip()] \
        if ROWS_PATH.exists() else []
    sim_rows = [json.loads(l) for l in SIM_ROWS_PATH.read_text().splitlines() if l.strip()] \
        if SIM_ROWS_PATH.exists() else []

    n_attempted = len(rows)
    invalid, vacuous, errored, confirmed_broken = _bucket_counts(rows)
    n_confirmed = len(confirmed_broken)

    by_op = {}
    for r in rows:
        by_op.setdefault(r["mutation"], {"attempted": 0, "invalid": 0, "vacuous": 0,
                                          "error": 0, "confirmed_broken": 0})
        d = by_op[r["mutation"]]
        d["attempted"] += 1
        if r["sany"] != "pass":
            d["invalid"] += 1
        elif r["tlc"] == "pass":
            d["vacuous"] += 1
        elif r["tlc"] == "error":
            d["error"] += 1
        else:
            d["confirmed_broken"] += 1

    stats_a = _addressable_stats(confirmed_broken)  # (a) all operators
    checkable_rows = [r for r in rows if r["mutation"] in CHECKABLE_OPERATORS]
    _, _, _, confirmed_broken_b = _bucket_counts(checkable_rows)
    stats_b = _addressable_stats(confirmed_broken_b)  # (b) cup_to_cap + plus_to_minus only

    sim_by_bfs = {}
    for r in sim_rows:
        sim_by_bfs.setdefault(r["bfs_key"], []).append(r)
    n_slow_tail = len(sim_by_bfs)
    n_converted = sum(1 for k, rs in sim_by_bfs.items()
                       if any(r["status"].startswith("violation") for r in rs))

    def fmt_ttv_table(ttv):
        if not ttv:
            return ["(no confirmed-broken-with-violation-found rows)"]
        return [
            "| stat | seconds |", "|---|---|",
            f"| median (p50) | {statistics.median(ttv):.2f} |",
            f"| p90 | {pct(ttv, 0.90):.2f} |",
            f"| p95 | {pct(ttv, 0.95):.2f} |",
            f"| p99 | {pct(ttv, 0.99):.2f} |",
            f"| max | {ttv[-1]:.2f} |",
        ]

    lines = []
    lines.append("# LEWM full-corpus KILL confirmation")
    lines.append("")
    lines.append("2026-07-21. Full-corpus confirmation of the ratified KILL decision "
                 "(docs/designs/2026-07-20-lewm-tlc-requirements.md, \"Scoping result / "
                 "disposition\"), which was based on a 400-mutant-attempt sample over "
                 "150 of ~1839 eligible W4 Opus survivor specs "
                 "(results/runs/lewm-scoping/). This run sweeps EVERY eligible survivor "
                 "(not a sample), all 4 harness/mutation.py operators per spec where "
                 "applicable, to check whether the addressable population "
                 "(confirmed-broken AND BFS-slow) stays negligible at full scale.")
    lines.append("")
    lines.append(coverage_note)
    lines.append("")
    lines.append("## Method")
    lines.append("")
    lines.append("- Same corpus, same exclusions, same TLC invocation as "
                 "results/runs/lewm-scoping/ (tools/lewm_scoping.py's load_survivors(), "
                 "load_exclusions(), run_bfs_mutant/run_simulate_mutant, imported not "
                 "forked). Eligible survivors deduped by seed_key (keep-last in "
                 "shard-file append order, matching w4_exclusions.json's own "
                 "dedup_overrides convention for correction rows).")
    lines.append("- Each mutant: SANY-checked, then plain BFS TLC, 120s wall cap. "
                 "Buckets identical to lewm-scoping: `invalid` (SANY reject), "
                 "`vacuous` (BFS still passes), `error` (TLC crash unrelated to the "
                 "invariant), `confirmed_broken` (BFS found a violation OR timed out).")
    lines.append(f"- N = {n_attempted} mutant-attempts across "
                 f"{len(set(r['seed_key'] for r in rows))} distinct base specs and "
                 f"{len(by_op)} distinct mutation operators.")
    lines.append("")
    lines.append("## Attempted / confirmed-broken / vacuous (all operators)")
    lines.append("")
    lines.append("| bucket | n | fraction of N |")
    lines.append("|---|---|---|")
    if n_attempted:
        lines.append(f"| attempted (N) | {n_attempted} | 100% |")
        lines.append(f"| invalid (SANY reject) | {len(invalid)} | {len(invalid)/n_attempted:.1%} |")
        lines.append(f"| vacuous (BFS pass) | {len(vacuous)} | {len(vacuous)/n_attempted:.1%} |")
        lines.append(f"| error (crash, not counted) | {len(errored)} | {len(errored)/n_attempted:.1%} |")
        lines.append(f"| **confirmed_broken** | **{n_confirmed}** | **{n_confirmed/n_attempted:.1%}** |")
    lines.append("")
    lines.append("### By mutation operator")
    lines.append("")
    lines.append("| operator | attempted | invalid | vacuous | error | confirmed_broken |")
    lines.append("|---|---|---|---|---|---|")
    for op, d in sorted(by_op.items()):
        lines.append(f"| {op} | {d['attempted']} | {d['invalid']} | {d['vacuous']} | "
                     f"{d['error']} | {d['confirmed_broken']} |")
    lines.append("")
    lines.append("Note (expected, per task design): `and_to_or` structurally corrupts "
                 "the temporal Spec definition -> SANY-valid but TLC-uncheckable "
                 "`error`; `in_to_notin` structurally hits quantifier bindings -> SANY "
                 "reject. Both run anyway (reflects the real pipeline); the headline "
                 "below is computed both including and excluding them.")
    lines.append("")
    lines.append("## THE HEADLINE: BFS time-to-first-violation, computed two ways")
    lines.append("")
    lines.append("### (a) All confirmed-broken mutants, regardless of operator")
    lines.append("")
    lines.extend(fmt_ttv_table(stats_a["ttv"]))
    lines.append("")
    lines.append(f"{stats_a['n_timeouts']} confirmed-broken mutants had BFS itself "
                 f"time out at the 120s cap without ever finding the violation.")
    lines.append("")
    lines.append(f"**Addressable population (a):** {stats_a['n_addressable']} / "
                 f"{stats_a['n_confirmed']}"
                 + (f" ({stats_a['frac_of_confirmed']:.1%} of confirmed-broken, "
                    f"{stats_a['n_addressable']/n_attempted:.1%} of all {n_attempted} attempted)"
                    if stats_a['frac_of_confirmed'] is not None else "") + ".")
    lines.append("")
    lines.append("### (b) Restricted to checkable operators only (cup_to_cap, plus_to_minus)")
    lines.append("")
    lines.append(f"({len(checkable_rows)} attempts, {len(confirmed_broken_b)} confirmed-broken "
                 f"under this restriction)")
    lines.append("")
    lines.extend(fmt_ttv_table(stats_b["ttv"]))
    lines.append("")
    lines.append(f"{stats_b['n_timeouts']} confirmed-broken mutants (checkable operators "
                 f"only) had BFS time out at the 120s cap.")
    lines.append("")
    lines.append(f"**Addressable population (b):** {stats_b['n_addressable']} / "
                 f"{stats_b['n_confirmed']}"
                 + (f" ({stats_b['frac_of_confirmed']:.1%} of confirmed-broken under this "
                    f"restriction, {stats_b['n_addressable']/len(checkable_rows):.1%} of "
                    f"{len(checkable_rows)} checkable-operator attempts)"
                    if stats_b['frac_of_confirmed'] is not None and checkable_rows else "") + ".")
    lines.append("")
    lines.append("## Simulate head-to-head on the slow tail")
    lines.append("")
    lines.append(f"Of the {stats_a['n_addressable']} confirmed-broken BFS-slow/timeout "
                 f"mutants (definition (a), all operators), {n_slow_tail} were run under "
                 f"`-simulate num={SIM_NUM_STATES} -depth {SIM_DEPTH}` seeds {SIM_SEEDS}, "
                 f"{SIM_CAP_S}s cap per seed.")
    lines.append("")
    if n_slow_tail:
        lines.append(f"- Converted to a fast violation under -simulate: "
                     f"{n_converted}/{n_slow_tail} ({n_converted/n_slow_tail:.1%}).")
        conv_speedups = []
        for k, rs in sim_by_bfs.items():
            viol = [r for r in rs if r["status"].startswith("violation")]
            if viol:
                fastest = min(r["wall_s"] for r in viol)
                bfs_s = rs[0]["bfs_wall_s"] if rs[0]["bfs_tlc"] != "timeout" else 120.0
                if fastest > 0:
                    conv_speedups.append(bfs_s / fastest)
        if conv_speedups:
            lines.append(f"- Speedup on converted mutants (BFS wall / fastest -simulate "
                         f"seed wall): median {statistics.median(conv_speedups):.1f}x, "
                         f"max {max(conv_speedups):.1f}x.")
        lines.append(f"- Did NOT convert: {n_slow_tail - n_converted}/{n_slow_tail}.")
    else:
        lines.append("(no slow-tail mutants to test)")
    lines.append("")
    lines.append("## VERDICT")
    lines.append("")
    if n_confirmed == 0:
        verdict = "INCONCLUSIVE"
        verdict_text = "No confirmed-broken mutants were produced at all."
    elif (stats_a["frac_of_confirmed"] is not None and stats_a["frac_of_confirmed"] <= 0.05
          and stats_a["n_addressable"] < 30):
        verdict = "CONFIRMED"
        verdict_text = (
            f"KILL CONFIRMED at full-corpus scale. Addressable population (a, all "
            f"operators): {stats_a['n_addressable']}/{stats_a['n_confirmed']} "
            f"({stats_a['frac_of_confirmed']:.1%} of confirmed-broken, "
            f"{stats_a['n_addressable']/n_attempted:.1%} of all {n_attempted} attempted). "
            f"Restricted to checkable operators only (b): "
            f"{stats_b['n_addressable']}/{stats_b['n_confirmed']}"
            + (f" ({stats_b['frac_of_confirmed']:.1%})" if stats_b['frac_of_confirmed'] is not None else "")
            + f". Both readings stay negligible and absolute counts stay tiny, "
            f"consistent with the 150-spec scoping sample "
            f"(2/20, 0.5% of attempts). LEWM's entire addressable population "
            f"(option-(b) post-hoc guided replay, per the design doc's Q1) remains "
            f"~zero at full scale. The ratified KILL stands."
        )
    else:
        verdict = "REFUTED"
        verdict_text = (
            f"KILL REFUTED at full-corpus scale. Addressable population (a): "
            f"{stats_a['n_addressable']}/{stats_a['n_confirmed']} "
            f"({stats_a['frac_of_confirmed']:.1%} of confirmed-broken, "
            f"{stats_a['n_addressable']/n_attempted:.1%} of all attempted) -- this is "
            f"a SUBSTANTIALLY larger absolute/fractional population than the 150-spec "
            f"scoping sample found (2/20, 0.5%). Restricted reading (b): "
            f"{stats_b['n_addressable']}/{stats_b['n_confirmed']}"
            + (f" ({stats_b['frac_of_confirmed']:.1%})" if stats_b['frac_of_confirmed'] is not None else "")
            + f". This warrants revisiting the LEWM disposition -- flag to Eric before "
            f"proceeding with the park decision as final."
        )
    lines.append(f"**{verdict}**")
    lines.append("")
    lines.append(verdict_text)
    lines.append("")
    SUMMARY_PATH.parent.mkdir(parents=True, exist_ok=True)
    SUMMARY_PATH.write_text("\n".join(lines) + "\n")
    return verdict, verdict_text, {
        "n_attempted": n_attempted, "n_invalid": len(invalid), "n_vacuous": len(vacuous),
        "n_error": len(errored), "n_confirmed_broken": n_confirmed,
        "stats_a": stats_a, "stats_b": stats_b,
        "n_slow_tail": n_slow_tail, "n_converted": n_converted,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--smoke", action="store_true", help="3 mutants end-to-end, then exit")
    ap.add_argument("--report", action="store_true", help="only regenerate SUMMARY.md from existing rows.jsonl")
    ap.add_argument("--budget-hours", type=float, default=SWEEP_BUDGET_S / 3600)
    args = ap.parse_args()

    if args.report:
        verdict, _, stats = write_summary()
        print(f"[lewm-confirm] VERDICT={verdict} stats={stats}")
        return

    plan, n_survivors = build_full_plan()
    print(f"[lewm-confirm] plan: {len(plan)} mutant-attempts queued across "
          f"{n_survivors} eligible (deduped) survivors")

    if args.smoke:
        smoke_plan = plan[:3]
        run_sweep(smoke_plan)
        print("[smoke] done. Inspect results/runs/lewm-confirm/rows.jsonl")
        return

    stopped_early = run_sweep(plan, budget_seconds=args.budget_hours * 3600)
    run_simulate_on_slow_tail(plan)
    coverage_note = (
        f"(Coverage: {len(load_existing_rows(ROWS_PATH))}/{len(plan)} planned mutant-attempts "
        f"across {n_survivors} eligible survivors" +
        (", stopped early at the time budget -- resumable, re-run to continue.)"
         if stopped_early else ", full planned sweep completed.)")
    )
    verdict, _, stats = write_summary(coverage_note=coverage_note)
    print(f"[lewm-confirm] VERDICT={verdict} stats={stats}")


if __name__ == "__main__":
    main()
