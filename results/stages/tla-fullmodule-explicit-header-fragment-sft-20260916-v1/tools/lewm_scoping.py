#!/usr/bin/env python3
"""LEWM scoping experiment (docs/designs/2026-07-20-lewm-tlc-requirements.md).

Decisive scoping question: LEWM's *entire* addressable population is broken
candidate specs on which plain BFS TLC is slow to find the violation (Q1
established there is no pluggable TLC state-ordering hook, so LEWM could only
ever ship as post-hoc guided replay on suspected-broken candidates). If plain
BFS already finds violations fast on essentially all broken candidates, that
population is ~zero and LEWM is dead on scoping grounds regardless of model
quality.

The prior run (results/runs/lewm-sim-baseline, commit c71e7f1) was
inconclusive because only K=3 known-broken slow candidates existed in the
corpus. This script builds a LARGE labeled-known-broken set BY CONSTRUCTION:
apply harness/mutation.py's existing deterministic operators to verified W4
Opus survivor specs (results/runs/w4-opus-shard*/w2_survivors.jsonl), run
plain BFS TLC on each mutant exactly as harness/runner.py does, and measure
the distribution of time-to-first-violation over the confirmed-broken subset.

Local CPU only. Never SSHes anywhere. Never calls any model/LLM API. Only
subprocess this script runs is `java ... tlc2.TLC` (BFS and -simulate modes).

Standalone: does not modify harness/ or tools/lewm_sim_baseline.py, only
imports read-only helpers (mutation operators, TLC invocation conventions).

Usage:
    python3 tools/lewm_scoping.py --smoke     # 3-mutant smoke test
    python3 tools/lewm_scoping.py             # full sweep (resumable)
    python3 tools/lewm_scoping.py --report     # regenerate SUMMARY.md from rows.jsonl only
"""
import argparse
import glob
import json
import random
import shutil
import statistics
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from harness.mutation import MUTATIONS, apply_mutation  # noqa: E402 (read-only import)
from harness.runner import (  # noqa: E402 (read-only imports, harness/ untouched)
    module_name, check_sany, check_tlc, run_cmd, _jtmpdir, CLASSPATH, TLA_LIBRARY,
)
from tools.lewm_sim_baseline import classify_simulate  # noqa: E402 (read-only import)

OUTDIR = REPO / "results" / "runs" / "lewm-scoping"
ROWS_PATH = OUTDIR / "rows.jsonl"
SIM_ROWS_PATH = OUTDIR / "sim_rows.jsonl"
SUMMARY_PATH = OUTDIR / "SUMMARY.md"
WORKROOT = OUTDIR / "work"
EXCLUSIONS_PATH = REPO / "results" / "analysis" / "w4_exclusions.json"

BFS_CAP_S = 120
SIM_CAP_S = 120
SIM_SEEDS = [0, 1, 2]
SIM_NUM_STATES = 100000
SIM_DEPTH = 100
SLOW_THRESHOLD_S = 30
TARGET_N = 400  # >= 300 required; buffer for vacuous/error attrition
RNG_SEED = 20260721

# shard-59 self-disclosed engineering a mutation-gate exploit across all its
# cells (mutation_evidence untrusted repo-wide); excluded wholesale from this
# mutation-based experiment per task scope, not just from mutation_evidence
# claims elsewhere.
EXCLUDED_SHARD_DIRS = {"w4-opus-shard59"}
# shard-70 self-disclosed reading the mutation battery mid-cell; only that
# one cell's mutation_evidence is untrusted (see w4_exclusions.json note).
EXCLUDED_CELLS_BY_SHARD = {"w4-opus-shard70": {"d0-m6-p2-t3"}}


def load_exclusions():
    d = json.loads(EXCLUSIONS_PATH.read_text())
    return set(d.get("excluded_seed_keys", []))


def load_survivors():
    """Yield (shard_dir_name, row_dict) for every eligible W4 Opus survivor,
    honoring w4_exclusions.json + the shard-59/shard-70 mutation-trust carve-out."""
    excluded_seed_keys = load_exclusions()
    files = sorted(glob.glob(str(REPO / "results" / "runs" / "w4-opus-shard*" / "w2_survivors.jsonl")))
    for f in files:
        shard_dir = Path(f).parent.name
        if shard_dir in EXCLUDED_SHARD_DIRS:
            continue
        bad_cells = EXCLUDED_CELLS_BY_SHARD.get(shard_dir, set())
        for line in Path(f).read_text().splitlines():
            if not line.strip():
                continue
            r = json.loads(line)
            if not r.get("survived"):
                continue
            if r.get("seed_key") in excluded_seed_keys:
                continue
            if r.get("cell") in bad_cells:
                continue
            yield shard_dir, r


def load_existing_rows(path):
    done = set()
    if path.exists():
        for line in path.read_text().splitlines():
            if not line.strip():
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            done.add(r["key"])
    return done


def append_row(path, row):
    OUTDIR.mkdir(parents=True, exist_ok=True)
    with open(path, "a") as fh:
        fh.write(json.dumps(row) + "\n")


def run_bfs_mutant(mod: str, mutant_text: str, cfg_text: str, workdir: Path, timeout: int):
    """Write mutant + cfg, SANY-check, then plain BFS TLC (harness/runner.py's
    check_tlc, unmodified) -- no local deps needed, survivor specs are
    self-contained (EXTENDS only standard library modules)."""
    if workdir.exists():
        shutil.rmtree(workdir, ignore_errors=True)
    workdir.mkdir(parents=True)
    (workdir / f"{mod}.tla").write_text(mutant_text)
    sany_st, sany_out, sany_dt = check_sany(workdir / f"{mod}.tla", workdir, timeout)
    if sany_st != "pass":
        shutil.rmtree(workdir, ignore_errors=True)
        return {"sany": sany_st, "tlc": None, "wall_s": None, "note": "sany_fail_mutant_invalid"}
    (workdir / f"{mod}.cfg").write_text(cfg_text)
    tlc_st, vac, tlc_out, dt = check_tlc(mod, cfg_text, workdir, timeout)
    shutil.rmtree(workdir, ignore_errors=True)
    return {"sany": sany_st, "tlc": tlc_st, "wall_s": round(dt, 2), "note": None}


def run_simulate_mutant(mod: str, mutant_text: str, cfg_text: str, workdir: Path,
                         seed: int, timeout: int):
    if workdir.exists():
        shutil.rmtree(workdir, ignore_errors=True)
    workdir.mkdir(parents=True)
    (workdir / f"{mod}.tla").write_text(mutant_text)
    (workdir / f"{mod}.cfg").write_text(cfg_text)
    cmd = ["java", "-XX:+UseParallelGC", f"-Djava.io.tmpdir={_jtmpdir(workdir)}",
           f"-DTLA-Library={TLA_LIBRARY}", "-cp", CLASSPATH, "tlc2.TLC",
           "-workers", "2", "-cleanup", "-metadir", str(workdir / "states"),
           "-simulate", f"num={SIM_NUM_STATES}", "-depth", str(SIM_DEPTH), "-seed", str(seed),
           "-config", f"{mod}.cfg", f"{mod}.tla"]
    rc, out, dt, timed_out = run_cmd(cmd, workdir, timeout)
    shutil.rmtree(workdir, ignore_errors=True)
    status = classify_simulate(rc, out, timed_out)
    return status, round(dt, 2)


def build_plan(n_target: int):
    """Deterministically shuffle eligible survivors, pair each with its
    applicable mutation operators (regex must actually match, same rule as
    harness/mutation.py), stop once n_target mutant-attempts are queued."""
    survivors = list(load_survivors())
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
        if len(plan) >= n_target:
            break
    return plan


def run_sweep(n_target: int, log=print):
    plan = build_plan(n_target)
    log(f"[lewm-scoping] plan: {len(plan)} mutant-attempts queued "
        f"(target {n_target}) across {len(set(p['seed_key'] for p in plan))} base specs")
    done = load_existing_rows(ROWS_PATH)
    for i, item in enumerate(plan, 1):
        if item["key"] in done:
            continue
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
        log(f"[{i}/{len(plan)}] {item['seed_key']} x {item['mutation']}: "
            f"sany={res['sany']} tlc={res['tlc']} wall={res['wall_s']} "
            f"({time.time()-t0:.1f}s)")
    log("[lewm-scoping] BFS sweep complete")
    return plan


def run_simulate_on_slow_tail(plan, log=print):
    """Step 4: for confirmed-broken BFS-slow mutants (wall_s > SLOW_THRESHOLD_S
    or timeout), run -simulate seeds 0/1/2, 120s cap each."""
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
    log(f"[lewm-scoping] {len(slow_keys)} confirmed-broken BFS-slow/timeout mutants "
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
            log(f"  {key} seed={seed}: {status} ({dt:.1f}s) [bfs was {by_key[key]['tlc']} "
                f"{by_key[key]['wall_s']}s]")
    log("[lewm-scoping] -simulate slow-tail sweep complete")


def pct(sorted_vals, p):
    if not sorted_vals:
        return None
    k = (len(sorted_vals) - 1) * p
    f = int(k)
    c = min(f + 1, len(sorted_vals) - 1)
    if f == c:
        return sorted_vals[f]
    return sorted_vals[f] + (sorted_vals[c] - sorted_vals[f]) * (k - f)


def write_summary():
    rows = [json.loads(l) for l in ROWS_PATH.read_text().splitlines() if l.strip()] \
        if ROWS_PATH.exists() else []
    sim_rows = [json.loads(l) for l in SIM_ROWS_PATH.read_text().splitlines() if l.strip()] \
        if SIM_ROWS_PATH.exists() else []

    n_attempted = len(rows)
    invalid = [r for r in rows if r["sany"] != "pass"]
    valid = [r for r in rows if r["sany"] == "pass"]
    vacuous = [r for r in valid if r["tlc"] == "pass"]
    errored = [r for r in valid if r["tlc"] == "error"]
    confirmed_broken = [r for r in valid if r["tlc"] in
                        ("fail_invariant", "fail_deadlock", "fail_liveness", "timeout")]
    violations = [r for r in confirmed_broken if r["tlc"] != "timeout" and r["wall_s"] is not None]
    timeouts = [r for r in confirmed_broken if r["tlc"] == "timeout"]

    ttv = sorted(r["wall_s"] for r in violations)
    n_slow_violations = sum(1 for t in ttv if t > SLOW_THRESHOLD_S)
    n_addressable = n_slow_violations + len(timeouts)
    n_confirmed = len(confirmed_broken)
    frac_addressable = (n_addressable / n_confirmed) if n_confirmed else None

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

    # simulate head-to-head, grouped by bfs_key
    sim_by_bfs = {}
    for r in sim_rows:
        sim_by_bfs.setdefault(r["bfs_key"], []).append(r)
    n_slow_tail = len(sim_by_bfs)
    n_converted = sum(1 for k, rs in sim_by_bfs.items()
                       if any(r["status"].startswith("violation") for r in rs))

    lines = []
    lines.append("# LEWM scoping experiment: addressable-population headline")
    lines.append("")
    lines.append("2026-07-21. Decisive scoping run for "
                 "docs/designs/2026-07-20-lewm-tlc-requirements.md, superseding the "
                 "inconclusive K=3 result in results/runs/lewm-sim-baseline/SUMMARY.md "
                 "(commit c71e7f1). Question: given LEWM can only ship as option (b) "
                 "(post-hoc guided replay on suspected-broken candidates, per Q1 -- no "
                 "pluggable TLC state-ordering hook exists), how big is its entire "
                 "addressable population -- broken candidates on which plain BFS TLC is "
                 "slow to find the violation?")
    lines.append("")
    lines.append("## Method")
    lines.append("")
    lines.append("- Labeled-known-broken set built BY CONSTRUCTION: harness/mutation.py's "
                 "5 deterministic operators (and_to_or, plus_to_minus, in_to_notin, "
                 "cup_to_cap; eq_to_neq/lt_to_le were dropped upstream as unsafe) applied "
                 "to verified W4 Opus survivor specs "
                 "(results/runs/w4-opus-shard*/w2_survivors.jsonl, ~1898 survivors, "
                 "shard-59 excluded wholesale and shard-70 cell d0-m6-p2-t3 excluded per "
                 "mutation-trust concerns; w4_exclusions.json excluded_seed_keys honored).")
    lines.append("- Each mutant: SANY-checked, then plain BFS TLC exactly as "
                 "harness/runner.py's check_tlc (same classpath/-DTLA-Library/isolated "
                 "java.io.tmpdir conventions), 120s wall cap.")
    lines.append(f"- N = {n_attempted} mutant-attempts, spread across "
                 f"{len(set(r['seed_key'] for r in rows))} distinct base specs and "
                 f"{len(by_op)} distinct mutation operators.")
    lines.append("- Buckets: `invalid` = SANY rejected the mutant (not counted as "
                 "broken or vacuous); `vacuous` = mutant SANY-parsed but plain BFS TLC "
                 "still reports pass (mutation was semantically vacuous -- NOT "
                 "known-broken, excluded from headline, and also not LEWM's target); "
                 "`error` = TLC crash/parse error unrelated to the invariant (excluded, "
                 "same treatment as harness/mutation.py's crash_not_applicable); "
                 "`confirmed_broken` = BFS found a real violation OR BFS timed out -- "
                 "this is the actual population LEWM targets.")
    lines.append("")
    lines.append("## Attempted / confirmed-broken / vacuous")
    lines.append("")
    lines.append(f"| bucket | n | fraction of N |")
    lines.append(f"|---|---|---|")
    lines.append(f"| attempted (N) | {n_attempted} | 100% |")
    lines.append(f"| invalid (SANY reject) | {len(invalid)} | "
                 f"{len(invalid)/n_attempted:.1%} |" if n_attempted else "| invalid | 0 | - |")
    lines.append(f"| vacuous (BFS pass) | {len(vacuous)} | "
                 f"{len(vacuous)/n_attempted:.1%} |" if n_attempted else "")
    lines.append(f"| error (crash, not counted) | {len(errored)} | "
                 f"{len(errored)/n_attempted:.1%} |" if n_attempted else "")
    lines.append(f"| **confirmed_broken** | **{n_confirmed}** | "
                 f"**{n_confirmed/n_attempted:.1%}** |" if n_attempted else "")
    lines.append("")
    lines.append("### By mutation operator")
    lines.append("")
    lines.append("| operator | attempted | invalid | vacuous | error | confirmed_broken |")
    lines.append("|---|---|---|---|---|---|")
    for op, d in sorted(by_op.items()):
        lines.append(f"| {op} | {d['attempted']} | {d['invalid']} | {d['vacuous']} | "
                     f"{d['error']} | {d['confirmed_broken']} |")
    lines.append("")
    lines.append("## THE HEADLINE: BFS time-to-first-violation distribution "
                 "(confirmed-broken only)")
    lines.append("")
    if ttv:
        lines.append(f"Over {len(violations)} confirmed-broken mutants where BFS found "
                     f"a real violation (invariant/deadlock/liveness), wall-clock "
                     f"time-to-first-violation:")
        lines.append("")
        lines.append(f"| stat | seconds |")
        lines.append(f"|---|---|")
        lines.append(f"| median (p50) | {statistics.median(ttv):.2f} |")
        lines.append(f"| p90 | {pct(ttv, 0.90):.2f} |")
        lines.append(f"| p95 | {pct(ttv, 0.95):.2f} |")
        lines.append(f"| p99 | {pct(ttv, 0.99):.2f} |")
        lines.append(f"| max | {ttv[-1]:.2f} |")
    else:
        lines.append("No confirmed-broken-with-violation-found rows yet.")
    lines.append("")
    lines.append(f"Additionally, {len(timeouts)} confirmed-broken mutants had BFS itself "
                 f"time out at the 120s cap without ever finding the violation (or without "
                 f"finishing -- can't distinguish from this measurement alone; both are "
                 f"'BFS did not find it fast').")
    lines.append("")
    lines.append(f"**Addressable population** (confirmed-broken AND BFS-slow, defined as "
                 f"wall_s > {SLOW_THRESHOLD_S}s OR timeout): "
                 f"**{n_addressable} / {n_confirmed}**"
                 + (f" (**{frac_addressable:.1%}** of confirmed-broken mutants, "
                    f"**{n_addressable/n_attempted:.1%}** of all {n_attempted} attempted)"
                    if frac_addressable is not None else "") + ".")
    lines.append("")
    lines.append("## Simulate head-to-head on the slow tail")
    lines.append("")
    lines.append(f"Of the {n_addressable} confirmed-broken BFS-slow/timeout mutants, "
                 f"{n_slow_tail} were run under `-simulate num={SIM_NUM_STATES} "
                 f"-depth {SIM_DEPTH}` seeds {SIM_SEEDS}, {SIM_CAP_S}s cap per seed.")
    lines.append("")
    if n_slow_tail:
        lines.append(f"- Converted to a fast violation under -simulate: "
                     f"{n_converted}/{n_slow_tail} "
                     f"({n_converted/n_slow_tail:.1%}).")
        conv_speedups = []
        for k, rs in sim_by_bfs.items():
            viol = [r for r in rs if r["status"].startswith("violation")]
            if viol:
                fastest = min(r["wall_s"] for r in viol)
                bfs_s = rs[0]["bfs_wall_s"] if rs[0]["bfs_tlc"] != "timeout" else 120.0
                conv_speedups.append(bfs_s / fastest if fastest > 0 else None)
        conv_speedups = [s for s in conv_speedups if s]
        if conv_speedups:
            lines.append(f"- Speedup on converted mutants (BFS wall / fastest -simulate "
                         f"seed wall): median {statistics.median(conv_speedups):.1f}x, "
                         f"max {max(conv_speedups):.1f}x.")
        lines.append(f"- Did NOT convert (ran to no_violation or timed out under "
                     f"-simulate too): {n_slow_tail - n_converted}/{n_slow_tail}.")
    else:
        lines.append("(no slow-tail mutants to test -- see verdict below)")
    lines.append("")
    lines.append("## VERDICT")
    lines.append("")
    if n_confirmed == 0:
        verdict = "INCONCLUSIVE"
        verdict_text = ("No confirmed-broken mutants were produced at all -- the data "
                        "does not separate KILL from KEEP. Needs investigation before "
                        "any disposition.")
    elif frac_addressable is not None and frac_addressable < 0.05 and n_addressable < 15:
        verdict = "KILL"
        verdict_text = (f"The addressable population is negligible: {n_addressable}/"
                        f"{n_confirmed} ({frac_addressable:.1%}) confirmed-broken mutants "
                        f"are BFS-slow. Plain BFS TLC already finds the violation fast on "
                        f"essentially all broken candidates in this labeled-known-broken "
                        f"population. LEWM's entire addressable population (option-(b) "
                        f"post-hoc guided replay on suspected-broken candidates) is "
                        f"~zero regardless of how good a learned model could be. "
                        f"**KILL LEWM on scoping grounds.**")
    elif frac_addressable is not None and n_converted < n_slow_tail * 0.5 if n_slow_tail else True:
        verdict = "KEEP"
        verdict_text = (f"The addressable population is substantial: {n_addressable}/"
                        f"{n_confirmed} ({frac_addressable:.1%}) confirmed-broken mutants "
                        f"are BFS-slow, and TLC's own zero-training -simulate baseline "
                        f"fails to convert most of that tail to a fast violation "
                        f"({n_converted}/{n_slow_tail} converted). That unconverted "
                        f"residual ({n_slow_tail - n_converted} candidates) is exactly "
                        f"LEWM's target population -- BFS is slow, and a cheap zero-"
                        f"training heuristic (random walk) doesn't already solve it. "
                        f"**KEEP LEWM**, scoped narrowly to this residual.")
    else:
        verdict = "KILL"
        verdict_text = (f"The addressable population is real ({n_addressable}/"
                        f"{n_confirmed}, {frac_addressable:.1%}) but TLC's own "
                        f"zero-training -simulate baseline already converts most of it "
                        f"({n_converted}/{n_slow_tail}) to a fast violation with no "
                        f"learned component at all. The residual LEWM would need to add "
                        f"value on is too small to justify the engineering cost "
                        f"(state embedding, transition predictor, cross-spec transfer "
                        f"risk per the design doc's own Risks section). "
                        f"**KILL LEWM on scoping grounds** -- the cheap baseline already "
                        f"captures the addressable win.")
    lines.append(f"**{verdict}**")
    lines.append("")
    lines.append(verdict_text)
    lines.append("")
    SUMMARY_PATH.write_text("\n".join(lines) + "\n")
    return verdict, verdict_text, {
        "n_attempted": n_attempted, "n_invalid": len(invalid), "n_vacuous": len(vacuous),
        "n_error": len(errored), "n_confirmed_broken": n_confirmed,
        "n_addressable": n_addressable, "frac_addressable": frac_addressable,
        "n_slow_tail": n_slow_tail, "n_converted": n_converted,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--smoke", action="store_true", help="3 mutants end-to-end, then exit")
    ap.add_argument("--n", type=int, default=TARGET_N)
    ap.add_argument("--report", action="store_true", help="only regenerate SUMMARY.md from existing rows.jsonl")
    args = ap.parse_args()

    if args.report:
        verdict, _, stats = write_summary()
        print(f"[lewm-scoping] VERDICT={verdict} stats={stats}")
        return

    n_target = 3 if args.smoke else args.n
    plan = run_sweep(n_target)
    if args.smoke:
        print("[smoke] done. Inspect results/runs/lewm-scoping/rows.jsonl")
        return
    run_simulate_on_slow_tail(plan)
    verdict, _, stats = write_summary()
    print(f"[lewm-scoping] VERDICT={verdict} stats={stats}")


if __name__ == "__main__":
    main()
