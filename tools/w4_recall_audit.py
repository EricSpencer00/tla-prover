#!/usr/bin/env python3
"""W4 corpus re-audit against the mutation-recall gate.

    python3 tools/w4_recall_audit.py [--limit 30] [--timeout 60]

tools/w4_audit.py marked the stop floors MET while reading `mutation_evidence`
straight from the ledger. harness/mutation_recall.py then measured the deployed
battery at 0.12 operator recall on the arms that were not engineered against it
(results/analysis/mutation_recall_gate_2026-08-30.md). A ledger label written by
a 0.12-recall battery cannot be read as spec strength, so this re-scores the
corpus the floors were declared on.

Method: stratify the effective corpus (harness.w4_corpus.load_effective) by its
ledgered `mutation_evidence`, sample `--limit` specs per stratum with
mutation_recall.sample_rows (seeded, ledger order), and re-run BOTH the deployed
battery and the reference probes on each. Per spec it records

  reproduced      -- the fresh battery run reaches the ledger's own label
  real_catch      -- some probe operator scored a non-TypeOK safety kill
  verdict         -- covered / recall_miss / no_evidence, as the gate defines it

The number the floors need is the corpus-weighted one: re-weight the three
strata by their corpus sizes to get an operator recall for the corpus as a
whole, and an estimate of how many rows have an invariant that demonstrably
catches a corruption the deployed battery never generates.

Append-only and resumable: rows already in the output file are skipped, so an
interrupted run continues where it stopped.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
import tempfile
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness import w4_corpus  # noqa: E402
from harness.mutation import run_mutation_on_module  # noqa: E402
from harness.mutation_recall import (  # noqa: E402
    MIN_RECALL,
    recall_row,
    run_probe_on_module,
    sample_rows,
    summarize_recall,
)

# Ledger labels, in the order the audit reports them. safety_catch is the
# control arm: those rows the battery already caught, so recall there must be
# high or the probe set is measuring something else.
STRATA = ["no_kill", "no_site", "safety_catch"]

DEFAULT_ROWS = Path("results/analysis/w4_recall_audit_2026-08-30_rows.jsonl")


def battery_evidence(row: dict) -> str:
    """The ledger label a fresh battery run would write for this spec. Same rule
    as w2_loop.py:561 so `reproduced` compares like with like."""
    if not row.get("battery_attempted"):
        return "no_site"
    if row.get("battery_safety_killed"):
        return "safety_catch"
    if row.get("battery_killed"):
        return "typeok_only"
    return "no_kill"


def scored_specs(path: Path) -> dict:
    """spec id -> row, for every spec already in the output ledger."""
    if not path.exists():
        return {}
    out = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if line:
            r = json.loads(line)
            out[r["spec"]] = r
    return out


def score(row: dict, timeout: int) -> dict:
    """One corpus row through both mutant sets, plus the audit's own fields.

    Mirrors mutation_recall.score_survivor but keeps the battery's raw kill
    count, which the gate's own row schema drops and `battery_evidence` needs to
    tell a TypeOK-only kill from no kill at all."""
    mod = row["module"]
    with tempfile.TemporaryDirectory(prefix="w4recall-") as d:
        tla_path = Path(d) / f"{mod}.tla"
        tla_path.write_text(row["spec_text"])
        (Path(d) / f"{mod}.cfg").write_text(row["cfg_text"])
        battery = run_mutation_on_module(tla_path, row["cfg_text"], mod, timeout)
        probe = run_probe_on_module(tla_path, row["cfg_text"], mod, timeout)

    out = recall_row(row.get("seed_key") or mod, battery, probe)
    out["battery_killed"] = battery.get("killed") or 0
    out["ledger_mutation_evidence"] = row.get("mutation_evidence")
    out["shard"] = row.get("_shard")
    out["battery_evidence"] = battery_evidence(out)
    out["reproduced"] = out["battery_evidence"] == out["ledger_mutation_evidence"]
    out["real_catch"] = bool(out["probe_safety_killed"])
    return out


def weighted_recall(rows_by_stratum: dict, sizes: dict):
    """Corpus-weighted operator recall, or None when no stratum has evidence."""
    cov = miss = 0.0
    for name, n in sizes.items():
        rows = rows_by_stratum.get(name, [])
        if not rows:
            continue
        share = n / len(rows)
        cov += share * sum(1 for r in rows if r["verdict"] == "covered")
        miss += share * sum(1 for r in rows if r["verdict"] == "recall_miss")
    if not cov + miss:
        return None, cov, miss
    return cov / (cov + miss), cov, miss


def recall_ci(rows_by_stratum: dict, sizes: dict, draws=5000, seed=0):
    """Percentile bootstrap over specs, resampled within each stratum.

    The stratum is the sampling unit the audit drew on, so the resample has to
    respect it or the interval reads narrower than the design earns."""
    rng = random.Random(seed)
    est = []
    for _ in range(draws):
        boot = {n: [rng.choice(rs) for _ in rs]
                for n, rs in rows_by_stratum.items() if rs}
        r, _, _ = weighted_recall(boot, sizes)
        if r is not None:
            est.append(r)
    if not est:
        return None, None
    est.sort()
    return est[int(0.025 * len(est))], est[int(0.975 * len(est))]


def report(rows_by_stratum: dict, sizes: dict) -> None:
    """Per-stratum recall plus the corpus-weighted estimate the floors turn on.

    Per-stratum recall is NOT the corpus number. `covered` needs a battery kill,
    and the no_kill/no_site strata are defined by the battery not killing, so
    their recall is 0.00 by construction. Re-weighting the three strata by their
    corpus sizes is what gives a recall for the corpus as a whole."""
    print("\n== re-audit summary ==")
    print(f"{'stratum':<14}{'n':>4}{'cov':>5}{'miss':>6}{'noev':>6}"
          f"{'recall':>8}{'real_catch':>12}{'reproduced':>12}")
    for name in STRATA:
        rows = rows_by_stratum.get(name, [])
        if not rows:
            continue
        rep = summarize_recall(rows)
        real = sum(1 for r in rows if r["real_catch"])
        repro = sum(1 for r in rows if r["reproduced"])
        recall = "-" if rep["operator_recall"] is None else f"{rep['operator_recall']:.2f}"
        print(f"{name:<14}{len(rows):>4}{rep['covered']:>5}{rep['recall_miss']:>6}"
              f"{rep['no_evidence']:>6}{recall:>8}"
              f"{real:>7}/{len(rows):<4}{repro:>7}/{len(rows):<4}")

    weak = [r for n in ("no_kill", "no_site") for r in rows_by_stratum.get(n, [])]
    if weak:
        real = sum(1 for r in weak if r["real_catch"])
        print(f"\nweak-labelled rows (no_kill + no_site) with a demonstrable catch: "
              f"{real}/{len(weak)} = {real / len(weak):.0%}")

    catch = 0.0
    for name, n in sizes.items():
        rows = rows_by_stratum.get(name, [])
        if not rows:
            continue
        catch += (n / len(rows)) * sum(1 for r in rows if r["real_catch"])
    total = sum(sizes.values())
    recall, cov, miss = weighted_recall(rows_by_stratum, sizes)
    if recall is not None:
        lo, hi = recall_ci(rows_by_stratum, sizes)
        print(f"corpus-weighted operator recall = {cov:.0f}/{cov + miss:.0f} = "
              f"{recall:.2f} (bootstrap 95% CI [{lo:.2f}, {hi:.2f}], "
              f"floor {MIN_RECALL})")
    print(f"corpus rows with a demonstrable catch ~= {catch:.0f}/{total} = "
          f"{catch / total:.0%}; ledgered safety_catch = {sizes.get('safety_catch', 0)} "
          f"= {sizes.get('safety_catch', 0) / total:.0%}")

    ops = Counter()
    for rows in rows_by_stratum.values():
        for r in rows:
            if r["verdict"] == "recall_miss":
                ops.update(r["probe_killers"])
    print(f"operators the battery is missing: {dict(ops.most_common()) or '(none)'}")


def main() -> int:
    ap = argparse.ArgumentParser(prog="w4_recall_audit")
    ap.add_argument("--limit", type=int, default=30, help="specs per stratum")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--rows", type=Path, default=DEFAULT_ROWS)
    args = ap.parse_args()

    corpus = w4_corpus.load_effective()
    strata = {n: [r for r in corpus if r.get("mutation_evidence") == n] for n in STRATA}
    print("== W4 mutation-recall re-audit ==")
    print(f"effective corpus {len(corpus)}; strata "
          + "  ".join(f"{n}={len(strata[n])}" for n in STRATA))
    print(f"sample {args.limit}/stratum, seed {args.seed}, timeout {args.timeout}s")

    done = scored_specs(args.rows)
    if done:
        print(f"resuming: {len(done)} specs already scored in {args.rows}")

    args.rows.parent.mkdir(parents=True, exist_ok=True)
    rows_by_stratum: dict = {n: [] for n in STRATA}
    for name in STRATA:
        sample = sample_rows(strata[name], args.limit, args.seed)
        print(f"-- stratum {name} (N={len(strata[name])})")
        for row in sample:
            spec = row.get("seed_key")
            out = done.get(spec)
            if out is None:
                out = score(row, args.timeout)
                with args.rows.open("a") as fh:
                    fh.write(json.dumps(out) + "\n")
                print(f"  [{name}] {spec}: {out['verdict']} "
                      f"battery={out['battery_safety_killed']}/{out['battery_attempted']} "
                      f"probe={out['probe_safety_killed']}/{out['probe_attempted']} "
                      f"killers={','.join(out['probe_killers']) or '-'}", flush=True)
            out.setdefault("real_catch", bool(out["probe_safety_killed"]))
            out.setdefault("reproduced", True)
            rows_by_stratum[name].append(out)

    report(rows_by_stratum, {n: len(strata[n]) for n in STRATA})
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
