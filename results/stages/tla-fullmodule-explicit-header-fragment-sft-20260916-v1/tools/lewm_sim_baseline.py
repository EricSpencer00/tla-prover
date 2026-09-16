#!/usr/bin/env python3
"""LEWM Open-Question-3 falsifiable baseline (docs/designs/2026-07-20-lewm-tlc-requirements.md).

Measures TLC's built-in `-simulate` random-walk mode as a non-learned baseline
for time-to-first-violation, on the recorded slow/timeout/repair candidates in
results/analysis/lewm_baseline_candidates.json, BEFORE any learned fail-fast
triage model is justified.

Standalone: does not modify harness/, only imports read-only helpers from it
(module_name parsing, dependency resolution, exact classpath/-DTLA-Library/
java.io.tmpdir conventions) so the TLC invocation is byte-for-byte consistent
with the rest of the repo's tooling.

Local CPU only. Never SSHes anywhere. Never calls any model/LLM API -- the
only subprocess this script runs is `java ... tlc2.TLC -simulate`.

Usage:
    python3 tools/lewm_sim_baseline.py --smoke      # 2-candidate smoke test
    python3 tools/lewm_sim_baseline.py               # full sweep (resumable)
"""
import argparse
import hashlib
import json
import re
import shutil
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))

from harness.runner import (  # noqa: E402  (read-only imports, harness/ untouched)
    module_name, build_module_index, local_deps, _write_local_deps, _jtmpdir,
    run_cmd, POLICY,
)

CORPUS = Path("/Users/eric/GitHub/tla_benchmark/data")  # per gate2-v2-120b-B config.json
MANIFEST = REPO / "results" / "analysis" / "lewm_baseline_candidates.json"
OUTDIR = REPO / "results" / "runs" / "lewm-sim-baseline"
ROWS_PATH = OUTDIR / "rows.jsonl"
WORKROOT = OUTDIR / "work"
SEEDS = [0, 1, 2]
WALL_CAP_S = 120
NUM_STATES = 100000
DEPTH = 100

CFG_DIRS = [
    ("override", REPO / "corpus" / "configs" / "overrides"),
    ("original", CORPUS / "cfg"),
    ("draft", REPO / "corpus" / "configs" / "drafts"),
]


def resolve_cfg(num: str):
    for label, d in CFG_DIRS:
        c = d / f"{num}.cfg"
        if c.exists():
            return c.read_text(errors="replace"), label
    return None, None


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def classify_simulate(rc: int, out: str, timed_out: bool):
    """Adapted from harness.runner.classify_tlc for -simulate mode output.
    -simulate never terminates "cleanly" with a states-exhausted verdict the
    way -simulate num=N does when N random traces are exhausted without
    finding a violation -- that shows up as normal (rc==0) completion."""
    if timed_out:
        return "timeout"
    if "Invariant" in out and "is violated" in out:
        return "violation_invariant"
    if "Deadlock reached" in out:
        return "violation_deadlock"
    if "Temporal properties were violated" in out:
        return "violation_liveness"
    if "The number of states generated" in out or "the depth-first simulation" in out or rc == 0:
        return "no_violation"
    return "error"


TIME_ELAPSED_RE = re.compile(r"in\s+(\d+)h(\d+)m(\d+)s\s+at", re.M)
FINISHED_RE = re.compile(r"Finished in (\d+)s at", re.M)


def parse_ttv_from_output(out: str, wall_s: float, found_violation: bool):
    """Best-effort time-to-violation from TLC's own 'Finished in Ns' report;
    falls back to measured wall-clock (the process exits essentially as soon
    as TLC halts on the violation, so wall_s is already a good proxy)."""
    if not found_violation:
        return None
    m = FINISHED_RE.search(out)
    if m:
        return float(m.group(1))
    return round(wall_s, 2)


def prepare_candidate_workdir(num: str, mod: str, text: str, num2mod, mod2path, workdir: Path):
    """Write candidate + local deps + resolved cfg (with wrapper-policy
    handling) into workdir. Returns (tlc_mod, cfg_text, cfg_origin) or
    (None, None, reason) if the cfg can't be recovered."""
    if workdir.exists():
        shutil.rmtree(workdir, ignore_errors=True)
    workdir.mkdir(parents=True)
    (workdir / f"{mod}.tla").write_text(text)
    seen = _write_local_deps(text, mod, mod2path, workdir, set())

    cfg_text, cfg_origin = resolve_cfg(num)
    if cfg_text is None:
        return None, None, None, "no_cfg_found"

    pol = POLICY.get(num, {})
    tlc_mod = mod
    if "wrapper" in pol:
        w = pol["wrapper"]
        if "corpus_spec" in w:
            w_num = w["corpus_spec"]
            w_mod = num2mod.get(w_num)
            if w_mod is None or w_mod not in mod2path:
                return None, None, None, f"wrapper_corpus_spec_{w_num}_unresolved"
            w_path = mod2path[w_mod]
            w_patch = REPO / "corpus" / "configs" / "patches" / f"{w_num}.tla"
            w_text = w_patch.read_text(errors="replace") if w_patch.exists() else w_path.read_text(errors="replace")
            (workdir / f"{w_mod}.tla").write_text(w_text)
            for d in (local_deps(w_text, mod2path) - seen - {mod}):
                seen.add(d)
                dtext = mod2path[d].read_text(errors="replace")
                (workdir / f"{d}.tla").write_text(dtext)
            tlc_mod = w_mod
        else:
            w_file = REPO / w["file"]
            if not w_file.exists():
                return None, None, None, f"wrapper_file_missing_{w['file']}"
            w_text = w_file.read_text()
            (workdir / f"{w['module']}.tla").write_text(w_text)
            for d in (local_deps(w_text, mod2path) - seen - {mod}):
                seen.add(d)
                dtext = mod2path[d].read_text(errors="replace")
                (workdir / f"{d}.tla").write_text(dtext)
            tlc_mod = w["module"]
    (workdir / f"{tlc_mod}.cfg").write_text(cfg_text)
    return tlc_mod, cfg_text, cfg_origin, None


def run_tlc_simulate(tlc_mod: str, workdir: Path, seed: int, extra_flags, jvm_flags, wall_cap: int):
    from harness.runner import CLASSPATH, TLA_LIBRARY
    cmd = ["java", "-XX:+UseParallelGC", f"-Djava.io.tmpdir={_jtmpdir(workdir)}",
           f"-DTLA-Library={TLA_LIBRARY}", *jvm_flags, "-cp", CLASSPATH, "tlc2.TLC",
           "-workers", "2", "-cleanup", "-metadir", str(workdir / "states"),
           *extra_flags,
           "-simulate", f"num={NUM_STATES}", "-depth", str(DEPTH), "-seed", str(seed),
           "-config", f"{tlc_mod}.cfg", f"{tlc_mod}.tla"]
    rc, out, dt, timed_out = run_cmd(cmd, workdir, wall_cap)
    status = classify_simulate(rc, out, timed_out)
    found_violation = status.startswith("violation")
    ttv = parse_ttv_from_output(out, dt, found_violation)
    return status, dt, ttv, out


def load_existing_rows():
    done = set()
    if ROWS_PATH.exists():
        for line in ROWS_PATH.read_text().splitlines():
            if not line.strip():
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            done.add((r["candidate_sha256"], r["seed"]))
    return done


def append_row(row):
    OUTDIR.mkdir(parents=True, exist_ok=True)
    with open(ROWS_PATH, "a") as fh:
        fh.write(json.dumps(row) + "\n")


def dedupe_candidates(manifest_rows):
    """sha256 -> {sha256, spec, candidate_abs_path, manifest_rows: [...]}"""
    by_sha = {}
    for r in manifest_rows:
        if not r.get("candidate_recoverable"):
            continue
        p = r.get("candidate_abs_path")
        if not p or not Path(p).exists():
            continue
        sha = sha256_of(Path(p))
        entry = by_sha.setdefault(sha, {
            "candidate_sha256": sha, "candidate_abs_path": p, "spec": r["spec"],
            "manifest_rows": [],
        })
        entry["manifest_rows"].append(r)
    return by_sha


def run_one_candidate(sha, entry, num2mod, mod2path, done, log=print):
    p = Path(entry["candidate_abs_path"])
    num = entry["spec"]
    text = p.read_text(errors="replace")
    mod = module_name(text)
    if not mod:
        for seed in SEEDS:
            if (sha, seed) in done:
                continue
            row = base_row(sha, entry, seed, "skip_no_module_header")
            append_row(row)
            done.add((sha, seed))
        return

    workdir = WORKROOT / f"{sha[:12]}"
    tlc_mod, cfg_text, cfg_origin, cfg_err = prepare_candidate_workdir(
        num, mod, text, num2mod, mod2path, workdir)
    if tlc_mod is None:
        for seed in SEEDS:
            if (sha, seed) in done:
                continue
            row = base_row(sha, entry, seed, f"skip_{cfg_err}")
            append_row(row)
            done.add((sha, seed))
        shutil.rmtree(workdir, ignore_errors=True)
        return

    pol = POLICY.get(num, {})
    extra_flags = list(pol.get("tlc_flags", ()))
    jvm_flags = list(pol.get("jvm_flags", ()))

    for seed in SEEDS:
        if (sha, seed) in done:
            continue
        status, dt, ttv, out = run_tlc_simulate(tlc_mod, workdir, seed, extra_flags,
                                                jvm_flags, WALL_CAP_S)
        row = base_row(sha, entry, seed, status)
        row.update({
            "wall_s": round(dt, 2),
            "time_to_first_violation_s": ttv,
            "cfg_origin": cfg_origin,
            "tlc_mod": tlc_mod,
        })
        append_row(row)
        done.add((sha, seed))
        log(f"  spec {num} sha={sha[:10]} seed={seed}: {status} ({dt:.1f}s)"
            + (f" ttv={ttv}s" if ttv is not None else ""))
    shutil.rmtree(workdir, ignore_errors=True)


def base_row(sha, entry, seed, status):
    manifest_rows = entry["manifest_rows"]
    buckets = sorted(set(r["bucket"] for r in manifest_rows))
    classifications = sorted(set(r["tlc_classification"] for r in manifest_rows))
    tlc_s_values = [r["tlc_s"] for r in manifest_rows if r.get("tlc_s") is not None]
    known_broken = any(r.get("known_broken_elsewhere") for r in manifest_rows)
    return {
        "candidate_sha256": sha,
        "spec": entry["spec"],
        "candidate_abs_path": entry["candidate_abs_path"],
        "n_manifest_rows": len(manifest_rows),
        "manifest_buckets": buckets,
        "manifest_tlc_classifications": classifications,
        "manifest_tlc_s_values": tlc_s_values,
        "known_broken_elsewhere": known_broken,
        "seed": seed,
        "status": status,
        "timestamp": time.time(),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--smoke", action="store_true", help="run only 2 candidates end-to-end and exit")
    ap.add_argument("--jobs", type=int, default=1, help="parallel candidates (<=4, be polite)")
    args = ap.parse_args()

    manifest_rows = json.loads(MANIFEST.read_text())
    by_sha = dedupe_candidates(manifest_rows)
    print(f"[lewm-sim-baseline] {len(manifest_rows)} manifest rows, "
          f"{sum(1 for r in manifest_rows if r.get('candidate_recoverable'))} recoverable rows, "
          f"{len(by_sha)} unique candidate files")

    num2mod, mod2path = build_module_index(CORPUS)

    if args.smoke:
        # one known_broken_elsewhere timeout candidate, one slow_fail candidate
        timeout_entry = None
        slowfail_entry = None
        for sha, entry in by_sha.items():
            rows = entry["manifest_rows"]
            if timeout_entry is None and any(
                    r["bucket"] == "timeout" and r.get("known_broken_elsewhere") for r in rows):
                timeout_entry = (sha, entry)
            if slowfail_entry is None and any(r["bucket"] == "slow_fail" for r in rows):
                slowfail_entry = (sha, entry)
        picks = [x for x in (timeout_entry, slowfail_entry) if x]
        if len(picks) < 2:
            # fall back: just take first two available
            picks = list(by_sha.items())[:2]
        print(f"[smoke] running {len(picks)} candidates")
        done = load_existing_rows()
        for sha, entry in picks:
            print(f"[smoke] candidate spec={entry['spec']} sha={sha[:10]} "
                  f"buckets={sorted(set(r['bucket'] for r in entry['manifest_rows']))}")
            run_one_candidate(sha, entry, num2mod, mod2path, done)
        print("[smoke] done. Inspect results/runs/lewm-sim-baseline/rows.jsonl")
        return

    done = load_existing_rows()
    items = list(by_sha.items())
    n_total = len(items)
    for i, (sha, entry) in enumerate(items, 1):
        needed = [s for s in SEEDS if (sha, s) not in done]
        if not needed:
            print(f"[{i}/{n_total}] spec {entry['spec']} sha={sha[:10]}: already done, skip")
            continue
        print(f"[{i}/{n_total}] spec {entry['spec']} sha={sha[:10]}: running seeds {needed}")
        run_one_candidate(sha, entry, num2mod, mod2path, done)
    print("[lewm-sim-baseline] sweep complete")


if __name__ == "__main__":
    main()
