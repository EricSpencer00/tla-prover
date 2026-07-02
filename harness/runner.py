"""Stage-0 verification harness (PLAN.md W0.1).

One row per spec: {spec, method, sany, tlc, tlc_vacuity, tlaps, apalache,
budget_used, log_path}. Oracle method = the canonical corpus spec verbatim.
"""
import csv
import json
import re
import shutil
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
# Pinned current release (SANY 2.2/2020 in tla_benchmark's jar mis-parses TLAPS proofs)
TLA2TOOLS = REPO / "tools" / "tla2tools.jar"
# CM modules as plain .tla on the library path — the CM fat jar bundles classes
# compiled against a newer tla2tools (KSubsetValue) and breaks TLC if on the classpath.
CLASSPATH = str(TLA2TOOLS)
TLA_LIBRARY = ":".join(str(p) for p in [
    REPO / "tools" / "tlapm" / "lib" / "tlapm" / "stdlib",
    REPO / "tools" / "community-modules",
    REPO / "tools" / "extra-modules",
])

# Modules shipped inside tla2tools.jar; anything else EXTENDed must be a
# corpus sibling or it is a missing-module failure.
STANDARD_MODULES = {
    "Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags",
    "TLC", "TLCExt", "Randomization", "RealTime", "Toolbox", "Json",
}

_policy_file = REPO / "corpus" / "configs" / "policy.json"
POLICY = json.loads(_policy_file.read_text()) if _policy_file.exists() else {}

MODULE_RE = re.compile(r"^\s*-{4,}\s*MODULE\s+(\w+)\s*-{4,}", re.M)
EXTENDS_RE = re.compile(r"^\s*EXTENDS\s+(.+)$", re.M)
INSTANCE_RE = re.compile(r"\bINSTANCE\s+(\w+)", re.M)


def module_name(tla_text: str):
    m = MODULE_RE.search(tla_text)
    return m.group(1) if m else None


def build_module_index(corpus: Path):
    """spec_num -> module name, and module name -> tla path (for dep copying)."""
    num2mod, mod2path = {}, {}
    for f in sorted((corpus / "tla_files").glob("*.tla")):
        text = f.read_text(errors="replace")
        mod = module_name(text)
        if mod:
            num2mod[f.stem] = mod
            mod2path[mod] = f
    return num2mod, mod2path


def local_deps(tla_text: str, mod2path: dict):
    """Corpus modules this spec EXTENDS/INSTANCEs (transitive closure done by caller)."""
    deps = set()
    for m in EXTENDS_RE.finditer(tla_text):
        for name in re.split(r"[,\s]+", m.group(1).strip()):
            name = name.strip().rstrip(",")
            if name and name not in STANDARD_MODULES and name in mod2path:
                deps.add(name)
    for m in INSTANCE_RE.finditer(tla_text):
        if m.group(1) not in STANDARD_MODULES and m.group(1) in mod2path:
            deps.add(m.group(1))
    return deps


def run_cmd(cmd, cwd, timeout):
    t0 = time.time()
    try:
        p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr, time.time() - t0, False
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        return -1, out, time.time() - t0, True


def check_sany(tla_file: Path, workdir: Path, timeout: int):
    rc, out, dt, timed_out = run_cmd(
        ["java", f"-DTLA-Library={TLA_LIBRARY}", "-cp", CLASSPATH,
         "tla2sany.SANY", tla_file.name], workdir, timeout)
    if timed_out:
        return "timeout", out, dt
    ok = rc == 0 and "Fatal errors" not in out and "*** Errors:" not in out \
        and "Parse Error" not in out and "Semantic errors" not in out.replace("Semantic errors detected: 0", "")
    if not ok and re.search(r"Cannot find (?:the )?source file|module .* not found", out, re.I):
        return "fail_missing_module", out, dt
    return ("pass" if ok else "fail"), out, dt


def classify_tlc(rc: int, out: str, timed_out: bool):
    if timed_out:
        return "timeout"
    if "Model checking completed. No error has been found" in out or \
       ("No error has been found" in out and rc == 0):
        return "pass"
    if "Invariant" in out and "is violated" in out:
        return "fail_invariant"
    if "Deadlock reached" in out:
        return "fail_deadlock"
    if "Temporal properties were violated" in out:
        return "fail_liveness"
    if rc == 0:
        return "pass"
    return "error"


def vacuity_flags(cfg_text: str, out: str):
    """Pass-side vacuity checks (W0.4). Returns list of reasons; empty = non-vacuous."""
    reasons = []
    if not re.search(r"^\s*(INVARIANTS?|PROPERT(Y|IES))\b", cfg_text, re.M):
        reasons.append("no_invariant_or_property_in_cfg")
    m = re.search(r"(\d+) distinct states found", out)
    if m and int(m.group(1)) <= 1:
        reasons.append(f"only_{m.group(1)}_distinct_states")
    m2 = re.search(r"^(\d+) states generated", out, re.M)
    if m2 and int(m2.group(1)) == 0:
        reasons.append("zero_states_generated")
    return reasons


def check_tlc(mod: str, cfg_text: str, workdir: Path, timeout: int, extra_flags=()):
    rc, out, dt, timed_out = run_cmd(
        ["java", "-XX:+UseParallelGC", f"-DTLA-Library={TLA_LIBRARY}", "-cp", CLASSPATH, "tlc2.TLC",
         "-workers", "2", "-cleanup", "-metadir", str(workdir / "states"),
         *extra_flags, "-config", f"{mod}.cfg", f"{mod}.tla"], workdir, timeout)
    status = classify_tlc(rc, out, timed_out)
    vac = vacuity_flags(cfg_text, out) if status == "pass" else []
    return status, vac, out, dt


def eval_spec(num: str, corpus: Path, num2mod, mod2path, cfg_dirs, workroot: Path,
              logdir: Path, timeout: int, stages):
    """Evaluate one corpus spec (oracle method: verbatim canonical files)."""
    row = {"spec": num, "method": "oracle", "sany": None, "tlc": None,
           "tlc_vacuity": None, "tlaps": None, "apalache": None,
           "budget_used": {}, "log_path": str(logdir / f"{num}.log")}
    log_parts = []
    tla_src = corpus / "tla_files" / f"{num}.tla"
    if not tla_src.exists():
        row["sany"] = "no_tla_file"
        (logdir / f"{num}.log").write_text("no .tla file in corpus\n")
        return row
    text = tla_src.read_text(errors="replace")
    mod = num2mod.get(num)
    if not mod:
        row["sany"] = "no_module_header"
        (logdir / f"{num}.log").write_text("could not extract module name\n")
        return row

    workdir = workroot / num
    if workdir.exists():
        shutil.rmtree(workdir)
    workdir.mkdir(parents=True)
    (workdir / f"{mod}.tla").write_text(text)
    # copy corpus-local deps (transitive)
    seen, frontier = set(), local_deps(text, mod2path)
    while frontier:
        d = frontier.pop()
        if d in seen or d == mod:
            continue
        seen.add(d)
        dtext = mod2path[d].read_text(errors="replace")
        (workdir / f"{d}.tla").write_text(dtext)
        frontier |= (local_deps(dtext, mod2path) - seen)

    if "sany" in stages:
        st, out, dt = check_sany(workdir / f"{mod}.tla", workdir, timeout)
        row["sany"] = st
        row["budget_used"]["sany_s"] = round(dt, 1)
        log_parts.append(f"===== SANY ({st}) =====\n{out}")

    if "tlc" in stages and row["sany"] == "pass":
        cfg_text, cfg_origin = None, None
        for label, d in cfg_dirs:
            c = d / f"{num}.cfg"
            if c.exists():
                cfg_text, cfg_origin = c.read_text(errors="replace"), label
                break
        if cfg_text is None:
            row["tlc"] = "no_cfg"
        else:
            (workdir / f"{mod}.cfg").write_text(cfg_text)
            # per-spec policy (corpus/configs/policy.json): e.g. {"5": {"tlc_flags":
            # ["-deadlock"], "reason": "terminating algorithm; deadlock check n/a"}}
            pol = POLICY.get(num, {})
            tlc_mod = mod
            # optional MC-wrapper: {"wrapper": {"module": "MCFoo", "file": "corpus/configs/wrappers/MCFoo.tla"}}
            if "wrapper" in pol:
                w = pol["wrapper"]
                (workdir / f"{w['module']}.tla").write_text((REPO / w["file"]).read_text())
                tlc_mod = w["module"]
                (workdir / f"{tlc_mod}.cfg").write_text(cfg_text)
            st, vac, out, dt = check_tlc(tlc_mod, cfg_text, workdir, timeout,
                                         extra_flags=pol.get("tlc_flags", ()))
            if pol:
                row["policy"] = pol.get("reason", "custom flags")
            row["tlc"] = st
            row["tlc_vacuity"] = ("vacuous:" + ";".join(vac)) if vac else ("clean" if st == "pass" else None)
            row["cfg_origin"] = cfg_origin
            row["budget_used"]["tlc_s"] = round(dt, 1)
            log_parts.append(f"===== TLC ({st}, cfg={cfg_origin}) =====\n{out[-8000:]}")

    (logdir / f"{num}.log").write_text("\n".join(log_parts) or "no stages run\n")
    shutil.rmtree(workdir, ignore_errors=True)
    return row


def run_sweep(corpus: Path, run_id: str, stages, specs=None, timeout=120, jobs=6,
              extra_cfg_dir=None):
    rundir = REPO / "results" / "runs" / run_id
    logdir = rundir / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    workroot = Path("/tmp/prove-tla-work") / run_id
    num2mod, mod2path = build_module_index(corpus)
    # precedence: explicit override (replaces broken original text) > original > draft
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg")]
    if extra_cfg_dir:
        cfg_dirs.append(("draft", Path(extra_cfg_dir)))
    all_nums = sorted({p.stem for p in (corpus / "descriptions").glob("*.json")}, key=int)
    todo = [n for n in all_nums if not specs or n in specs]

    (rundir / "config.json").write_text(json.dumps({
        "run_id": run_id, "corpus": str(corpus), "stages": stages, "timeout_s": timeout,
        "jobs": jobs, "n_specs": len(todo), "extra_cfg_dir": str(extra_cfg_dir) if extra_cfg_dir else None,
        "tla2tools": str(TLA2TOOLS)}, indent=2))

    rows = []
    with ThreadPoolExecutor(max_workers=jobs) as ex, open(rundir / "rows.jsonl", "w") as fh:
        futs = {ex.submit(eval_spec, n, corpus, num2mod, mod2path, cfg_dirs,
                          workroot, logdir, timeout, stages): n for n in todo}
        for i, fut in enumerate(as_completed(futs), 1):
            row = fut.result()
            rows.append(row)
            fh.write(json.dumps(row) + "\n")
            fh.flush()
            if i % 25 == 0:
                print(f"[{i}/{len(todo)}] done")

    rows.sort(key=lambda r: int(r["spec"]))
    with open(rundir / "summary.csv", "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["spec", "method", "sany", "tlc", "tlc_vacuity",
                                           "cfg_origin", "tlaps", "apalache", "budget_used", "log_path"],
                           extrasaction="ignore")
        w.writeheader()
        for r in rows:
            r2 = dict(r)
            r2["budget_used"] = json.dumps(r["budget_used"])
            w.writerow(r2)

    tally = {}
    for r in rows:
        key = (r["sany"], r["tlc"], (r["tlc_vacuity"] or "").split(":")[0] or None)
        tally[key] = tally.get(key, 0) + 1
    print(f"\n=== {run_id}: {len(rows)} specs ===")
    for (s, t, v), c in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  sany={s:<22} tlc={t!s:<16} vac={v!s:<10} n={c}")
    shutil.rmtree(workroot, ignore_errors=True)
    return rows
