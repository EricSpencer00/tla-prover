"""Stage-0 verification harness (PLAN.md W0.1).

One row per spec: {spec, method, sany, tlc, tlc_vacuity, tlaps, apalache,
budget_used, log_path}. Oracle method = the canonical corpus spec verbatim.
"""
import csv
import json
import os
import re
import signal
import shutil
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
# Pinned current release (SANY 2.2/2020 in tla_benchmark's jar mis-parses TLAPS proofs)
TLA2TOOLS = REPO / "tools" / "tla2tools.jar"
TLAPM = REPO / "tools" / "tlapm" / "bin" / "tlapm"
APALACHE = REPO / "tools" / "apalache-0.58.2" / "bin" / "apalache-mc"
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


def _library_module_names():
    """Module names already resolvable via -DTLA-Library (tlapm stdlib,
    community-modules, extra-modules). A handful of corpus specs ARE
    standalone copies of these same library modules under a benchmark
    number (e.g. spec 110 = an older, incomplete Functions.tla) -- without
    this exclusion, local_deps() would copy the corpus's stale edition into
    the workdir, where it shadows the correct library copy on the classpath
    (workdir files win over -DTLA-Library search) and breaks any OTHER spec
    that EXTENDS the real thing (e.g. spec 106 Util needs Functions'
    FoldFunction, which corpus spec 110's Functions.tla lacks)."""
    names = set()
    for d in (REPO / "tools" / "tlapm" / "lib" / "tlapm" / "stdlib",
              REPO / "tools" / "community-modules",
              REPO / "tools" / "extra-modules"):
        if not d.exists():
            continue
        for f in d.glob("*.tla"):
            mod = module_name(f.read_text(errors="replace"))
            if mod:
                names.add(mod)
    return names

_policy_file = REPO / "corpus" / "configs" / "policy.json"
POLICY = json.loads(_policy_file.read_text()) if _policy_file.exists() else {}
_populations_file = REPO / "corpus" / "configs" / "populations.json"
_populations = json.loads(_populations_file.read_text()) if _populations_file.exists() else {}
PROOF_MODULES = set(_populations.get("proof_module", []))
LIBRARIES = set(_populations.get("library", []))
# Amendment 3 (PENDING Eric): spec_num -> name of the invariant/property this spec
# is DESIGNED to violate (puzzle-solving specs where the violation trace is the
# solution; pedagogical negative-control specs demonstrating TLC catching a bug).
EXPECTED_VIOLATIONS = _populations.get("expected_violation", {})

MODULE_RE = re.compile(r"^\s*-{4,}\s*MODULE\s+(\w+)\s*-{4,}", re.M)
EXTENDS_RE = re.compile(r"^\s*EXTENDS\s+(.+)$", re.M)
INSTANCE_RE = re.compile(r"\bINSTANCE\s+(\w+)", re.M)


def module_name(tla_text: str):
    m = MODULE_RE.search(tla_text)
    return m.group(1) if m else None


LIBRARY_MODULES = _library_module_names()


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
            if name and name not in STANDARD_MODULES and name not in LIBRARY_MODULES \
                    and name in mod2path:
                deps.add(name)
    for m in INSTANCE_RE.finditer(tla_text):
        if m.group(1) not in STANDARD_MODULES and m.group(1) not in LIBRARY_MODULES \
                and m.group(1) in mod2path:
            deps.add(m.group(1))
    return deps


def run_cmd(cmd, cwd, timeout):
    # start_new_session so a timeout kills the whole process group, not just the
    # direct child: tlapm spawns Isabelle/z3 grandchildren that subprocess's own
    # timeout kill orphans -- observed E2.c arm 120b-a, 2026-07-07: leaked polyml
    # processes at 25% RAM each ground the host until the OS killed the sweep.
    t0 = time.time()
    p = subprocess.Popen(cmd, cwd=cwd, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True,
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=timeout)
        return p.returncode, out or "", time.time() - t0, False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            p.kill()
        out, _ = p.communicate()
        return -1, out or "", time.time() - t0, True


def _jtmpdir(workdir: Path):
    """Isolated -Djava.io.tmpdir per spec. SANY/TLC extract tla2tools.jar's bundled
    StandardModules (Integers.tla, TLC.tla, ...) to java.io.tmpdir on every run; the
    JVM default is the shared OS temp dir, so parallel workers (run_sweep's
    ThreadPoolExecutor) can race on the same extracted file -- one worker reads a
    StandardModule mid-write by another and SANY reports a spurious parse failure
    (observed: spec 62 flaked to sany=fail under -jobs 8, passed cleanly alone).
    workdir is already unique per spec, so a subdir under it isolates each run."""
    d = workdir / "jtmp"
    d.mkdir(exist_ok=True)
    return d


def check_sany(tla_file: Path, workdir: Path, timeout: int):
    rc, out, dt, timed_out = run_cmd(
        ["java", f"-Djava.io.tmpdir={_jtmpdir(workdir)}", f"-DTLA-Library={TLA_LIBRARY}",
         "-cp", CLASSPATH, "tla2sany.SANY", tla_file.name], workdir, timeout)
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


INVARIANT_NAMES_RE = re.compile(r"^\s*INVARIANTS?\b(.*)$", re.M)


def trivial_invariant_names(cfg_text: str, mod_text: str):
    """W0.4: static TRUE-equivalent-invariant detector. Follows each name listed
    under INVARIANT(S) in the cfg to its definition in the checked module's source
    and flags it if the body is syntactically just TRUE -- passes TLC on any spec,
    checks nothing. Best-effort (single-line/simple defs only, no macro expansion);
    misses are possible, false positives on a real TRUE body are not a concern."""
    names = []
    for m in INVARIANT_NAMES_RE.finditer(cfg_text):
        rest = m.group(1)
        for tok in re.split(r"[,\s]+", rest.strip()):
            if tok:
                names.append(tok)
    trivial = []
    for name in names:
        d = re.search(rf"^{re.escape(name)}\s*==\s*(.+?)\s*$", mod_text, re.M)
        if not d:
            continue
        body = d.group(1).split("\\*", 1)[0].strip()  # drop trailing inline comment
        if body == "TRUE":
            trivial.append(name)
    return trivial


VARIABLES_RE = re.compile(r"^\s*VARIABLES?\b", re.M)


def vacuity_flags(cfg_text: str, out: str, mod_text: str = ""):
    """Pass-side vacuity checks (W0.4). Returns list of reasons; empty = non-vacuous."""
    reasons = []
    # A module with no VARIABLES has nothing for INVARIANT/state-count checks to mean
    # -- these are pure-ASSUME "solve by constant evaluation" specs (e.g. spec 180's
    # Stones puzzle: TLC actually finds and PrintT's the solution via ASSUME, with 0
    # states generated by design, no VARIABLES declared at all). Flagging that as
    # vacuous would be wrong -- it did real, verified work; it just isn't a state
    # machine. Skip the state-count/no-invariant checks in that case; a trivial
    # invariant (checked below) still applies if the module DOES declare one.
    has_vars = bool(VARIABLES_RE.search(mod_text))
    if has_vars:
        if not re.search(r"^\s*(INVARIANTS?|PROPERT(Y|IES))\b", cfg_text, re.M):
            reasons.append("no_invariant_or_property_in_cfg")
        m = re.search(r"(\d+) distinct states found", out)
        if m and int(m.group(1)) <= 1:
            reasons.append(f"only_{m.group(1)}_distinct_states")
        m2 = re.search(r"^(\d+) states generated", out, re.M)
        if m2 and int(m2.group(1)) == 0:
            reasons.append("zero_states_generated")
    for name in trivial_invariant_names(cfg_text, mod_text):
        reasons.append(f"trivial_invariant:{name}")
    return reasons


def check_tlc(mod: str, cfg_text: str, workdir: Path, timeout: int, extra_flags=(), jvm_flags=()):
    rc, out, dt, timed_out = run_cmd(
        ["java", "-XX:+UseParallelGC", f"-Djava.io.tmpdir={_jtmpdir(workdir)}",
         f"-DTLA-Library={TLA_LIBRARY}", *jvm_flags, "-cp", CLASSPATH, "tlc2.TLC",
         "-workers", "2", "-cleanup", "-metadir", str(workdir / "states"),
         *extra_flags, "-config", f"{mod}.cfg", f"{mod}.tla"], workdir, timeout)
    status = classify_tlc(rc, out, timed_out)
    if status == "pass":
        mod_file = workdir / f"{mod}.tla"
        mod_text = mod_file.read_text(errors="replace") if mod_file.exists() else ""
        vac = vacuity_flags(cfg_text, out, mod_text)
    else:
        vac = []
    return status, vac, out, dt


def check_tlapm(tla_file: Path, workdir: Path, timeout=300):
    """Returns (status, proved, total, output, seconds). pass = all obligations proved."""
    # tlapm has no equivalent of SANY's -DTLA-Library env mechanism -- needs
    # explicit -I per directory, or EXTENDS of a community-module-only theorem
    # module (e.g. SequencesExtTheorems, spec 129) fails with "Unknown module"
    # even though SANY resolves it fine via TLA_LIBRARY.
    include_flags = []
    for p in TLA_LIBRARY.split(":"):
        include_flags += ["-I", p]
    rc, out, dt, timed_out = run_cmd(
        [str(TLAPM)] + include_flags + [tla_file.name], workdir, timeout)
    if timed_out:
        return "timeout", 0, 0, out, dt
    m = re.search(r"All (\d+) obligations? proved", out)
    if m:
        n = int(m.group(1))
        return "pass", n, n, out, dt
    mm = re.search(r"(\d+)/(\d+) obligations? proved", out)
    if mm:
        return "partial", int(mm.group(1)), int(mm.group(2)), out, dt
    mf = re.search(r"(\d+)/(\d+) obligations? failed", out)
    if mf:
        failed, total = int(mf.group(1)), int(mf.group(2))
        return "partial", total - failed, total, out, dt
    return "error", 0, 0, out, dt


def check_apalache(tla_file: Path, workdir: Path, inv=None, length=5, timeout=300):
    """Returns (status, output, seconds). pass = 'The outcome is: NoError'."""
    cmd = [str(APALACHE), "check", f"--length={length}"]
    if inv:
        cmd.append(f"--inv={inv}")
    cmd.append(tla_file.name)
    rc, out, dt, timed_out = run_cmd(cmd, workdir, timeout)
    if timed_out:
        return "timeout", out, dt
    if "The outcome is: NoError" in out:
        return "pass", out, dt
    if "The outcome is: Error" in out:
        return "fail_violation", out, dt
    return "error", out, dt


def _write_local_deps(text: str, mod: str, mod2path: dict, workdir: Path, seen: set):
    """Copy corpus-local deps (transitive) into workdir, patch-aware -- a dep can
    itself have a patch (e.g. spec 175/MC_spanning EXTENDS spec 176/spanning, whose
    TypeOK is the actual defect; the patch lives under 176's own spec number, not
    175's). Mutates and returns `seen` (the set of dep module names already copied)."""
    frontier = local_deps(text, mod2path) - seen
    while frontier:
        d = frontier.pop()
        if d in seen or d == mod:
            continue
        seen.add(d)
        dep_num = mod2path[d].stem
        dep_patch = REPO / "corpus" / "configs" / "patches" / f"{dep_num}.tla"
        dtext = dep_patch.read_text(errors="replace") if dep_patch.exists() \
            else mod2path[d].read_text(errors="replace")
        (workdir / f"{d}.tla").write_text(dtext)
        frontier |= (local_deps(dtext, mod2path) - seen)
    return seen


def _dispatch_criterion(num: str, mod: str, workdir: Path, cfg_dirs, timeout: int,
                        stages, row: dict, log_parts: list, num2mod, mod2path,
                        seen: set, override_cfg=None):
    """Shared SANY -> TLC/TLAPS dispatch tail (Amendment 1/3 population criterion):
    state_machine: SANY + non-vacuous TLC; library: SANY only; proof_module: SANY +
    all TLAPS obligations; expected_violation: SANY + named property violated ->
    normalized to tlc="pass_expected_violation". Mutates row/log_parts in place;
    also returns them for convenience. `seen` is the set of dep module names
    already copied into workdir (so a wrapper's own deps don't duplicate them).
    override_cfg, if given, is used in place of the reference cfg_dirs lookup."""
    if "sany" in stages:
        st, out, dt = check_sany(workdir / f"{mod}.tla", workdir, timeout)
        row["sany"] = st
        row["budget_used"]["sany_s"] = round(dt, 1)
        log_parts.append(f"===== SANY ({st}) =====\n{out}")

    if "tlc" in stages and row["sany"] == "pass":
        if override_cfg is not None:
            cfg_text, cfg_origin = override_cfg, "override_injected"
        else:
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
            # optional MC-wrapper, two forms:
            #  {"wrapper": {"module": "MCFoo", "file": "corpus/configs/wrappers/MCFoo.tla"}}
            #    -- vendored external file (upstream tla-examples or hand-authored)
            #  {"wrapper": {"corpus_spec": "13"}}
            #    -- the wrapper IS another corpus spec (e.g. spec 11's original .cfg
            #    was written for spec 13's MCBakery, EXTENDS Bakery=spec 11 itself;
            #    both are already in the corpus as separate benchmark entries).
            #    Resolved dynamically via num2mod/mod2path so there is no vendored
            #    copy to go stale; respects corpus/configs/patches/ like any other
            #    corpus-local dependency.
            if "wrapper" in pol:
                w = pol["wrapper"]
                if "corpus_spec" in w:
                    w_num = w["corpus_spec"]
                    w_mod = num2mod[w_num]
                    w_path = mod2path[w_mod]
                    w_patch = REPO / "corpus" / "configs" / "patches" / f"{w_num}.tla"
                    w_text = w_patch.read_text(errors="replace") if w_patch.exists() \
                        else w_path.read_text(errors="replace")
                    (workdir / f"{w_mod}.tla").write_text(w_text)
                    for d in (local_deps(w_text, mod2path) - seen - {mod}):
                        seen.add(d)
                        dtext = mod2path[d].read_text(errors="replace")
                        (workdir / f"{d}.tla").write_text(dtext)
                    tlc_mod = w_mod
                else:
                    w_text = (REPO / w["file"]).read_text()
                    (workdir / f"{w['module']}.tla").write_text(w_text)
                    # the vendored wrapper can itself need a corpus-local module the
                    # top-level spec doesn't transitively EXTEND (e.g. spec 47's own
                    # module is DiskSynod; MC_HDiskSynod EXTENDS HDiskSynod, one level
                    # up -- HDiskSynod is never pulled in by spec 47's own local_deps).
                    for d in (local_deps(w_text, mod2path) - seen - {mod}):
                        seen.add(d)
                        dtext = mod2path[d].read_text(errors="replace")
                        (workdir / f"{d}.tla").write_text(dtext)
                    tlc_mod = w["module"]
                (workdir / f"{tlc_mod}.cfg").write_text(cfg_text)
            # per-spec timeout override (corpus/configs/TIMEOUT_POLICY.md): only
            # raised for specs individually confirmed to converge given more time,
            # never used to paper over a genuinely large/non-converging state space.
            spec_timeout = max(timeout, pol.get("timeout", 0))
            st, vac, out, dt = check_tlc(tlc_mod, cfg_text, workdir, spec_timeout,
                                         extra_flags=pol.get("tlc_flags", ()),
                                         jvm_flags=pol.get("jvm_flags", ()))
            expected_prop = EXPECTED_VIOLATIONS.get(num)
            if expected_prop and st in ("fail_invariant", "fail_liveness") and \
                    re.search(rf"(?:Invariant|Property)\s+{re.escape(expected_prop)}\s+is violated", out):
                st = "pass_expected_violation"
                vac = []
                row["expected_violation"] = expected_prop
            if pol:
                row["policy"] = pol.get("reason", "custom flags")
            row["tlc"] = st
            row["tlc_vacuity"] = ("vacuous:" + ";".join(vac)) if vac else \
                ("clean" if st in ("pass", "pass_expected_violation") else None)
            row["cfg_origin"] = cfg_origin
            row["budget_used"]["tlc_s"] = round(dt, 1)
            # Keep head+tail, not just tail: long counterexample traces (e.g. a
            # 117-state puzzle solution) can push the actual "Error: ... is
            # violated" line out of a tail-only truncation (found while
            # root-causing specs 4/173 -- the classification was still correct,
            # since check_tlc searches the full untruncated text, but the saved
            # evidence log was missing the line a human would look for first).
            body = out if len(out) <= 16000 else (out[:4000] + "\n...[truncated]...\n" + out[-12000:])
            log_parts.append(f"===== TLC ({st}, cfg={cfg_origin}) =====\n{body}")

    if "tlaps" in stages and row["sany"] == "pass" and num in PROOF_MODULES:
        st, proved, total, out, dt = check_tlapm(workdir / f"{mod}.tla", workdir, timeout=timeout * 3)
        row["tlaps"] = st
        row["tlaps_obligations"] = f"{proved}/{total}"
        row["budget_used"]["tlaps_s"] = round(dt, 1)
        log_parts.append(f"===== TLAPS ({st}, {proved}/{total} obligations) =====\n{out[-8000:]}")

    return row, log_parts


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
    # documented corpus-defect repair (Amendment 1: "repaired from upstream sources";
    # for specs where the defect is upstream too, corpus/configs/PATCHES.md records
    # the minimal hand-authored fix): full-module override, same module name.
    patch_file = REPO / "corpus" / "configs" / "patches" / f"{num}.tla"
    text = patch_file.read_text(errors="replace") if patch_file.exists() else tla_src.read_text(errors="replace")
    if patch_file.exists():
        row["source_origin"] = "patched"
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
    seen = _write_local_deps(text, mod, mod2path, workdir, set())

    row, log_parts = _dispatch_criterion(num, mod, workdir, cfg_dirs, timeout, stages,
                                         row, log_parts, num2mod, mod2path, seen)

    (logdir / f"{num}.log").write_text("\n".join(log_parts) or "no stages run\n")
    shutil.rmtree(workdir, ignore_errors=True)
    return row


def eval_module_text(num: str, module_text: str, corpus: Path, num2mod, mod2path,
                     cfg_dirs, workroot: Path, logdir: Path, timeout: int, stages,
                     override_cfg=None, log_name=None):
    """Score an arbitrary module string (e.g. a model-generated or model-repaired
    candidate, cf. harness.gen_eval.extract_module) for corpus spec `num` under
    exactly the same criterion machinery as eval_spec: dependency resolution
    (with patches), wrapper resolution, policy.json handling, and the population
    criterion (state_machine / library / proof_module / expected_violation).
    TLC stays SERIAL (call this with jobs=1 at the sweep level) and the 120s
    timeout budget is the caller's `timeout` arg, same as eval_spec.

    The injected module's declared name (parsed from its own `---- MODULE X ----`
    header, NOT assumed to be num2mod[num]) is what it is written to disk as --
    a candidate that mis-names itself is a real scoring outcome (sany=no_module_header),
    not something this function should silently correct.

    override_cfg, if given, replaces the reference cfg_dirs lookup for spec num
    (e.g. to score under a draft/candidate .cfg instead of the corpus original).

    log_name, if given, overrides the log filename (default f"{num}.log") --
    callers that score multiple candidates for the same spec (e.g. gen_eval's
    per-sample scoring) pass a distinct log_name per candidate so logs don't
    overwrite each other.
    """
    log_file = logdir / (log_name or f"{num}.log")
    row = {"spec": num, "method": "injected", "sany": None, "tlc": None,
           "tlc_vacuity": None, "tlaps": None, "apalache": None,
           "budget_used": {}, "log_path": str(log_file)}
    log_parts = []
    mod = module_name(module_text)
    if not mod:
        row["sany"] = "no_module_header"
        log_file.write_text("could not extract module name from injected text\n")
        return row

    workdir = workroot / num
    if workdir.exists():
        shutil.rmtree(workdir)
    workdir.mkdir(parents=True)
    (workdir / f"{mod}.tla").write_text(module_text)
    seen = _write_local_deps(module_text, mod, mod2path, workdir, set())

    row, log_parts = _dispatch_criterion(num, mod, workdir, cfg_dirs, timeout, stages,
                                         row, log_parts, num2mod, mod2path, seen,
                                         override_cfg=override_cfg)

    log_file.write_text("\n".join(log_parts) or "no stages run\n")
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
                                           "cfg_origin", "tlaps", "tlaps_obligations", "apalache",
                                           "budget_used", "log_path"],
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
        print(f"  sany={s!s:<22} tlc={t!s:<16} vac={v!s:<10} n={c}")
    shutil.rmtree(workroot, ignore_errors=True)
    return rows
