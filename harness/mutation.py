"""Mutation kill-rate (W0.4 / ROADMAP.md Stage 0 "Diamond tier" precedent).

SCOPE, stated plainly: this is a small, explicit set of syntactic operator swaps
applied to the WHOLE checked module at once, not single-point localized mutation
(a full SpecGen-style tool mutates one operator occurrence per mutant and tracks
each independently). That is real future work, not done here. What this gives you:
for each mutation operator, one mutant per spec, and whether the spec's own
invariant/property catches the injected change.

Run: python3 -m harness.mutation --specs <comma-list> [--corpus PATH] [--timeout N]
Reuses eval_spec's workdir/dependency-copy machinery from harness.runner so the
mutant sees exactly the same corpus-local deps + cfg the real oracle run would.

A mutant is "killed" if TLC (same cfg/invariant as the unmutated spec) now reports
anything other than "pass" -- the injected change was semantically caught. Mutants
that fail to even produce a valid mutation (operator not present in the module) are
skipped, not counted as survived. kill_rate = killed / attempted, reported per spec
-- informational (spec-strength signal, antidote to vacuous 100% claims per
ROADMAP.md), not folded into the spec's own pass/fail.
"""
import argparse
import json
import re
import shutil
from pathlib import Path

from .runner import (REPO, POLICY, build_module_index, local_deps, check_tlc,
                     check_sany, module_name)

DEFAULT_CORPUS = "/Users/eric/GitHub/tla_benchmark/data"

# (label, regex, replacement) -- applied with re.sub across the whole module body
# (EXTENDS/CONSTANT/VARIABLE lines excluded by only touching action bodies is NOT
# attempted here -- whole-module swap, see module docstring).
MUTATIONS = [
    # /\ and \/ are unambiguously the boolean connectives everywhere in TLA+ --
    # safe to swap textually.
    ("and_to_or", re.compile(r"/\\"), "\\/"),
    ("plus_to_minus", re.compile(r"(?<=\d|\s|\))\s\+\s(?=\d|\w)"), " - "),
    # \in is unambiguously set-membership everywhere in TLA+ (no other token
    # contains it as a substring -- \notin is the only lookalike and its
    # presence would just match "notin" have zero overlap with "\in" since
    # "\notin" does not contain the substring "\in" -- the token starts
    # "\not" not "\in"). Swapping to \notin negates the membership test,
    # which for MC-stub/library modules (whose entire body is often just
    # ASSUME/EXTENDS/one-liner operator defs with no /\ or "n + m") is
    # frequently the ONLY available mutation site -- added specifically to
    # close the NoCandidateMutation gap on holdout specs 13, 14, 105, 106,
    # 132, 133, 135, 181 (see harness/gen_eval.py corrupt()).
    ("in_to_notin", re.compile(r"\\in\b"), "\\notin"),
    # \cup (set union) and \cap (set intersection) are likewise unambiguous
    # infix set operators; swapping preserves arity/fixity and SANY parses
    # either symbol identically, only the runtime semantics change. Kept as
    # a second independent site so specs with \cup but no \in-adjacent
    # mutation risk (none currently in the frozen holdout, but future specs)
    # aren't stranded on \in alone.
    ("cup_to_cap", re.compile(r"\\cup\b"), "\\cap"),
]

# Tried and DROPPED after testing on real corpus specs (see corpus/configs/MUTATION.md):
# eq_to_neq ("=" -> "#") and lt_to_le ("<" -> "<=") both reliably break real specs
# even after excluding "==", "<=", ">=", ":=" -- "=" is ALSO the required token in
# EXCEPT's "![i] = v" clause syntax (not a boolean comparison there) and inside "=>"
# (implication), and regex has no way to tell those apart from a real "x = y"
# comparison without actually parsing the expression. Whole-file regex mutation
# cannot safely cover relational operators for arbitrary TLA+; would need a real
# parser (tree-sitter-tlaplus or SANY's own AST) to do this correctly -- not
# attempted here.


def apply_mutation(text: str, regex, replacement: str):
    # Replacement is passed through a lambda, not the raw string, so re never
    # parses it as a backreference template -- replacements like "\cap"/"\notin"
    # contain backslash-letter sequences (\c, \n) that Python's re engine (as of
    # 3.12+, hardened in 3.14) rejects as an invalid escape in template syntax
    # even though nothing here is a real \g<n> group reference.
    new_text, n = regex.subn(lambda m: replacement, text)
    return (new_text, n) if n > 0 else (None, 0)


# TLC prints the first violated invariant/property by name, e.g.
# "Invariant Safety is violated." / "Property Liveness is violated.".
_VIOLATION_RE = re.compile(r"(?:Invariant|Property)\s+(\w+)\s+is violated")
# TypeOK-style invariants only assert well-typedness; a mutant that trips only
# one of these proves nothing about the spec's real safety property.
_TYPE_NAME_RE = re.compile(r"type", re.IGNORECASE)


def classify_mutation_catch(tlc_out: str):
    """#4 catch-attribution: which invariant/property did the mutant trip, and
    was it a REAL safety catch? Returns {"violated": name|None, "is_safety_catch":
    bool}. A catch counts as a safety catch only when a NON-TypeOK-style property
    was violated -- a mutant that only breaks TypeOK is a weak/gameable signal
    (a strong TypeOK + vacuous safety invariant would otherwise score well while
    checking nothing)."""
    m = _VIOLATION_RE.search(tlc_out or "")
    if not m:
        return {"violated": None, "is_safety_catch": False}
    name = m.group(1)
    return {"violated": name, "is_safety_catch": not bool(_TYPE_NAME_RE.search(name))}


def mutant_verdict(tlc_status: str, tlc_out: str) -> dict:
    """FIX 1: decide a mutant's verdict from the TLC (status, output), discounting
    crash-kills. Returns {killed, safety_killed, violated, note}.

    Old code used `killed = tlc_st != "pass"`, which counted a mutant that merely
    made TLC *crash* (evaluation error, "did not specify the initial state
    predicate", runtime parse error) as a kill with violated=None -- a gameable
    non-catch. On the full 949 sweep that inflated kill_rate to 96% junk (667 of
    695 kills had violated=None). New semantics:
      - TLC pass                          -> killed=False  (mutant survived)
      - invariant/property violation      -> killed=True, safety_killed iff NON-TypeOK
      - genuine deadlock                  -> killed=True, safety_killed=False
                                             (behavioral catch, not a safety invariant)
      - crash/error/timeout, no violation -> killed=None, note="crash_not_applicable"
        (a broken mutant, excluded from `attempted` -- same treatment as a
        mutant that fails to even parse under SANY).
    """
    if tlc_status == "pass":
        return {"killed": False, "safety_killed": False, "violated": None, "note": None}
    catch = classify_mutation_catch(tlc_out)
    if catch["violated"] is not None:
        return {"killed": True, "safety_killed": catch["is_safety_catch"],
                "violated": catch["violated"], "note": None}
    if tlc_status == "fail_deadlock" or "Deadlock reached" in (tlc_out or ""):
        return {"killed": True, "safety_killed": False, "violated": None, "note": "deadlock"}
    # crash/error/timeout with no violation and no deadlock: not a real catch.
    return {"killed": None, "safety_killed": False, "violated": None,
            "note": "crash_not_applicable"}


def summarize_mutants(results):
    """#4: aggregate per-mutant results into catch metrics. `attempted` = mutants
    that ran to a kill/survive verdict (killed is not None; parse-failed or
    inapplicable mutants excluded). Reports BOTH the raw kill_rate (any TLC
    failure -- gameable) and the safety_catch_rate (only NON-TypeOK property
    violations). quality_gold should gate on safety_catch_rate."""
    attempted = [r for r in results if r.get("killed") is not None]
    n = len(attempted)
    killed_n = sum(1 for r in attempted if r["killed"])
    safety_n = sum(1 for r in attempted if r.get("safety_killed"))
    return {
        "attempted": n,
        "killed": killed_n,
        "kill_rate": round(killed_n / n, 2) if n else None,
        "safety_killed": safety_n,
        "safety_catch_rate": round(safety_n / n, 2) if n else None,
    }


def run_mutation_for_spec(num: str, corpus: Path, cfg_dirs, timeout: int):
    num2mod, mod2path = build_module_index(corpus)
    mod = num2mod.get(num)
    if not mod:
        return {"spec": num, "error": "no_module"}
    tla_src = corpus / "tla_files" / f"{num}.tla"
    orig_text = tla_src.read_text(errors="replace")

    cfg_text = None
    for _, d in cfg_dirs:
        c = d / f"{num}.cfg"
        if c.exists():
            cfg_text = c.read_text(errors="replace")
            break
    if cfg_text is None:
        return {"spec": num, "error": "no_cfg"}

    workroot = Path("/tmp/prove-tla-mutation") / num
    results = []
    for label, regex, repl in MUTATIONS:
        mutant_text, n = apply_mutation(orig_text, regex, repl)
        if mutant_text is None:
            results.append({"mutation": label, "applied": False})
            continue
        workdir = workroot / label
        if workdir.exists():
            shutil.rmtree(workdir)
        workdir.mkdir(parents=True)
        (workdir / f"{mod}.tla").write_text(mutant_text)
        seen, frontier = set(), local_deps(orig_text, mod2path)
        while frontier:
            d = frontier.pop()
            if d in seen or d == mod:
                continue
            seen.add(d)
            dtext = mod2path[d].read_text(errors="replace")
            (workdir / f"{d}.tla").write_text(dtext)
            frontier |= (local_deps(dtext, mod2path) - seen)
        sany_st, _, _ = check_sany(workdir / f"{mod}.tla", workdir, timeout)
        if sany_st != "pass":
            results.append({"mutation": label, "applied": True, "sany": sany_st,
                             "killed": None, "note": "mutant fails to parse, not counted"})
            shutil.rmtree(workdir, ignore_errors=True)
            continue
        (workdir / f"{mod}.cfg").write_text(cfg_text)
        pol = POLICY.get(num, {})
        tlc_st, vac, tlc_out, _ = check_tlc(mod, cfg_text, workdir, timeout,
                                       extra_flags=pol.get("tlc_flags", ()))
        v = mutant_verdict(tlc_st, tlc_out)
        results.append({"mutation": label, "applied": True, "sany": sany_st,
                         "tlc": tlc_st, "killed": v["killed"],
                         "violated": v["violated"],
                         "safety_killed": v["safety_killed"], "note": v["note"]})
        shutil.rmtree(workdir, ignore_errors=True)
    shutil.rmtree(workroot, ignore_errors=True)

    return {"spec": num, "module": mod, "mutants": results,
            **summarize_mutants(results)}


def _local_module_index(src_dir: Path) -> dict:
    """module name -> .tla path for every module file in the spec's own source
    directory (the raw scrape tree co-locates a spec with its local deps). This
    is the FIX-2 dep universe: we mutate only these local siblings, never
    standard/community library modules that aren't present as local files."""
    idx = {}
    for f in sorted(src_dir.glob("*.tla")):
        m = module_name(f.read_text(errors="replace"))
        if m:
            idx[m] = f
    return idx


def _local_dep_closure(top_text: str, mod2path: dict, top_module: str) -> set:
    """Transitive closure of the LOCAL modules `top` EXTENDS/INSTANCEs (only
    those resolvable in mod2path -- i.e. present as sibling files)."""
    seen, frontier = set(), local_deps(top_text, mod2path)
    while frontier:
        d = frontier.pop()
        if d in seen or d == top_module:
            continue
        seen.add(d)
        frontier |= (local_deps(mod2path[d].read_text(errors="replace"), mod2path) - seen)
    return seen


def run_mutation_on_module(tla_path: Path, cfg_text: str, module: str, timeout: int) -> dict:
    """W1 adequacy battery entry point (design doc Workstream 1): the deterministic
    MUTATIONS battery keyed to an arbitrary FILE PATH (tier1/tier3 scraped specs).

    FIX 2 -- mutate the EXTENDS'd parent, not just the harness. 210/779 specs on
    the full sweep had ZERO mutation sites because they are thin *_MC / Test1
    harnesses whose real action/next-state logic lives in the module they EXTEND
    (Paxos_MC -> PaxosPlusCal, Test1 -> Percolator, ...). We now enumerate
    mutation TARGETS = {top module} + its transitive LOCAL dependency modules
    (sibling .tla files resolvable in the spec's own source dir; standard/
    community library modules are excluded because they aren't local files). For
    each (target module, mutation label) we produce one mutant that mutates only
    that target, keep every other module verbatim, and run SANY+TLC against the
    TOP spec+cfg so the top-level invariant is what must catch the change.
    Everything aggregates into one summarize_mutants over all mutants."""
    src_dir = tla_path.parent
    mod2path = _local_module_index(src_dir)
    top_text = tla_path.read_text(errors="replace")
    # top module's own file may not be named <module>.tla in the raw tree; make
    # sure the index maps the top module to the file we were handed.
    mod2path[module] = tla_path
    deps = _local_dep_closure(top_text, mod2path, module)
    # Non-module sibling files (cfgs of deps, data files) copied verbatim so the
    # mutant workdir matches the real run environment.
    aux_files = [p for p in src_dir.iterdir()
                 if p.is_file() and p.suffix != ".tla" and p.name != f"{module}.cfg"]

    # Mutation targets, top module first (stable ordering for reproducibility).
    targets = [module] + sorted(deps)
    workroot = Path("/tmp/prove-tla-mutation-adequacy") / module
    results = []
    for target in targets:
        target_text = mod2path[target].read_text(errors="replace")
        for label, regex, repl in MUTATIONS:
            mutant_text, _ = apply_mutation(target_text, regex, repl)
            row = {"mutation": label, "target": target}
            if mutant_text is None:
                row["applied"] = False
                results.append(row)
                continue
            workdir = workroot / target / label
            if workdir.exists():
                shutil.rmtree(workdir)
            workdir.mkdir(parents=True)
            # write every local module; the target carries the mutation, the rest
            # are verbatim.
            for m, p in mod2path.items():
                text = mutant_text if m == target else p.read_text(errors="replace")
                (workdir / f"{m}.tla").write_text(text)
            for aux in aux_files:
                shutil.copy2(aux, workdir / aux.name)
            sany_st, _, _ = check_sany(workdir / f"{module}.tla", workdir, timeout)
            if sany_st != "pass":
                row.update(applied=True, sany=sany_st, killed=None,
                           note="mutant fails to parse, not counted")
                results.append(row)
                shutil.rmtree(workdir, ignore_errors=True)
                continue
            (workdir / f"{module}.cfg").write_text(cfg_text)
            tlc_st, _, tlc_out, _ = check_tlc(module, cfg_text, workdir, timeout)
            v = mutant_verdict(tlc_st, tlc_out)
            row.update(applied=True, sany=sany_st, tlc=tlc_st, killed=v["killed"],
                       violated=v["violated"], safety_killed=v["safety_killed"],
                       note=v["note"])
            results.append(row)
            shutil.rmtree(workdir, ignore_errors=True)
    shutil.rmtree(workroot, ignore_errors=True)

    return {"module": module, "mutants": results, **summarize_mutants(results)}


def main():
    ap = argparse.ArgumentParser(prog="harness.mutation")
    ap.add_argument("--corpus", default=DEFAULT_CORPUS)
    ap.add_argument("--specs", required=True)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--extra-cfg-dir", default=None)
    a = ap.parse_args()
    corpus = Path(a.corpus)
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg")]
    if a.extra_cfg_dir:
        cfg_dirs.append(("draft", Path(a.extra_cfg_dir)))
    for num in a.specs.split(","):
        r = run_mutation_for_spec(num, corpus, cfg_dirs, a.timeout)
        print(json.dumps(r))


# Guard (was a bare main() call): harness.repair imports MUTATIONS/apply_mutation
# from this module; an unguarded main() would run argparse at import time.
# `python3 -m harness.mutation` still works -- -m executes the module as __main__.
if __name__ == "__main__":
    main()
