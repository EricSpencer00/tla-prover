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

from .runner import REPO, POLICY, build_module_index, local_deps, check_tlc, check_sany

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
    new_text, n = regex.subn(replacement, text)
    return (new_text, n) if n > 0 else (None, 0)


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
        tlc_st, vac, _, _ = check_tlc(mod, cfg_text, workdir, timeout,
                                       extra_flags=pol.get("tlc_flags", ()))
        killed = tlc_st != "pass"
        results.append({"mutation": label, "applied": True, "sany": sany_st,
                         "tlc": tlc_st, "killed": killed})
        shutil.rmtree(workdir, ignore_errors=True)
    shutil.rmtree(workroot, ignore_errors=True)

    attempted = [r for r in results if r.get("killed") is not None]
    killed_n = sum(1 for r in attempted if r["killed"])
    return {"spec": num, "module": mod, "mutants": results,
            "attempted": len(attempted), "killed": killed_n,
            "kill_rate": round(killed_n / len(attempted), 2) if attempted else None}


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
