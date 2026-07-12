"""Tests for harness.mutation catch-attribution (#4 fix).

A mutant that only breaks a TypeOK-style invariant must NOT count as a real
"catch" -- otherwise a spec with a strong TypeOK and a vacuous safety invariant
scores well while checking nothing (the exact failure this project exists to
detect). Only a violation of a non-TypeOK safety property/invariant is a real
catch.
"""
from pathlib import Path

from harness.mutation import (classify_mutation_catch, summarize_mutants,
                               run_mutation_on_module, mutant_verdict, MUTATIONS)


# --- FIX 1: crash-kills are not catches --------------------------------------
#
# Old semantics `killed = tlc_st != "pass"` counted a mutant that made TLC
# *error/crash* (evaluation error, "did not specify the initial state
# predicate", runtime parse error) as killed=True -- a gameable non-catch that
# inflated kill_rate to 96% junk on the full sweep (667 of 695 kills had
# violated=None). New semantics: only an invariant/property violation or a
# genuine deadlock is a kill; a bare crash is not-applicable (killed=None).

def test_verdict_pass_is_survived_not_killed():
    v = mutant_verdict("pass", "Model checking completed. No error has been found.")
    assert v["killed"] is False
    assert v["safety_killed"] is False
    assert v["violated"] is None


def test_verdict_invariant_violation_is_safety_kill():
    v = mutant_verdict("fail_invariant", "Error: Invariant Safety is violated.")
    assert v["killed"] is True
    assert v["safety_killed"] is True
    assert v["violated"] == "Safety"


def test_verdict_typeok_violation_killed_but_not_safety():
    v = mutant_verdict("fail_invariant", "Error: Invariant TypeOK is violated.")
    assert v["killed"] is True
    assert v["safety_killed"] is False
    assert v["violated"] == "TypeOK"


def test_verdict_deadlock_is_killed_but_not_safety_kill():
    # Behavioral catch, not a safety-invariant catch: counts as killed (the spec
    # noticed the mutant broke reachability) but NOT safety_killed.
    v = mutant_verdict("fail_deadlock", "Error: Deadlock reached.")
    assert v["killed"] is True
    assert v["safety_killed"] is False
    assert v["violated"] is None


def test_verdict_liveness_violation_is_safety_kill():
    v = mutant_verdict("fail_liveness",
                       "Error: Temporal properties were violated.\nError: Property Liveness is violated.")
    assert v["killed"] is True
    assert v["safety_killed"] is True
    assert v["violated"] == "Liveness"


def test_verdict_crash_with_no_violation_is_not_applicable():
    # TLC errored (e.g. evaluation error) with no violation/deadlock line: this
    # is a broken mutant, not a caught one -> killed=None, excluded from attempted.
    v = mutant_verdict("error", "Error: In evaluation, the identifier x is undefined.")
    assert v["killed"] is None
    assert v["note"] == "crash_not_applicable"


def test_verdict_initial_state_crash_is_not_applicable():
    v = mutant_verdict("error",
                       "Error: The behavior specification did not specify the initial state predicate.")
    assert v["killed"] is None
    assert v["note"] == "crash_not_applicable"


def test_verdict_timeout_is_not_applicable():
    v = mutant_verdict("timeout", "")
    assert v["killed"] is None


def test_summarize_excludes_crash_not_applicable_from_attempted():
    results = [
        {"mutation": "a", "applied": True, "killed": True, "safety_killed": True},
        {"mutation": "b", "applied": True, "killed": False, "safety_killed": False},  # survived
        {"mutation": "c", "applied": True, "killed": None, "note": "crash_not_applicable"},
    ]
    s = summarize_mutants(results)
    assert s["attempted"] == 2      # a, b only -- crash excluded
    assert s["killed"] == 1
    assert s["safety_catch_rate"] == round(1 / 2, 2)

# Real safety invariant (NonNegative: x >= 0). Dec's guard "x \in {0}" (only
# decrement at 0) is a stand-in bound check that in_to_notin flips to \notin
# {0} (decrement whenever x # 0), letting TLC actually walk x below 0 and trip
# NonNegative -- a genuine safety catch, not just a parse/deadlock error.
SAFETY_SPEC = """---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Dec == x \\in {0} \\/ x' = x - 1
Next == Dec
Spec == Init /\\ [][Next]_x
NonNegative == x >= 0
====
"""
SAFETY_CFG = """INIT Init
NEXT Next
INVARIANT NonNegative
"""

# Trivial spec: invariant is syntactically TRUE, no mutation should ever catch
# anything real (kept minimal -- no real safety property to violate regardless
# of which mutation textually applies).
TRIVIAL_SPEC = """---- MODULE Trivial ----
VARIABLE x
Init == x = 0
Next == x' = x
Spec == Init /\\ [][Next]_x
AlwaysTrue == TRUE
====
"""
TRIVIAL_CFG = """INIT Init
NEXT Next
INVARIANT AlwaysTrue
"""


def _write_spec(tmp_path: Path, name: str, spec_text: str, cfg_text: str) -> Path:
    d = tmp_path / name
    d.mkdir()
    tla = d / f"{name}.tla"
    tla.write_text(spec_text)
    (d / f"{name}.cfg").write_text(cfg_text)
    return tla


def test_run_mutation_on_module_catches_real_safety_violation(tmp_path):
    tla_path = _write_spec(tmp_path, "Counter", SAFETY_SPEC, SAFETY_CFG)
    r = run_mutation_on_module(tla_path, SAFETY_CFG, "Counter", timeout=30)
    assert r["safety_catch_rate"] is not None
    assert r["safety_catch_rate"] > 0
    assert "mutants" in r
    assert len(r["mutants"]) == len(MUTATIONS)


def test_run_mutation_on_module_trivial_invariant_never_caught(tmp_path):
    tla_path = _write_spec(tmp_path, "Trivial", TRIVIAL_SPEC, TRIVIAL_CFG)
    r = run_mutation_on_module(tla_path, TRIVIAL_CFG, "Trivial", timeout=30)
    assert r["safety_catch_rate"] in (None, 0, 0.0)


# --- FIX 2: mutate the EXTENDS'd parent, not just the harness -----------------
#
# Real logic (Dec's mutable "x \in {0}" guard) lives in the parent Base module;
# the harness only EXTENDS it and adds the invariant. Before FIX 2 the battery
# mutated only the harness (no sites -> attempted=0 -> safety_catch_rate null).
# After FIX 2 the parent is a mutation target, so a site exists AND the
# harness's NonNegative invariant catches the loosened guard.
_PARENT_BASE = """---- MODULE Base ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Dec == x \\in {0} \\/ x' = x - 1
Inc == x' = x + 1
Next == Dec \\/ Inc
====
"""
_HARNESS_MC = """---- MODULE HarnessMC ----
EXTENDS Base
Spec == Init /\\ [][Next]_x
NonNegative == x >= 0
====
"""
_HARNESS_CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"


def test_run_mutation_on_module_mutates_extends_parent(tmp_path):
    d = tmp_path / "proj"
    d.mkdir()
    (d / "Base.tla").write_text(_PARENT_BASE)
    (d / "HarnessMC.tla").write_text(_HARNESS_MC)
    (d / "HarnessMC.cfg").write_text(_HARNESS_CFG)

    r = run_mutation_on_module(d / "HarnessMC.tla", _HARNESS_CFG, "HarnessMC", timeout=30)

    # a mutation site now exists on the Base parent
    applied = [m for m in r["mutants"] if m.get("applied")]
    assert any(m["target"] == "Base" for m in applied), "parent Base was never mutated"
    # and the harness invariant caught at least one loosened-guard mutant
    assert r["safety_catch_rate"] is not None
    assert r["safety_catch_rate"] > 0
    assert any(m.get("safety_killed") for m in r["mutants"])


def test_safety_invariant_violation_is_a_real_catch():
    out = "Error: Invariant Safety is violated.\nThe behavior up to this point is:"
    r = classify_mutation_catch(out)
    assert r["violated"] == "Safety"
    assert r["is_safety_catch"] is True


def test_typeok_only_violation_is_not_a_real_catch():
    out = "Error: Invariant TypeOK is violated.\nThe behavior up to this point is:"
    r = classify_mutation_catch(out)
    assert r["violated"] == "TypeOK"
    assert r["is_safety_catch"] is False


def test_temporal_property_violation_is_a_real_catch():
    out = "Error: Temporal properties were violated.\nError: Property Liveness is violated."
    r = classify_mutation_catch(out)
    assert r["violated"] == "Liveness"
    assert r["is_safety_catch"] is True


def test_type_named_invariant_variants_are_not_safety_catches():
    for name in ("TypeInv", "TypeInvariant", "MyTypeCorrectness"):
        out = f"Error: Invariant {name} is violated."
        r = classify_mutation_catch(out)
        assert r["violated"] == name
        assert r["is_safety_catch"] is False, name


def test_no_violation_line_is_not_a_catch():
    out = "Model checking completed. No error has been found."
    r = classify_mutation_catch(out)
    assert r["violated"] is None
    assert r["is_safety_catch"] is False


def test_summarize_counts_only_safety_catches_for_safety_rate():
    results = [
        {"mutation": "a", "applied": True, "killed": True, "safety_killed": True},
        {"mutation": "b", "applied": True, "killed": True, "safety_killed": False},   # TypeOK-only
        {"mutation": "c", "applied": True, "killed": False, "safety_killed": False},  # survived
        {"mutation": "d", "applied": False},                                          # not applicable
        {"mutation": "e", "applied": True, "killed": None},                           # mutant unparseable
    ]
    s = summarize_mutants(results)
    assert s["attempted"] == 3            # a, b, c
    assert s["killed"] == 2               # a, b
    assert s["kill_rate"] == round(2 / 3, 2)
    assert s["safety_killed"] == 1        # a only
    assert s["safety_catch_rate"] == round(1 / 3, 2)


def test_summarize_no_attempted_returns_none_rates():
    s = summarize_mutants([{"mutation": "a", "applied": False}])
    assert s["attempted"] == 0
    assert s["killed"] == 0
    assert s["kill_rate"] is None
    assert s["safety_catch_rate"] is None
