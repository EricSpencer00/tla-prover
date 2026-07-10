"""Tests for harness.mutation catch-attribution (#4 fix).

A mutant that only breaks a TypeOK-style invariant must NOT count as a real
"catch" -- otherwise a spec with a strong TypeOK and a vacuous safety invariant
scores well while checking nothing (the exact failure this project exists to
detect). Only a violation of a non-TypeOK safety property/invariant is a real
catch.
"""
from pathlib import Path

from harness.mutation import (classify_mutation_catch, summarize_mutants,
                               run_mutation_on_module, MUTATIONS)

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
