"""Tests for harness.mutation catch-attribution (#4 fix).

A mutant that only breaks a TypeOK-style invariant must NOT count as a real
"catch" -- otherwise a spec with a strong TypeOK and a vacuous safety invariant
scores well while checking nothing (the exact failure this project exists to
detect). Only a violation of a non-TypeOK safety property/invariant is a real
catch.
"""
from harness.mutation import classify_mutation_catch, summarize_mutants


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
