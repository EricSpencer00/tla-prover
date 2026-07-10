"""Tests for harness.adequacy structural-feature extraction (W1 battery).

Structural features are a deterministic, TLC-free complexity signal used two ways:
(1) as inputs to quality_gold, (2) as the complexity weights for the RFT reward
(review fix #2 -- reward complex survivors, not just any survivor).
"""
from harness.adequacy import structural_features, quality_label

SPEC = """---- MODULE Counter ----
\\* a counter spec
EXTENDS Naturals, Sequences
VARIABLES x, y
Init == x = 0 /\\ y = 0
Next == \\/ x' = x + 1 /\\ y' = y
        \\/ y' = y + 1 /\\ x' = x
Spec == Init /\\ [][Next]_<<x, y>>
Safety == x >= 0
===="""


def test_counts_variables():
    assert structural_features(SPEC)["num_variables"] == 2


def test_counts_top_level_definitions():
    # Init, Next, Spec, Safety
    assert structural_features(SPEC)["num_definitions"] == 4


def test_extends_depth():
    assert structural_features(SPEC)["extends_depth"] == 2


def test_counts_disjuncts_and_conjuncts():
    f = structural_features(SPEC)
    assert f["num_disjuncts"] == 2   # the two \/ in Next
    assert f["num_conjuncts"] == 4   # Init(1) + Next(2) + Spec(1)


def test_counts_temporal_operators():
    # one box [] in [][Next]_<<x,y>>
    assert structural_features(SPEC)["temporal_op_count"] == 1


def test_comment_ratio_nonzero_and_loc():
    f = structural_features(SPEC)
    assert f["noncomment_loc"] >= 8
    assert 0.0 < f["comment_ratio"] < 0.5


def test_empty_text_is_all_zero_not_crash():
    f = structural_features("")
    assert f["num_variables"] == 0
    assert f["num_definitions"] == 0
    assert f["comment_ratio"] == 0.0


# --- quality_label (quality_gold gate) --------------------------------------

def test_gold_when_nonvacuous_notthin_strong_mutation():
    r = quality_label(vacuity_reasons=[], distinct_states=7, safety_catch_rate=0.75)
    assert r["quality_gold"] is True
    assert r["fail_reasons"] == []


def test_vacuous_fails_gold():
    r = quality_label(vacuity_reasons=["trivial_invariant:Inv"], distinct_states=7,
                      safety_catch_rate=1.0)
    assert r["quality_gold"] is False
    assert "vacuous" in r["fail_reasons"]


def test_thin_model_fails_gold():
    r = quality_label(vacuity_reasons=[], distinct_states=2, safety_catch_rate=1.0)
    assert r["quality_gold"] is False
    assert "thin_model" in r["fail_reasons"]


def test_weak_mutation_fails_gold_at_threshold_boundary():
    # 0.5 passes; just below fails
    assert quality_label([], 7, 0.5)["quality_gold"] is True
    r = quality_label([], 7, 0.49)
    assert r["quality_gold"] is False
    assert "weak_mutation" in r["fail_reasons"]


def test_none_mutation_rate_fails_gold():
    r = quality_label(vacuity_reasons=[], distinct_states=7, safety_catch_rate=None)
    assert r["quality_gold"] is False
    assert "weak_mutation" in r["fail_reasons"]


def test_multiple_failures_accumulate():
    r = quality_label(vacuity_reasons=["zero_states_generated"], distinct_states=1,
                      safety_catch_rate=0.0)
    assert r["quality_gold"] is False
    assert set(r["fail_reasons"]) == {"vacuous", "thin_model", "weak_mutation"}
