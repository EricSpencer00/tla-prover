"""Tests for harness.adequacy structural-feature extraction (W1 battery).

Structural features are a deterministic, TLC-free complexity signal used two ways:
(1) as inputs to quality_gold, (2) as the complexity weights for the RFT reward
(review fix #2 -- reward complex survivors, not just any survivor).
"""
from harness.adequacy import structural_features

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
