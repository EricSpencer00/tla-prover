import pytest

from tools.proof_obligation_residual_model import fit_pairwise, residual_features, shape_atoms


def test_shape_atoms_capture_obligation_families_without_identifiers():
    atoms = shape_atoms("\\A x \\in S : x' = x /\\ UNCHANGED vars")
    assert {"quantifier", "equality", "prime", "conjunction", "unchanged"} <= atoms
    assert all("x" not in atom for atom in atoms if atom.startswith("goal_has:"))


def test_residual_features_do_not_export_candidate_names():
    task = {"id": "x", "theorem_name": "Target",
            "prefix": "---- MODULE X -----\nTHEOREM Target == foo = bar\n<1>1. TRUE\n",
            "suffix": "\n====\n", "dependencies": []}
    index = {"facts": {
        "A": {"name": "A", "statement": "foo = bar", "provenance": "local"},
    }, "library_sha256": {}}
    values = residual_features(task, "BY SMT, A", index)
    assert all(":A" not in value for value in values)
    assert any(value.startswith("satisfied:equality:") for value in values)


def test_pairwise_fit_prefers_positive_feature_set():
    positive = ("solver:smt", "residual:shape_count:0")
    negative = ("solver:def", "residual:shape_count:3")
    weights, bias = fit_pairwise([(positive, negative)], epochs=80)
    assert bias + sum(weights.get(x, 0.0) for x in positive) > \
           bias + sum(weights.get(x, 0.0) for x in negative)


def test_shape_pattern_is_not_an_answer_or_feedback_channel():
    with pytest.raises(Exception):
        # The feature extractor accepts syntax only; this ensures a malformed
        # unsupported candidate cannot silently become a positive signal.
        residual_features({"theorem_name": "T", "prefix": "THEOREM T == x",
                           "suffix": "", "dependencies": []}, "OMITTED", {"facts": {}})
