import pytest

from tools.proof_goal_coverage_model import candidate_parts, coverage_features


def test_candidate_parts_are_bounded_and_answer_free():
    assert candidate_parts("BY SMT, TypeOK, Next") == ("smt_facts", ("TypeOK", "Next"))
    assert candidate_parts("BY SMT DEF vars, Init") == ("smt_def", ("vars", "Init"))
    with pytest.raises(ValueError):
        candidate_parts("BY SMT, OMITTED")


def test_goal_coverage_features_measure_union_and_redundancy():
    task = {"id": "x", "theorem_name": "Target",
            "prefix": "---- MODULE X -----\nA == foo = bar\nB == foo /\\ bar\nTHEOREM Target == foo = bar\n<1>1. TRUE\n",
            "suffix": "\n====\n", "dependencies": []}
    index = {"facts": {
        "A": {"name": "A", "statement": "foo = bar", "provenance": "local"},
        "B": {"name": "B", "statement": "foo /\\ bar", "provenance": "local"},
    }, "library_sha256": {}}
    features = coverage_features(task, "BY SMT, A, B", index)
    assert "goal:covered:2" in features
    assert any(item.startswith("facts:redundant") for item in features)


def test_coverage_features_do_not_include_raw_candidate_names():
    task = {"id": "x", "theorem_name": "Target",
            "prefix": "---- MODULE X -----\nA == x\nTHEOREM Target == x\n<1>1. TRUE\n",
            "suffix": "\n====\n", "dependencies": []}
    index = {"facts": {"A": {"name": "A", "statement": "x", "provenance": "local"}},
             "library_sha256": {}}
    assert all(":A" not in item and ":B" not in item for item in
               coverage_features(task, "BY SMT, A", index))
