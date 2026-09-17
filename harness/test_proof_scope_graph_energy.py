import pytest

from tools import proof_scope_graph_energy as scope


def test_scope_graph_extracts_hierarchy_without_answer_text():
    task = {"prefix": "THEOREM T == TRUE\n  <1>a. Init => T\n    <2>a. T => T\n"}
    values = scope.scope_features(task)
    assert "scope:depth:2" in values
    assert any(value.startswith("scope:parent_kind:") for value in values)


def test_scope_action_cross_features_are_present():
    task = {"prefix": "THEOREM T == TRUE\n  <1>a. Init => T\n"}
    values = scope.joint_scope_features(task, "BY SMT, T")
    assert any(value.startswith("scope_action:") for value in values)


def test_scope_parser_is_deterministic():
    task = {"prefix": "THEOREM T == TRUE\n  <1>a. Init => T\n"}
    assert scope.scope_features(task) == scope.scope_features(task)


def test_invalid_candidate_contract_is_not_silently_promoted():
    assert "action:solver:smt" in scope.candidate_features("BY SMT")
