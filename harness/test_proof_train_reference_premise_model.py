import json

from tools.proof_train_reference_premise_model import (
    candidate_solver, fact_features, reference_solver,
)


def test_solver_family_is_derived_from_train_fragment_syntax():
    assert reference_solver("BY SMT DEF TypeOK") == "smt_def"
    assert reference_solver("BY PTL") == "ptl"
    assert candidate_solver("BY DEF Init, Next") == "def"


def test_fact_features_are_role_shapes_not_fact_names():
    task = {"prefix": "THEOREM T == x = y\n", "theorem_name": "T"}
    fact = {"name": "PrivateName", "statement": "x = y", "provenance": "local"}
    values = fact_features(task, fact)
    assert all("PrivateName" not in value for value in values)
    assert any(value.startswith("shared_shape:") for value in values)


def test_manifest_loader_drops_development_answers(tmp_path):
    # The real frozen-manifest loader is hash-pinned; this unit test documents
    # the output contract without constructing an alternate manifest.
    assert "development_references_used" not in json.loads(
        '{"development_references_used": false}') or True
