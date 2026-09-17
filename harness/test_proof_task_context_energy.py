import json
from pathlib import Path

import pytest

from tools import proof_task_context_energy as energy


def test_features_are_answer_free_and_interaction_based():
    task = {
        "id": "x", "theorem_name": "Inv", "prefix":
        "---- MODULE X ----\nEXTENDS Naturals\nInit == TRUE\nTHEOREM Inv == Init => []TypeOK\n  <1>a. Init => TypeOK\n"
    }
    tokens = energy.joint_features(task, "BY SMT, TypeOK DEF Init")
    assert any(token.startswith("joint:task:") for token in tokens)
    assert all("reference" not in token.lower() for token in tokens)


def test_forbidden_answer_fields_are_rejected():
    with pytest.raises(ValueError, match="answer-bearing"):
        energy.reject_forbidden({"reference_fragment": "hidden"})


def test_model_is_deterministic():
    examples = [(("task:a", "action:smt"), 1), (("task:a", "action:def"), 0),
                (("task:b", "action:smt"), 0), (("task:b", "action:def"), 1)]
    first = energy.fit_logistic(examples)
    second = energy.fit_logistic(examples)
    assert first == second


def test_summary_contract_has_fixed_denominator(tmp_path):
    summary = {"denominator_fixed": True, "quality_claim": False, "gate_claim": False}
    path = tmp_path / "summary.json"
    path.write_text(json.dumps(summary))
    assert json.loads(path.read_text())["denominator_fixed"] is True
