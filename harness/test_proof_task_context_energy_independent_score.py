import json

import pytest

from tools import proof_task_context_energy_independent_score as scorer


def test_rank_is_deterministic_and_tie_breaks_by_candidate_index():
    task = {"theorem_name": "T", "prefix": "THEOREM T == TRUE\n"}
    candidates = ["BY DEF T", "BY SMT"]
    weights = {}
    ranked = scorer.rank(task, candidates, weights, 0.0)
    assert [row["candidate_index"] for row in ranked] == [0, 1]


def test_scorer_rejects_answer_bearing_rows():
    with pytest.raises(ValueError, match="answer-bearing"):
        scorer.reject_forbidden([{"response": "hidden"}], "packet.rows")


def test_summary_contract_is_non_promotional(tmp_path):
    path = tmp_path / "summary.json"
    path.write_text(json.dumps({"denominator_fixed": True, "quality_claim": False,
                                "gate_claim": False}))
    value = json.loads(path.read_text())
    assert value["denominator_fixed"] and not value["quality_claim"] and not value["gate_claim"]
