import copy
import pytest

from tools import protected_sequence_objective_contract as contract


def valid():
    pairs = [{
        "row": 45,
        "negative_origin": "actual_model_rollout",
        "positive_sany": True,
        "negative_sany": False,
        "positive_tokens": [11, 12, 128009],
        "negative_tokens": [11, 99, 100],
        "eos_token_id": 128009,
        "rollout_receipt_sha256": "a" * 64,
    }]
    return {
        "kind": contract.KIND,
        "algorithm": contract.ALGORITHM,
        "protected_rows": [47, 107],
        "protected_training": False,
        "gate_claim": False,
        "retention": {"rows": [47, 107], "mode": "supplied_prefix_parent_replay",
                      "required_sany_passes": 2, "credit": "zero"},
        "evaluation": {"rows": [47, 107], "mode": "unchanged_unsupplied_frozen_prompts",
                       "denominator": 2, "required_sany_passes": 2},
        "pairs": pairs,
        "objective_sha256": contract.digest({"kind": contract.KIND,
                                              "algorithm": contract.ALGORITHM, "pairs": pairs}),
    }


def test_accepts_distinct_sequence_contract():
    assert contract.validate(valid())["gate_claim"] is False


@pytest.mark.parametrize("mutation", [
    lambda v: v.update(kind="syntax_token_preference_v1"),
    lambda v: v["pairs"][0].update(row=47),
    lambda v: v["pairs"][0].update(negative_origin="synthetic_corruption"),
    lambda v: v["pairs"][0].update(negative_sany=True),
    lambda v: v["pairs"][0].update(positive_tokens=[11]),
    lambda v: v["pairs"][0].update(positive_tokens=[11, 12]),
    lambda v: v["retention"].update(credit="model"),
    lambda v: v["evaluation"].update(mode="supplied_prefix"),
])
def test_fails_closed_on_leakage_proxy_or_incomplete_sequence(mutation):
    value = copy.deepcopy(valid())
    mutation(value)
    with pytest.raises(ValueError):
        contract.validate(value)
