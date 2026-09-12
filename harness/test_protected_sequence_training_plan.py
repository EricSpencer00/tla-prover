import copy

from tools import protected_sequence_training_plan as plan
from harness.test_protected_sequence_objective_contract import valid


def packet20():
    value = valid()
    template = value["pairs"][0]
    value["pairs"] = []
    for index in range(20):
        pair = copy.deepcopy(template)
        pair["source_id"] = f"training-source-{index:02d}"
        value["pairs"].append(pair)
    from tools import protected_sequence_objective_contract as contract
    value["objective_sha256"] = contract.digest({
        "kind": contract.KIND, "algorithm": contract.ALGORITHM,
        "pairs": value["pairs"],
    })
    return value


def test_split_is_complete_disjoint_and_deterministic():
    value = packet20()
    first = plan.build(value)
    second = plan.build(copy.deepcopy(value))
    assert first == second
    assert len(first["train_source_ids"]) == 8
    assert len(first["holdout_source_ids"]) == 12
    assert not set(first["train_source_ids"]) & set(first["holdout_source_ids"])
    assert set(first["train_source_ids"] + first["holdout_source_ids"]) == {
        f"training-source-{index:02d}" for index in range(20)
    }


def test_plan_never_uses_protected_rows_for_training_or_selection():
    result = plan.build(packet20())
    assert result["protected_training"] is False
    assert result["protected_model_selection"] is False
    assert result["gate_claim"] is False
    assert result["acceptance_evaluation"]["mode"] == "unchanged_unsupplied_frozen_prompts"
