import json

import torch
import pytest

from tools import protected_sequence_preference_train as train
from tools import protected_sequence_training_plan as training_plan
from harness.test_protected_sequence_training_plan import packet20


def test_response_score_includes_all_response_tokens_and_eos():
    tokens = torch.tensor([[1, 2, 3, 4]])
    logits = torch.zeros((1, 4, 8))
    logits[0, 1, 3] = 4
    logits[0, 2, 4] = 6
    score = train.response_mean_logprob(logits, tokens, 2)
    expected = torch.stack([torch.log_softmax(logits[0, 1], 0)[3],
                            torch.log_softmax(logits[0, 2], 0)[4]]).mean()
    assert torch.allclose(score[0], expected)


def test_pairwise_loss_has_positive_and_negative_gradients():
    positive = torch.tensor([-2.0], requires_grad=True)
    negative = torch.tensor([-2.5], requires_grad=True)
    loss, gap = train.pairwise_loss(positive, negative)
    loss.backward()
    assert gap.item() == pytest.approx(0.5)
    assert positive.grad.item() < 0
    assert negative.grad.item() > 0


def test_anchor_prevents_lowering_both_scores_as_solution():
    high, _ = train.pairwise_loss(torch.tensor([-1.0]), torch.tensor([-2.0]))
    low, _ = train.pairwise_loss(torch.tensor([-11.0]), torch.tensor([-12.0]))
    assert low > high


def test_complete_pair_objective_backpropagates_without_update():
    class Tiny(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.embed = torch.nn.Embedding(16, 6)
            self.head = torch.nn.Linear(6, 16)
        def forward(self, input_ids, **_):
            return type("Output", (), {"logits": self.head(self.embed(input_ids))})
    net = Tiny()
    before = {name: value.detach().clone() for name, value in net.named_parameters()}
    pair = {"prompt_tokens": [1, 2], "positive_tokens": [3, 4, 5],
            "negative_tokens": [6, 7, 8, 9]}
    loss, gap = train.objective(net, pair)
    loss.backward()
    assert torch.isfinite(loss) and torch.isfinite(gap)
    assert any(value.grad is not None and value.grad.norm() > 0 for value in net.parameters())
    assert all(torch.equal(value, before[name]) for name, value in net.named_parameters())


def test_holdout_scoring_uses_precision_context_for_mixed_dtype_forward():
    class Tiny(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.embed = torch.nn.Embedding(16, 6)
            self.head = torch.nn.Linear(6, 16).to(torch.bfloat16)

        def forward(self, input_ids, **_):
            return type("Output", (), {"logits": self.head(self.embed(input_ids))})

    pairs = [
        {"prompt_tokens": [1, 2], "positive_tokens": [3], "negative_tokens": [4]},
        {"prompt_tokens": [5, 6], "positive_tokens": [7], "negative_tokens": [8]},
    ]
    score = train.mean_gap(Tiny(), pairs, device="cpu", context=torch.no_grad,
                           forward_context=lambda: torch.autocast("cpu", dtype=torch.bfloat16))
    assert torch.isfinite(torch.tensor(score))


def test_training_plan_admits_exact_disjoint_nonprotected_split(tmp_path):
    packet = packet20()
    path = tmp_path / "plan.json"
    path.write_text(json.dumps(training_plan.build(packet)))
    plan, selected, holdout = train.load_training_plan(path, packet)
    assert len(selected) == train.BUDGET["steps"]
    assert len(holdout) == train.BUDGET["pairs"] - train.BUDGET["steps"]
    assert {pair["source_id"] for pair in selected}.isdisjoint({pair["source_id"] for pair in holdout})
    assert plan["plan_sha256"] == json.loads(path.read_text())["plan_sha256"]
    assert plan["protected_training"] is False
    assert plan["protected_model_selection"] is False


def test_training_plan_rejects_protected_model_selection(tmp_path):
    packet = packet20()
    value = training_plan.build(packet)
    value["protected_model_selection"] = True
    value["plan_sha256"] = train.contract.digest({key: item for key, item in value.items()
                                                   if key != "plan_sha256"})
    path = tmp_path / "plan.json"
    path.write_text(json.dumps(value))
    with pytest.raises(ValueError):
        train.load_training_plan(path, packet)


@pytest.mark.parametrize("prompt", [0, 4])
def test_response_score_rejects_empty_side(prompt):
    with pytest.raises(ValueError):
        train.response_mean_logprob(torch.zeros((1, 4, 8)), torch.ones((1, 4), dtype=torch.long), prompt)
