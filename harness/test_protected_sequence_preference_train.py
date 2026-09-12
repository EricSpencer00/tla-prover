import torch
import pytest

from tools import protected_sequence_preference_train as train


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


@pytest.mark.parametrize("prompt", [0, 4])
def test_response_score_rejects_empty_side(prompt):
    with pytest.raises(ValueError):
        train.response_mean_logprob(torch.zeros((1, 4, 8)), torch.ones((1, 4), dtype=torch.long), prompt)
