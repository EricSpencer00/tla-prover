import pytest

torch = pytest.importorskip("torch")

from tools.proof_listwise_action_head_cuda_train import listwise_loss


def test_listwise_loss_normalizes_complete_candidate_set():
    scores = torch.tensor([0.0, 2.0, -1.0], requires_grad=True)
    loss = listwise_loss(scores, [0, 1, 0], torch)
    expected = -torch.log_softmax(scores, dim=0)[1]
    assert torch.allclose(loss, expected)
    loss.backward()
    assert torch.isfinite(scores.grad).all()


def test_listwise_loss_rejects_all_negative_task():
    with pytest.raises(ValueError, match="certified action"):
        listwise_loss(torch.zeros(3), [0, 0, 0], torch)
