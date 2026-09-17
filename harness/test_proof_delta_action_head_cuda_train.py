import pytest

torch = pytest.importorskip("torch")

from tools.proof_delta_action_head_cuda_train import pool_response_delta


class FakeNet:
    def __init__(self, hidden):
        self.hidden = hidden

    def __call__(self, **_kwargs):
        class Output:
            hidden_states = [None, self.hidden]
        return Output()


def test_delta_representation_subtracts_prompt_terminal_state():
    hidden = torch.tensor([[[1.0, 2.0], [3.0, 5.0], [7.0, 11.0]]])
    encoding = {"input_ids": [1, 2, 3], "labels": [-100, -100, 42]}
    value = pool_response_delta(FakeNet(hidden), encoding, "cpu", torch)
    assert torch.equal(value, torch.tensor([4.0, 6.0]))


def test_delta_representation_rejects_missing_prompt_or_response():
    hidden = torch.zeros((1, 2, 2))
    with pytest.raises(ValueError, match="empty response"):
        pool_response_delta(FakeNet(hidden), {"input_ids": [1, 2], "labels": [1, 2]}, "cpu", torch)
