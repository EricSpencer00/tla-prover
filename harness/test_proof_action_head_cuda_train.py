from tools.proof_action_head_cuda_train import HOLDOUT_IDS, pairwise_loss, validate_packet


def test_holdout_is_disjoint_and_fixed():
    assert len(HOLDOUT_IDS) == 4
    assert "highest-done-step" in HOLDOUT_IDS
    assert "addtwo-init" not in HOLDOUT_IDS


def test_validate_packet_rejects_wrong_kind():
    try:
        validate_packet({"packet_kind": "wrong", "denominator": 17, "rows": []}, "train", 17)
    except ValueError as error:
        assert "train" in str(error)
    else:
        raise AssertionError("wrong packet kind accepted")


def test_pairwise_loss_requires_mixed_labels():
    import pytest
    torch = pytest.importorskip("torch")
    scores = torch.tensor([1.0, 0.0], requires_grad=True)
    value = pairwise_loss(scores, [1, 0], torch)
    assert value.item() > 0
    value.backward()
    assert scores.grad is not None
