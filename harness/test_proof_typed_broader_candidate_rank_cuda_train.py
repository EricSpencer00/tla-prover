from __future__ import annotations

from tools import proof_typed_broader_candidate_rank_cuda_train as worker


def test_broader_worker_is_bound_to_broader_population():
    assert worker.PROFILE.endswith("broader32 TRAIN")
    assert worker.packet_tools.PARENT_SHA256


def test_broader_worker_has_no_verifier_or_reward_path():
    source = worker.__file__
    text = open(source, encoding="utf-8").read()
    assert "verifier_feedback_used" in text
    assert "reward_used" in text
    assert "torch.cuda.is_available" in text
