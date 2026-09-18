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


def test_broader_polaris_wrapper_is_bounded_and_hash_bound():
    pbs = open("tools/proof_typed_broader_candidate_rank_polaris.pbs", encoding="utf-8").read()
    assert "ngpus=1" in pbs and "walltime=00:15:00" in pbs
    assert "c919646ee4f3ac418474f91f8f771e0a1c436e9b583aed7ba42f9415e9efc37d" in pbs
    assert "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511" in pbs
