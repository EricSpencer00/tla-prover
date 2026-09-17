import json

import pytest

from tools.proof_variable_action_cuda_eval import cuda_bf16_supported, digest, validate_packet


def packet(rows):
    return {
        "packet_kind": "answer_free_official_variable_symbolic_action_ranking",
        "split": "official_test", "denominator": 119,
        "protected_evaluation": True, "rows": rows,
        "reference_fragment_used": False, "reference_fragment_exported": False,
        "proof_bodies_exported": False, "successful_candidates_exported": False,
        "generated_feedback": False, "training_executed": False,
        "parameter_updates": 0, "tlaps_executed": False,
        "proof_or_quality_claim": False,
    }


def row(index=0, width=5):
    candidates = [f"BY SMT DEF F{n}" for n in range(width)]
    return {"id": f"task-{index}", "split": "official_test",
            "theorem_name": "T", "prompt": "P",
            "prompt_sha256": __import__("hashlib").sha256(b"P").hexdigest(),
            "candidate_proposals": candidates,
            "candidate_proposals_sha256": digest(candidates)}


def test_variable_width_packet_accepts_bounded_rows():
    rows = [row(i) for i in range(119)]
    assert len(validate_packet(packet(rows))) == 119


def test_variable_width_packet_rejects_overbound_width():
    rows = [row(i) for i in range(119)]
    rows[0] = row(0, 33)
    with pytest.raises(ValueError, match="width"):
        validate_packet(packet(rows))


def test_bf16_check_uses_cuda_namespace_when_available():
    class Cuda:
        @staticmethod
        def is_bf16_supported():
            return True

    class Torch:
        cuda = Cuda()

    assert cuda_bf16_supported(Torch)


def test_bf16_check_falls_back_to_device_capability():
    class Cuda:
        @staticmethod
        def get_device_capability():
            return (8, 0)

    class Torch:
        cuda = Cuda()

    assert cuda_bf16_supported(Torch)
