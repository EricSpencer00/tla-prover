import json

import pytest

from tools.proof_verifier_scaffold_cuda_eval import trim_output, validate_packet


def _packet():
    rows = []
    for i in range(4):
        prompt = f"fixed prompt {i}"
        rows.append({
            "id": f"dev-{i}", "split": "development", "prompt": prompt,
            "prompt_sha256": __import__("hashlib").sha256(prompt.encode()).hexdigest(),
            "retrieval_hits": [],
        })
    return {
        "packet_kind": "answer_free_verifier_conditioned_retrieval",
        "split": "development", "denominator": 4, "rows": rows,
        "reference_fragment_used": False, "reference_fragment_exported": False,
        "proof_bodies_exported": False, "successful_candidates_exported": False,
        "model_executed": False, "training_executed": False,
        "parameter_updates": 0, "proof_or_quality_claim": False,
    }


def test_validate_packet_requires_exact_answer_free_development_population():
    assert len(validate_packet(_packet())) == 4


def test_validate_packet_rejects_answer_field():
    packet = _packet()
    packet["rows"][0]["response"] = "BY DEF Init"
    with pytest.raises(ValueError, match="answer-bearing"):
        validate_packet(packet)


def test_trim_output_stops_at_first_eos():
    assert trim_output([3, 4, 9, 5], {9}) == [3, 4, 9]
    assert trim_output([3, 4], {9}) == [3, 4]
