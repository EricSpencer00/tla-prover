import hashlib
import json

import pytest

from tools.build_official_candidate_rank_packet import build
from tools.proof_official_candidate_rank_score import (
    normalize_rankings,
    validate_answer_free_packet,
)


def test_official_packet_is_fixed_and_answer_free(tmp_path):
    manifest = tmp_path / "manifest.json"
    tasks = []
    for index in range(119):
        tasks.append({
            "id": str(index), "split": "official_test", "theorem_name": "T",
            "target_goal": "P", "symbolic_candidates": ["OBVIOUS", "BY DEF P"],
            "retrieval": {"visible_facts": [], "ranked_imported_facts": []},
        })
    manifest.write_text(json.dumps({"tasks": tasks,
                                    "reference_fragments_used": False}))
    output = tmp_path / "packet"
    result = build(manifest, output)
    assert result["rows"] == 119
    packet = json.loads((output / "packet.json").read_text())
    assert packet["denominator"] == 119
    assert packet["reference_fragment_used"] is False
    assert "response" not in json.dumps(packet)


def test_rankings_require_complete_frozen_candidate_set():
    packet = {"rows": [{"id": "x", "candidate_proposals": ["OBVIOUS", "BY DEF P"]}]}
    with pytest.raises(ValueError, match="incomplete"):
        normalize_rankings({"x": [{"candidate_index": 0, "candidate": "OBVIOUS",
                                    "mean_logp": -1.0}]}, packet)


def test_rankings_are_sorted_by_score_then_index():
    packet = {"rows": [{"id": "x", "candidate_proposals": ["OBVIOUS", "BY DEF P"]}]}
    result = normalize_rankings({"x": [
        {"candidate_index": 1, "candidate": "BY DEF P", "mean_logp": -1.0},
        {"candidate_index": 0, "candidate": "OBVIOUS", "mean_logp": -1.0},
    ]}, packet)
    assert [row["candidate_index"] for row in result["x"]] == [0, 1]


def test_typed_official_packet_is_answer_free_and_supported():
    packet = {
        "packet_kind": "answer_free_typed_candidate_rank_official",
        "split": "official_test", "denominator": 119,
        "reference_fragment_used": False,
        "reference_fragment_exported": False, "proof_bodies_exported": False,
        "successful_candidates_exported": False, "generated_feedback": False,
        "training_executed": False, "parameter_updates": 0,
        "tlaps_executed": False, "proof_or_quality_claim": False,
        "gate_claim": False, "development_targets_exported": False,
        "official_packet_sha256":
            "f40539a20e449ad63b8244e85eff33c8022402df11a84e8228b71ccbfeae11b5",
        "source_manifest_sha256":
            "3380cf37c7311466ea7762662d55866839b3c3620ce73fb8d7ad209befe6de1d",
    }
    validate_answer_free_packet(packet)
