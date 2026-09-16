import hashlib
import json

import pytest

from tools.build_official_candidate_rank_packet import build
from tools.proof_official_candidate_rank_score import normalize_rankings


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
