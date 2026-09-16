import json
from pathlib import Path

import pytest

from tools.proof_official_candidate_sum_rerank import rerank, sha


def packet_and_scores():
    root = Path(__file__).resolve().parents[1]
    packet = root / "results/stages/tla-official-candidate-rank-gpu-20260916-v1/packet.json"
    scores = root / "results/runs/tla-official-candidate-rank-gpu-20260916-v1/result.7628679/scores.jsonl"
    return packet, scores


def test_sum_rerank_is_complete_and_answer_free(tmp_path):
    packet, scores = packet_and_scores()
    output = tmp_path / "rankings.json"
    summary = rerank(packet, scores, output, sha(packet.read_bytes()))
    assert summary["fully_ranked_tasks"] == 119
    assert summary["candidate_rows"] == 462
    assert summary["reference_fragment_used"] is False
    data = json.loads(output.read_text())
    assert len(data) == 119
    assert all(len(rows) in {2, 4} for rows in data.values())


def test_sum_rerank_rejects_wrong_packet_hash(tmp_path):
    packet, scores = packet_and_scores()
    with pytest.raises(ValueError, match="packet hash mismatch"):
        rerank(packet, scores, tmp_path / "rankings.json", "0" * 64)
