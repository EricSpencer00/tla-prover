from __future__ import annotations

import json
from pathlib import Path

from tools import proof_typed_candidate_rank as rank


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-context-20260905-v1/manifest.json"


def test_candidate_rank_packet_is_train_labeled_and_development_target_free(tmp_path):
    output = tmp_path / "packet"
    summary = rank.build(MANIFEST, output)
    packet = rank.load_packet(output / "packet.json", summary["packet_sha256"])
    assert len(packet["train_rows"]) == 17
    assert len(packet["development_rows"]) == 4
    assert packet["candidate_index_labels_used"] is False
    assert packet["train_teacher_agenda_labels_used"] is True
    assert all("teacher_candidate_index" in row for row in packet["train_rows"])
    assert all("teacher_candidate_index" not in row for row in packet["development_rows"])
    assert sum(len(row["candidate_proposals"]) for row in packet["development_rows"]) == 116


def test_candidate_rank_rejects_development_teacher_label(tmp_path):
    output = tmp_path / "packet"
    rank.build(MANIFEST, output)
    path = output / "packet.json"
    packet = json.loads(path.read_text())
    packet["development_rows"][0]["teacher_candidate_index"] = 0
    path.write_text(json.dumps(packet))
    try:
        rank.load_packet(path)
    except ValueError as exc:
        assert "teacher label" in str(exc)
    else:
        raise AssertionError("development teacher label was accepted")
