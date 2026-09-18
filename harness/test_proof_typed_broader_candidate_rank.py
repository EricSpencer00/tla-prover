from __future__ import annotations

from pathlib import Path

from tools import proof_typed_broader_candidate_rank as broader


ROOT = Path(__file__).resolve().parents[1]


def test_broader_packet_builds_without_development_targets(tmp_path):
    summary = broader.build(tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = broader.load_packet(packet_path, summary["packet_sha256"])
    assert len(packet["train_rows"]) == 32
    assert len(packet["development_rows"]) == 4
    assert packet["development_targets_exported"] is False
    assert packet["candidate_index_labels_used"] is False
    assert all("teacher_candidate_index" not in row for row in packet["development_rows"])


def test_broader_packet_keeps_distinct_train_ids(tmp_path):
    summary = broader.build(tmp_path / "packet")
    packet = broader.load_packet(tmp_path / "packet" / "packet.json", summary["packet_sha256"])
    ids = [row["id"] for row in packet["train_rows"]]
    assert len(ids) == len(set(ids)) == 32
    assert len({row["source_family"] for row in packet["train_rows"]}) >= 4
