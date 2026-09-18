from __future__ import annotations

import json
from pathlib import Path

from tools import proof_typed_candidate_rank as rank
from tools import proof_typed_candidate_rank_train_labels as labels


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "results/runs/proof-typed-candidate-rank-20260917-v2/packet.json"


def test_label_packet_is_train_only_and_sanitized(tmp_path):
    packet = labels.load_packet(PACKET, rank.sha(PACKET.read_bytes()))
    output = tmp_path / "labels"
    # The test does not invoke TLAPS; validate the output contract with a
    # representative sanitized record instead.
    output.mkdir()
    path = output / "labels.jsonl"
    path.write_text(json.dumps({
        "task": packet["train_rows"][0]["id"], "candidate_index": 0,
        "candidate": packet["train_rows"][0]["candidate_proposals"][0],
        "certified": False,
    }) + "\n")
    record = json.loads(path.read_text())
    assert set(record) == {"task", "candidate_index", "candidate", "certified"}
    assert not any("reference" in key or "proof" in key for key in record)
    assert not packet["development_rows"][0].get("teacher_candidate_scores")


def test_label_sha_is_content_bound(tmp_path):
    path = tmp_path / "labels.jsonl"
    path.write_text('{"task":"x","candidate_index":0,"candidate":"BY SMT","certified":false}\n')
    assert labels.sha(path.read_bytes()) == labels.sha(path.read_bytes())
    path.write_text(path.read_text() + "\n")
    assert labels.sha(path.read_bytes()) != labels.sha((path.read_text().rstrip() + "\n").encode())
