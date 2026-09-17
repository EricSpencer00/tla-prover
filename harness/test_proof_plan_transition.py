import json
from pathlib import Path

import pytest

from tools import proof_plan_transition as plan


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-manifest-20260905-v2/manifest.json"


def test_plan_slots_are_ordered_and_frozen():
    assert plan.plan_for_fragment("BY DEF Init, TypeOK") == {
        "entry": "direct", "local": "definitions", "close": "by"
    }
    assert plan.plan_for_fragment("<1>1. P\n  OBVIOUS\n<1>. QED BY P") == {
        "entry": "structured", "local": "obligations", "close": "qed"
    }


def test_build_is_answer_free_and_exact_population(tmp_path):
    result = plan.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = json.loads(packet_path.read_text())
    assert result["train_rows"] == 17
    assert result["development_rows"] == 4
    assert packet["development_targets_exported"] is False
    assert all("plan" not in row for row in packet["development_rows"])
    assert all("reference_fragment" not in json.dumps(row) for row in packet["development_rows"])


def test_packet_round_trip_and_renderer_distance(tmp_path):
    plan.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = plan.load_packet(packet_path, plan.sha(packet_path.read_bytes()))
    row = packet["development_rows"][0]
    selected = plan.select_candidate(row, row["candidate_plans"][0])
    assert selected["candidate_index"] == 0
    assert selected["plan_distance"] == 0


def test_packet_rejects_answer_bearing_development_row(tmp_path):
    plan.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    altered = json.loads(packet_path.read_text())
    altered["development_rows"][0]["answer"] = "hidden"
    packet_path.write_text(json.dumps(altered))
    with pytest.raises(ValueError, match="answer-bearing"):
        plan.load_packet(packet_path, plan.sha(packet_path.read_bytes()))
