from __future__ import annotations

from pathlib import Path

from tools import proof_typed_candidate_rank_official as official


ROOT = Path(__file__).resolve().parents[1]
STAGE = ROOT / "results/stages/tla-official-candidate-rank-gpu-20260916-v1"


def test_official_typed_packet_has_fixed_119_and_no_reference_data(tmp_path):
    output = tmp_path / "official"
    summary = official.build(STAGE / "packet.json", STAGE / "source-manifest.json", output)
    packet = official.load_packet(output / "packet.json", summary["packet_sha256"])
    assert len(packet["rows"]) == 119
    assert packet["reference_fragment_used"] is False
    assert packet["training_executed"] is False
    assert sum(len(row["candidate_proposals"]) for row in packet["rows"]) > 119


def test_official_constants_bind_stage_inputs():
    assert official.sha((STAGE / "packet.json").read_bytes()) == official.OFFICIAL_PACKET_SHA256
    assert official.sha((STAGE / "source-manifest.json").read_bytes()) == official.SOURCE_MANIFEST_SHA256
