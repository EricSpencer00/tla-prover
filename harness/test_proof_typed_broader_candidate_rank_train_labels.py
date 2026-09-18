from __future__ import annotations

from pathlib import Path

from tools import proof_typed_broader_candidate_rank as packet_tools
from tools import proof_typed_broader_candidate_rank_train_labels as labels


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "results/runs/proof-typed-broader-candidate-rank-20260918-v1/packet.json"


def test_broader_label_loader_has_exact_train_population():
    packet = packet_tools.load_packet(PACKET, packet_tools.sha(PACKET.read_bytes()))
    assert len(packet["train_rows"]) == 32
    assert len(packet["development_rows"]) == 4
    assert labels.sha(PACKET.read_bytes()) == packet_tools.sha(PACKET.read_bytes())


def test_broader_label_output_is_sanitized():
    assert "reference_fragment" not in labels.__doc__
    assert "certify_fragment" in labels.__dict__
