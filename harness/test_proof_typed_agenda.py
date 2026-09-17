import json
from pathlib import Path

import pytest

from tools import proof_typed_agenda as agenda


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-context-20260905-v1/manifest.json"


def test_build_is_answer_free_and_fixed_population(tmp_path):
    result = agenda.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = agenda.load_packet(packet_path, agenda.sha(packet_path.read_bytes()))
    assert result["train_rows"] == 17
    assert result["development_rows"] == 4
    assert result["candidate_denominator"] == 116
    assert packet["reference_fragments_exported"] is False
    assert packet["candidate_index_labels_used"] is False
    assert all("reference_fragment" not in json.dumps(row)
               for row in packet["development_rows"])


def test_slot_renderer_is_deterministic_and_fails_closed(tmp_path):
    out = agenda.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = agenda.load_packet(packet_path, agenda.sha(packet_path.read_bytes()))
    row = packet["development_rows"][0]
    prediction = row["candidate_agenda_slots"][0]
    first = agenda.render_candidate(row, prediction)
    second = agenda.render_candidate(row, prediction)
    assert first == second
    with pytest.raises(ValueError, match="empty predicted"):
        agenda.render_candidate(row, [])
