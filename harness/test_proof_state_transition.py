import json
from pathlib import Path

import pytest

from tools import proof_state_transition as transition


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-context-20260905-v1/manifest.json"


def test_transition_trace_is_abstract_and_ordered():
    trace = transition.transition_trace(
        "<1>1. TAKE x \\in Nat\n  <1>2. CASE Even(x)\n"
        "  <1>3. QED BY <1>1, DEF Even")
    assert trace[0] == "entry:structured"
    assert trace.index("assume") < trace.index("case")
    assert "solver:def" in trace
    assert trace[-2:] == ["close:qed", "eos"]
    assert all("Even" not in token for token in trace)


def test_build_is_answer_free_and_fixed_population(tmp_path):
    result = transition.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = transition.load_packet(packet_path, transition.sha(packet_path.read_bytes()))
    assert result["train_rows"] == 17
    assert result["development_rows"] == 4
    assert result["candidate_denominator"] == 116
    assert packet["development_targets_exported"] is False
    assert packet["reference_fragments_exported"] is False
    assert all("reference_fragment" not in json.dumps(row)
               for row in packet["development_rows"])
    assert all(len(row["transition_ids"]) == len(row["transition_events"])
               for row in packet["train_rows"])


def test_renderer_selection_is_score_only(tmp_path):
    transition.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    packet = transition.load_packet(packet_path, transition.sha(packet_path.read_bytes()))
    row = packet["development_rows"][0]
    scores = list(range(len(row["candidate_proposals"])))
    selected = transition.select_candidate(row, scores)
    assert selected["candidate_index"] == len(scores) - 1
    assert selected["candidate"] == row["candidate_proposals"][-1]


def test_packet_rejects_answer_bearing_development_row(tmp_path):
    transition.build(MANIFEST, tmp_path / "packet")
    packet_path = tmp_path / "packet" / "packet.json"
    altered = json.loads(packet_path.read_text())
    altered["development_rows"][0]["answer"] = "hidden"
    packet_path.write_text(json.dumps(altered))
    with pytest.raises(ValueError, match="answer-bearing"):
        transition.load_packet(packet_path, transition.sha(packet_path.read_bytes()))
