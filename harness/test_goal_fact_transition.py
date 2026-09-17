import json
from pathlib import Path

import pytest

from tools import proof_goal_fact_transition as transition


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-context-20260905-v1/manifest.json"


def test_goal_fact_bridge_distinguishes_compound_visible_facts():
    goal = r"LEMMA SumType == ASSUME NEW f \\in [Node -> Nat] PROVE Sum(f) \\in Nat"
    broad = transition.transition_trace("BY DEF Sum, vars, TypeOK", goal)
    bridge = transition.transition_trace("BY SMT, SumIsSumFunction, NodeAssumption, SumFunctionNat", goal)
    assert "bridge:single" in broad
    assert "bridge:compound" in bridge
    assert bridge[-2:] == ["close:by", "eos"]


def test_build_is_answer_free_and_fixed_population(tmp_path):
    result = transition.build(MANIFEST, tmp_path / "packet")
    path = tmp_path / "packet" / "packet.json"
    packet = transition.load_packet(path, transition.sha(path.read_bytes()))
    assert result["train_rows"] == 17
    assert result["development_rows"] == 4
    assert result["candidate_denominator"] == 116
    assert packet["reference_fragments_exported"] is False
    assert all("reference_fragment" not in json.dumps(row)
               for row in packet["development_rows"])
    assert "bridge:compound" in packet["events"]


def test_packet_rejects_answer_bearing_development_row(tmp_path):
    transition.build(MANIFEST, tmp_path / "packet")
    path = tmp_path / "packet" / "packet.json"
    altered = json.loads(path.read_text())
    altered["development_rows"][0]["answer"] = "hidden"
    path.write_text(json.dumps(altered))
    with pytest.raises(ValueError, match="answer-bearing"):
        transition.load_packet(path, transition.sha(path.read_bytes()))


def test_polaris_contract_binds_exact_packet_hash():
    pbs = (ROOT / "tools/proof_goal_fact_transition_polaris.pbs").read_text()
    packet_sha = transition.sha(
        (ROOT / "results/runs/proof-goal-fact-transition-20260917-v1/packet.json")
        .read_bytes()
    )
    assert pbs.count(packet_sha) == 3
    assert "7fdb1f73c5f1d7a385ffef5e0cde1ab6cff416858777aa2d3d9b43039448f418" not in pbs
