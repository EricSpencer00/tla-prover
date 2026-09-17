import json
from pathlib import Path

import pytest

from tools import proof_state_transition as transition
from tools import proof_state_transition_score as score


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "results/runs/proof-state-transition-20260917-v3/packet.json"
RESULT = ROOT / "results/runs/proof-state-transition-20260917-v3/job-7630491/result.7630491"
AUDIT = ROOT / "results/runs/proof-protected-symbolic-search-20260917-v2/checks.jsonl"


def test_valid_task_bound_generations_and_fixed_audit():
    packet = transition.load_packet(PACKET, transition.sha(PACKET.read_bytes()))
    for arm in ("base", "parent", "child"):
        rows = score.load_generations(RESULT / f"{arm}_generations.json", packet)
        assert len(rows) == 4
    audit = score.load_frozen_audit(AUDIT, packet)
    assert len(audit) == 116


def test_generation_candidate_binding_fails_closed(tmp_path):
    packet = transition.load_packet(PACKET, transition.sha(PACKET.read_bytes()))
    altered = json.loads((RESULT / "child_generations.json").read_text())
    altered[0]["candidate"] = "BY SMT"
    path = tmp_path / "child.json"
    path.write_text(json.dumps(altered))
    with pytest.raises(ValueError, match="candidate bytes changed"):
        score.load_generations(path, packet)
