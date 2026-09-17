from pathlib import Path
import json

from tools.proof_action_signature_admission import (
    HOLDOUT_IDS, SLOTS, action_signature, load_packets, render_rank,
    target_signatures,
)


ROOT = Path(__file__).resolve().parents[1]
STAGE = ROOT / "results/stages/tla-action-head-gpu-20260917-v1"


def test_signature_is_fixed_and_structural():
    assert len(SLOTS) == 6
    assert action_signature("BY SMT DEF vars, Init") == (1, 1, 0, 0, 0, 0)
    assert action_signature("BY USE Foo INSTANCE Naturals") == (0, 0, 1, 0, 0, 1)


def test_sanitized_packets_and_targets():
    packet, official, labels = load_packets(
        STAGE / "train-packet.json", STAGE / "official-packet.json",
        STAGE / "train-labels.jsonl")
    targets = target_signatures(packet, labels)
    assert len(packet["rows"]) == 17
    assert len(official["rows"]) == 119
    assert set(targets) == {row["id"] for row in packet["rows"]}
    assert all(targets[task_id] is not None for task_id in HOLDOUT_IDS)


def test_renderer_is_total_and_tie_breaks_by_candidate_index():
    candidates = ["BY SMT", "BY SMT DEF vars"]
    ranking = render_rank((1, 1, 0, 0, 0, 0), candidates)
    assert ranking[0]["candidate_index"] == 1
    tied = render_rank((1, 0, 0, 0, 0, 0), candidates)
    assert [item["candidate_index"] for item in tied] == [0, 1]
