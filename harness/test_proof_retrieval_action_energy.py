import json
from pathlib import Path

import pytest

from tools import proof_retrieval_action_energy as energy


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "results/runs/proof-multistep-context-20260905-v1/manifest.json"
PACKET = ROOT / "results/runs/proof-multistep-action-coverage-20260917-v2/packet.json"
INDEX = ROOT / "results/runs/proof-verifier-scaffold-20260916-v3/index.jsonl"


def test_frozen_inputs_and_safe_index_are_answer_free():
    tasks, rows, packet_bytes = energy.load_safe_tasks(SOURCE, PACKET)
    assert len(tasks) == len(rows) == 17
    assert energy.sha(packet_bytes) == energy.PACKET_SHA256
    index = []
    for line in INDEX.read_text().splitlines():
        if line.strip():
            value = json.loads(line)
            energy.reject_forbidden(value)
            index.append(value)
    assert len(index) >= 100
    assert all("shape_signature" in item for item in index)
    assert all("proof" not in item for item in index)


def test_retrieval_features_are_deterministic_and_candidate_conditioned():
    tasks, rows, _ = energy.load_safe_tasks(SOURCE, PACKET)
    index = [json.loads(line) for line in INDEX.read_text().splitlines() if line.strip()]
    task_id = sorted(rows)[0]
    retrieved = energy.retrieval_features(index, tasks[task_id])
    assert retrieved == energy.retrieval_features(index, tasks[task_id])
    first = rows[task_id]["candidate_proposals"][0]
    second = rows[task_id]["candidate_proposals"][1]
    assert energy.joint_features(tasks[task_id], first, retrieved) != energy.joint_features(
        tasks[task_id], second, retrieved)


def test_forbidden_retrieval_fields_fail_closed():
    with pytest.raises(ValueError, match="answer-bearing"):
        energy.reject_forbidden({"shape_signature": "x", "response": "hidden"})
