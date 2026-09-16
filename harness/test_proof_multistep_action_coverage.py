import json
from pathlib import Path

import pytest

from tools import proof_multistep_action_coverage as coverage


def test_freeze_emits_answer_free_fixed_width_packet(tmp_path, monkeypatch):
    tasks = []
    for index in range(17):
        task_id = sorted(coverage.TRAIN_IDS)[index]
        tasks.append({
            "id": task_id,
            "split": "train",
            "prefix": "prefix",
            "suffix": "suffix",
            "theorem_name": "Target",
            "target_goal": "Target == P",
            "source_sha256": "source",
            "dependencies": [],
            "reference_fragment": "SECRET ANSWER",
        })

    monkeypatch.setattr(coverage, "answer_free_candidates",
                        lambda task: (["BY A", "BY B", "BY C", "BY D"], {}))
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"tasks": tasks}))
    packet, safe = coverage.freeze(manifest, tmp_path / "out")
    encoded = json.dumps(packet)
    assert "SECRET ANSWER" not in encoded
    assert packet["reference_fragment_used"] is False
    assert packet["reference_fragment_exported"] is False
    assert len(packet["rows"]) == 17
    assert all(len(row["candidate_proposals"]) == 4 for row in packet["rows"])
    assert set(safe) == coverage.TRAIN_IDS


def test_freeze_rejects_wrong_population(tmp_path):
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"tasks": []}))
    with pytest.raises(ValueError, match="17-row"):
        coverage.freeze(manifest, tmp_path / "out")
