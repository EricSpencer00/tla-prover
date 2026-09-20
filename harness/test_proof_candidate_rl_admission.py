import json
from pathlib import Path

import pytest

from tools.proof_candidate_rl import validate_frozen_tasks
from tools.proof_candidate_rl_admission import build


def _task(i=0):
    return {
        "id": f"train-{i}",
        "prefix": "---- MODULE M ----\nTHEOREM Goal == TRUE\n",
        "suffix": "\n====\n",
        "theorem_name": "Goal",
        "target_goal": "Goal == TRUE",
        "dependencies": [],
        "dependency_sha256": {},
        "context": {"library_sha256": {}, "reference_fragment_used": False},
        "candidates": ["BY SMT", "BY DEF Goal"],
        "prompt": "Complete the fixed proof <PROOF_HOLE>",
    }


def test_pre_frozen_validation_rejects_development_and_answer_fields():
    tasks = [_task(i) for i in range(17)]
    validate_frozen_tasks(tasks)
    tasks[0]["reference_fragment"] = "OMITTED"
    with pytest.raises(ValueError, match="answer-bearing"):
        validate_frozen_tasks(tasks)

    tasks = [_task(i) for i in range(17)]
    tasks[0]["id"] = "crdt-type-step"
    with pytest.raises(ValueError, match="task id"):
        validate_frozen_tasks(tasks)


def test_pre_frozen_validation_rejects_non_by_candidates():
    tasks = [_task(i) for i in range(17)]
    tasks[0]["candidates"][0] = "OMITTED"
    with pytest.raises(ValueError, match="candidate language"):
        validate_frozen_tasks(tasks)


def test_real_manifest_admission_is_target_free_and_contract_checked(tmp_path: Path):
    manifest = Path("results/runs/proof-multistep-manifest-20260905-v2/manifest.json")
    summary = build(manifest, tmp_path / "packet", candidates=2, step_candidates=False)
    assert summary["manifest_sha256"] == "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
    assert summary["train_tasks"] == 17
    assert summary["candidate_contract_validated"] == 34
    packet = json.loads((tmp_path / "packet" / "frozen.json").read_text())
    assert len(packet) == 17
    assert all("reference_fragment" not in row for row in packet)
    assert "crdt-type-step" not in json.dumps(packet)
    assert all(not Path(path).is_absolute()
               for row in packet
               for path in [*row["dependencies"], *row["context"]["library_sha256"]])
