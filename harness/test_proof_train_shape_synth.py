import json
from pathlib import Path

import pytest

from tools import proof_train_shape_synth as synth


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-manifest-20260905-v2/manifest.json"


def test_development_answers_are_removed_before_generation():
    raw, train, development = synth.load_tasks(MANIFEST)
    assert len(train) == 17
    assert len(development) == 4
    assert all("reference_fragment" not in task for task in development)
    assert all(set(task) == {"id", "prefix", "suffix", "theorem_name", "dependencies"}
               for task in development)


def test_train_shapes_are_the_only_response_inventory():
    _, train, _ = synth.load_tasks(MANIFEST)
    counts = synth.train_shapes(train)
    assert sum(counts.values()) == 17
    assert counts.get("direct-def", 0) + counts.get("direct-defs", 0) + counts.get("hierarchical", 0) >= 1


def test_fixed_candidates_cover_all_development_scaffolds():
    _, train, development = synth.load_tasks(MANIFEST)
    plans = {task["id"]: synth.candidates(task, train) for task in development}
    assert set(plans) == {"crdt-type-step", "crdt-safety-step",
                          "crdt-sum-type-proof", "crdt-sum-zero-proof"}
    assert all(plans.values())
    assert any("TypeOK, Next, Increment, Gossip, vars" in c for c in plans["crdt-type-step"])
    assert any("SumFunctionZero" in c for c in plans["crdt-sum-zero-proof"])


def test_plan_is_deterministic_without_checker(monkeypatch, tmp_path):
    _, train, development = synth.load_tasks(MANIFEST)
    expected = {task["id"]: synth.candidates(task, train) for task in development}
    assert expected == {task["id"]: synth.candidates(task, train) for task in development}


def test_answer_field_guard_fails_closed():
    with pytest.raises(ValueError, match="answer-bearing"):
        synth.reject_answer_fields({"development": {"reference_fragment": "secret"}})
