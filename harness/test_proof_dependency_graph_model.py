import json

import pytest

from tools.proof_dependency_graph_model import (
    HOLDOUT_IDS,
    TRAIN_IDS,
    candidate_atoms,
    graph_features,
    load_tasks,
)
from tools.proof_dependency_graph_independent_score import rank


def test_candidate_atoms_preserve_solver_and_order_without_answer_lookup():
    assert candidate_atoms("BY SMT, TypeOK, Next") == ("smt_facts", ("TypeOK", "Next"))
    assert candidate_atoms("BY SMT DEF vars, Init") == ("smt_def", ("vars", "Init"))
    assert candidate_atoms("BY DEF vars, Init") == ("def", ("vars", "Init"))
    with pytest.raises(ValueError):
        candidate_atoms("BY OMITTED")


def test_graph_features_are_identity_light_and_sensitive_to_connectivity():
    task = {
        "id": "x", "theorem_name": "Target",
        "prefix": "---- MODULE X -----\nA == x = y\nB == A /\\ z\nTHEOREM Target == B\n<1>1. TRUE\n",
        "suffix": "\n====\n", "dependencies": [],
    }
    graph = {"nodes": {
        "A": {"name": "A", "statement": "x = y", "provenance": "local"},
        "B": {"name": "B", "statement": "A /\\ z", "provenance": "local"},
    }, "edges": {"A": set(), "B": {"A"}}, "goal_nodes": {"B"},
             "library_sha256": {}}
    connected = graph_features(task, "BY SMT, B, A", graph)
    disconnected = graph_features(task, "BY SMT, A", graph)
    assert "graph:internal_edges:1" in connected
    assert "graph:internal_edges:0" in disconnected
    assert not any("reference" in item.lower() for item in connected)


def test_load_tasks_projects_exact_frozen_population_without_answer_fields():
    path = "results/runs/proof-multistep-context-20260905-v1/manifest.json"
    tasks = load_tasks(__import__("pathlib").Path(path))
    assert set(tasks) == TRAIN_IDS | HOLDOUT_IDS
    assert all(set(task) == {"id", "split", "theorem_name", "prefix", "suffix", "dependencies"}
               for task in tasks.values())
    assert not any("reference_fragment" in json.dumps(task) for task in tasks.values())


def test_independent_rank_uses_only_model_scores_and_stable_indices():
    task = {"id": "x", "theorem_name": "Target",
            "prefix": "---- MODULE X -----\nTHEOREM Target == TRUE\n<1>1. TRUE\n",
            "suffix": "\n====\n", "dependencies": []}
    graph = {"nodes": {}, "edges": {}, "goal_nodes": set(), "library_sha256": {}}
    model = {"bias": 0.0, "weights": {"solver:smt": 1.0}}
    rows = rank(task, ["BY SMT", "BY DEF A"], graph, model)
    assert [row["candidate_index"] for row in rows] == [0, 1]
