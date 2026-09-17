import json
from pathlib import Path

import pytest

from tools import proof_protected_symbolic_search as search


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "results/runs/proof-multistep-context-20260905-v1/manifest.json"


def test_protected_search_projects_only_answer_free_scaffolds():
    tasks, raw = search.load_tasks(MANIFEST)
    assert tuple(sorted(tasks)) == tuple(sorted(search.PROTECTED_IDS))
    assert search.sha(raw) == search.MANIFEST_SHA256
    source = {task["id"]: task for task in json.loads(MANIFEST.read_text())["tasks"]}
    for task in tasks.values():
        assert "reference_fragment" not in task
        assert task["split"] == "development"
        assert task["target_goal"] == source[task["id"]]["target_goal"]


def test_proposal_lattice_is_bounded_and_safe():
    tasks, _ = search.load_tasks(MANIFEST)
    for task in tasks.values():
        candidates = search.build_candidates(task)
        assert 1 <= len(candidates) <= 32
        assert all(candidate.startswith("BY ") for candidate in candidates)
        assert all("AXIOM" not in candidate and "OMITTED" not in candidate
                   for candidate in candidates)
    assert any("SumIsSumFunction" in candidate
               for candidate in search.build_candidates(tasks["crdt-sum-type-proof"]))
    assert any("SumType" in candidate
               for candidate in search.build_candidates(tasks["crdt-sum-zero-proof"]))


def test_forbidden_fields_fail_closed():
    with pytest.raises(ValueError, match="answer-bearing"):
        search.reject_forbidden({"reference_fragment": "BY SMT"})
    with pytest.raises(ValueError, match="answer-bearing"):
        search.reject_forbidden({"gate_claim": True})
