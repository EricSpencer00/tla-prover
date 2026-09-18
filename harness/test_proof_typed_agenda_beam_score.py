from __future__ import annotations

import json
from pathlib import Path

from tools import proof_typed_agenda_beam_score as beam


ROOT = Path(__file__).resolve().parents[1]


def test_beam_is_derived_from_worker_scores_and_is_bounded():
    path = ROOT / "results/runs/proof-typed-candidate-rank-20260917-v2/job-7630620/child_generations.json"
    rows = json.loads(path.read_text())
    indices = beam.top_indices(rows[0], 4)
    assert indices == [2, 1, 10, 9]
    assert len(indices) == 4


def test_beam_rejects_invalid_width():
    try:
        beam.top_indices({"scores": [0.0]}, 9)
    except ValueError as exc:
        assert "beam width" in str(exc)
    else:
        raise AssertionError("invalid beam width was accepted")
