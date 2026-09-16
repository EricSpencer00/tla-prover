"""Tests for harness.gate_check -- the re-score-from-rows.jsonl health gate."""
import json

import pytest

from harness.gate_check import gate_check


def _write(tmp_path, rows):
    d = tmp_path / "run"
    d.mkdir()
    (d / "rows.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    return d


def test_pass_at_k_from_rows_only(tmp_path):
    d = _write(tmp_path, [
        {"spec": "5", "sample": "greedy", "verdict": "fail:tlc=error"},
        {"spec": "5", "sample": "1", "verdict": "pass"},
        {"spec": "37", "sample": "greedy", "verdict": "pass"},
        {"spec": "37", "sample": "corruption", "verdict": "pass"},  # excluded
    ])
    rep = gate_check(d)
    assert rep["ok"]
    assert rep["pass_at_k"] == 2 and rep["pass_set"] == ["37", "5"]
    assert rep["rows_scored"] == 3  # corruption row excluded


def test_api_error_rate_trips(tmp_path):
    # the 2026-07-14 ctx-4096 signature: mass api_error 400s, run looks "done"
    d = _write(tmp_path, [{"spec": "5", "sample": str(i), "verdict": "api_error"}
                          for i in range(10)])
    rep = gate_check(d)
    assert not rep["ok"]
    assert "api_error" in rep["failures"][0]


def test_zero_rows_trips(tmp_path):
    d = _write(tmp_path, [])
    assert not gate_check(d)["ok"]


def test_missing_rows_file_raises(tmp_path):
    with pytest.raises(FileNotFoundError):
        gate_check(tmp_path)
