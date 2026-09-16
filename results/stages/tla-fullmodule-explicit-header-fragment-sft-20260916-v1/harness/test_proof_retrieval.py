"""Tests for harness.proof_retrieval -- W3.3 retrieval-over-verified-proofs.

Uses a synthetic mini trace dir (a rows.jsonl written directly, matching the
schema documented in harness/proof_traces.py) rather than real tlapm output,
so these tests run without tlapm installed and without the real corpora.
"""
import json
from pathlib import Path

import pytest

from .proof_retrieval import build_index, load_index, query


def _write_rows(path: Path, rows):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w") as fh:
        for r in rows:
            fh.write(json.dumps(r) + "\n")


def _row(**overrides):
    row = {
        "source": "corpus",
        "module": "Mod",
        "module_path": "/nonexistent/Mod.tla",
        "module_id": "corpus-1",
        "theorem_kind": "LEMMA",
        "theorem_name": "TypeCorrect",
        "obligation_id": "1",
        "loc": "10:1:12:1",
        "obligation_text": "NEW VARIABLE x PROVE x \\in Nat",
        "backend": "zenon",
        "method": "time-limit: 10",
        "status": "proved",
    }
    row.update(overrides)
    return row


def test_build_index_keeps_only_proved(tmp_path):
    trace_dir = tmp_path / "trace1"
    _write_rows(trace_dir / "rows.jsonl", [
        _row(obligation_id="1", status="proved"),
        _row(obligation_id="2", status="failed"),
        _row(obligation_id="3", status="unattempted"),
        _row(obligation_id="4", status="proved", obligation_text=""),  # no tokens -> dropped
    ])
    out_path = tmp_path / "index.jsonl"
    entries = build_index([trace_dir], out_path)

    assert len(entries) == 1
    assert entries[0]["id"] == "corpus-1#1"
    assert entries[0]["backend"] == "zenon"
    assert out_path.exists()
    loaded = load_index(out_path)
    assert loaded == entries


def test_build_index_merges_multiple_trace_dirs(tmp_path):
    d1 = tmp_path / "d1"
    d2 = tmp_path / "d2"
    _write_rows(d1 / "rows.jsonl", [_row(module_id="corpus-1", obligation_id="1")])
    _write_rows(d2 / "rows.jsonl", [_row(module_id="examples-1", obligation_id="1", source="examples")])
    out_path = tmp_path / "index.jsonl"
    entries = build_index([d1, d2], out_path)
    assert {e["id"] for e in entries} == {"corpus-1#1", "examples-1#1"}


def test_build_index_missing_trace_dir_is_skipped(tmp_path):
    out_path = tmp_path / "index.jsonl"
    entries = build_index([tmp_path / "does-not-exist"], out_path)
    assert entries == []
    assert out_path.exists()
    assert load_index(out_path) == []


def test_build_index_recovers_by_facts_from_module_text(tmp_path):
    module_path = tmp_path / "Mod.tla"
    module_path.write_text(
        "\n".join([
            "---- MODULE Mod ----",
            "LEMMA TypeCorrect ==",
            "  ASSUME NEW VARIABLE x",
            "  PROVE x \\in Nat",
            "  BY DEF TypeOK",
            "===="
        ]) + "\n"
    )
    trace_dir = tmp_path / "trace"
    _write_rows(trace_dir / "rows.jsonl", [
        _row(module_path=str(module_path), loc="3:3:4:3"),
    ])
    out_path = tmp_path / "index.jsonl"
    entries = build_index([trace_dir], out_path)
    assert entries[0]["by_facts"] == ["BY DEF TypeOK"]


def test_build_index_by_facts_empty_when_module_missing(tmp_path):
    trace_dir = tmp_path / "trace"
    _write_rows(trace_dir / "rows.jsonl", [_row(module_path="/does/not/exist.tla")])
    out_path = tmp_path / "index.jsonl"
    entries = build_index([trace_dir], out_path)
    assert entries[0]["by_facts"] == []


def test_query_ranks_exact_duplicate_first(tmp_path):
    trace_dir = tmp_path / "trace"
    goal = "NEW VARIABLE x PROVE x \\in Nat /\\ x > 0 /\\ x < 100 /\\ x # 5"
    _write_rows(trace_dir / "rows.jsonl", [
        _row(module_id="corpus-1", obligation_id="1", obligation_text=goal),
        _row(module_id="corpus-1", obligation_id="2",
             obligation_text="NEW VARIABLE y PROVE y \\in Int /\\ y > 10 /\\ y < 20 /\\ y # 3"),
        _row(module_id="corpus-1", obligation_id="3",
             obligation_text="THEOREM Completely /\\ Unrelated => Goal \\/ Statement"),
    ])
    out_path = tmp_path / "index.jsonl"
    build_index([trace_dir], out_path)

    results = query(out_path, goal, k=5)
    assert results, "expected at least one match"
    assert results[0]["id"] == "corpus-1#1"
    assert results[0]["score"] == pytest.approx(1.0)
    # scores are sorted descending
    scores = [r["score"] for r in results]
    assert scores == sorted(scores, reverse=True)


def test_query_accepts_loaded_index_list(tmp_path):
    trace_dir = tmp_path / "trace"
    goal = "NEW VARIABLE x PROVE x \\in Nat"
    _write_rows(trace_dir / "rows.jsonl", [_row(obligation_text=goal)])
    out_path = tmp_path / "index.jsonl"
    build_index([trace_dir], out_path)
    loaded = load_index(out_path)

    results = query(loaded, goal, k=3)
    assert results[0]["id"] == "corpus-1#1"


def test_query_respects_k(tmp_path):
    trace_dir = tmp_path / "trace"
    goal = "NEW VARIABLE x PROVE x \\in Nat /\\ x > 0"
    rows = [
        _row(module_id="corpus-1", obligation_id=str(i),
             obligation_text=f"NEW VARIABLE x PROVE x \\in Nat /\\ x > {i}")
        for i in range(10)
    ]
    _write_rows(trace_dir / "rows.jsonl", rows)
    out_path = tmp_path / "index.jsonl"
    build_index([trace_dir], out_path)

    results = query(out_path, goal, k=3)
    assert len(results) <= 3


def test_query_no_match_returns_empty(tmp_path):
    trace_dir = tmp_path / "trace"
    _write_rows(trace_dir / "rows.jsonl", [
        _row(obligation_text="NEW VARIABLE x PROVE x \\in Nat /\\ x > 0 /\\ x < 5"),
    ])
    out_path = tmp_path / "index.jsonl"
    build_index([trace_dir], out_path)

    results = query(out_path, "THEOREM Zorro /\\ Batman => Superman \\/ Ironman", k=5)
    assert results == []


def test_query_empty_index_returns_empty(tmp_path):
    out_path = tmp_path / "index.jsonl"
    build_index([tmp_path / "no-such-dir"], out_path)
    results = query(out_path, "NEW VARIABLE x PROVE x \\in Nat", k=5)
    assert results == []


def test_query_empty_obligation_text_returns_empty(tmp_path):
    trace_dir = tmp_path / "trace"
    _write_rows(trace_dir / "rows.jsonl", [_row()])
    out_path = tmp_path / "index.jsonl"
    build_index([trace_dir], out_path)
    assert query(out_path, "", k=5) == []
