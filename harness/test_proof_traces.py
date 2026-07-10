"""Tests for harness.proof_traces (W2.4).

parse_toolbox_stream / nearest_theorem_name are pure-string unit tests (fast,
no tlapm). run_proof_traces has one real-tlapm integration test against a
tiny two-theorem fixture (skipped if tlapm isn't built in this checkout, same
convention as harness/proof_tools.py's smoke check) to prove the end-to-end
wiring (workdir staging, rows.jsonl, summary) actually works against the real
tool, not just the parser.
"""
import json
import shutil
from pathlib import Path

import pytest

from harness import proof_traces
from harness.runner import TLAPM

# A captured --toolbox --printallobs transcript (trimmed) from running tlapm
# on tools/smoke/ProofSmoke.tla, 2026-07-08 -- see proof_traces.py docstring.
SAMPLE_STREAM = """\
@!!BEGIN
@!!type:obligation
@!!id:1
@!!loc:5:1:5:8
@!!status:to be proved
@!!obl:1 + 1 = 2

@!!END

@!!BEGIN
@!!type:obligation
@!!id:2
@!!loc:8:1:8:8
@!!status:to be proved
@!!obl:\\A p \\in BOOLEAN : p \\/ ~p

@!!END

@!!BEGIN
@!!type:obligationsnumber
@!!count:2
@!!END

@!!BEGIN
@!!type:obligation
@!!id:2
@!!loc:8:1:8:8
@!!status:normalized
@!!meth:time-limit: 5
@!!obl:\\A p \\in BOOLEAN : p \\/ ~p

@!!END

@!!BEGIN
@!!type:obligation
@!!id:2
@!!loc:8:1:8:8
@!!status:proved
@!!prover:smt
@!!meth:time-limit: 5; time-used: 0.0 (1%)
@!!already:false
@!!obl:
\\A p \\in BOOLEAN : p \\/ ~p

@!!END

@!!BEGIN
@!!type:obligation
@!!id:1
@!!loc:5:1:5:8
@!!status:proved
@!!prover:smt
@!!meth:time-limit: 5; time-used: 0.2 (4%)
@!!already:false
@!!obl:
1 + 1 = 2

@!!END
"""

FIXTURE_MOD = """---- MODULE TinyProof ----
EXTENDS Naturals, TLAPS

THEOREM OnePlusOne == 1 + 1 = 2
OBVIOUS

THEOREM Tautology == \\A p \\in BOOLEAN : p \\/ ~p
OBVIOUS

====
"""


def test_parse_toolbox_stream_keeps_terminal_status_per_id():
    obls = proof_traces.parse_toolbox_stream(SAMPLE_STREAM)
    assert len(obls) == 2
    by_id = {o["id"]: o for o in obls}
    assert by_id["1"]["status"] == "proved"
    assert by_id["1"]["prover"] == "smt"
    assert by_id["1"]["obl"] == "1 + 1 = 2"
    assert by_id["2"]["status"] == "proved"
    assert "BOOLEAN" in by_id["2"]["obl"]


def test_parse_toolbox_stream_no_obligations_block():
    assert proof_traces.parse_toolbox_stream("no toolbox markers here") == []


def test_nearest_theorem_name_attributes_by_preceding_declaration():
    kind, name = proof_traces.nearest_theorem_name(FIXTURE_MOD, 4)
    assert kind == "THEOREM"
    assert name == "OnePlusOne"
    kind2, name2 = proof_traces.nearest_theorem_name(FIXTURE_MOD, 7)
    assert name2 == "Tautology"


def test_nearest_theorem_name_before_any_theorem_returns_none():
    kind, name = proof_traces.nearest_theorem_name(FIXTURE_MOD, 1)
    assert kind is None and name is None


def test_summarize_counts_modules_and_obligations():
    module_rows = [
        {"module_id": "a", "status": "pass", "obligations": 2, "proved": 2},
        {"module_id": "b", "status": "partial", "obligations": 3, "proved": 1},
        {"module_id": "c", "status": "timeout", "obligations": 0, "proved": 0},
    ]
    s = proof_traces.summarize(module_rows)
    assert s["modules_attempted"] == 3
    assert s["obligations_total"] == 5
    assert s["obligations_proved"] == 3
    assert s["modules_status"] == {"pass": 1, "partial": 1, "timeout": 1}


def test_backend_discharge_rates_excludes_unattempted(tmp_path):
    rows_path = tmp_path / "rows.jsonl"
    rows = [
        {"status": "proved", "backend": "smt"},
        {"status": "proved", "backend": "smt"},
        {"status": "failed", "backend": "zenon"},
        {"status": "unattempted", "backend": None},
    ]
    rows_path.write_text("\n".join(json.dumps(r) for r in rows) + "\n")
    rates = proof_traces.backend_discharge_rates(rows_path)
    assert rates["smt"] == {"proved": 2, "total": 2}
    assert rates["zenon"] == {"proved": 0, "total": 1}
    assert "unknown" not in rates or rates.get("unknown", {"total": 0})["total"] == 0


@pytest.mark.skipif(not TLAPM.exists(), reason="tlapm not built in this checkout")
def test_run_proof_traces_end_to_end(tmp_path):
    src = tmp_path / "src"
    src.mkdir()
    tla_path = src / "TinyProof.tla"
    tla_path.write_text(FIXTURE_MOD)
    out_dir = tmp_path / "out"
    summary = proof_traces.run_proof_traces(
        out_dir, source="fixture", modules=[("TinyProof", tla_path, [])], timeout=60)
    assert summary["modules_attempted"] == 1
    assert summary["obligations_total"] == 2
    assert summary["obligations_proved"] == 2
    rows = [json.loads(l) for l in (out_dir / "rows.jsonl").read_text().splitlines()]
    assert len(rows) == 2
    names = {r["theorem_name"] for r in rows}
    assert names == {"OnePlusOne", "Tautology"}
    assert all(r["backend"] == "smt" for r in rows)
    assert all(r["status"] == "proved" for r in rows)
    assert all(r["source"] == "fixture" for r in rows)
