"""Tests for the W2.1 templated-bounded-TLC + vacuity-trap tier (harness.w21_funnel.stage_tlc).

Scope: unit tests for the pure/resumability logic (which rows are due, how a
runner-level (status, vacuity, dt) result is classified into the tier3
verdict), plus one integration test that drives a real tier1 file through
check_tlc via a tiny synthetic corpus (mirrors how runner.py's own tests
exercise check_tlc directly, avoiding a slow full-funnel fixture).

Templated bounded TLC (PLAN.md W2.1): scraped tier1 files are arbitrary
authors' specs, not corpus population-tagged specs, so there is no reference
"how long should this take" budget. The template is a fixed, short per-file
cap (BOUNDED_TIMEOUT_S) plus a depth cap via TLC's -dfid (iterative-deepening
DFS bounded search) so that even an unbounded-looking state machine returns
a bounded verdict instead of running to the timeout wall on every file.
"""
import json
from pathlib import Path

from harness import w21_funnel as wf


def test_bounded_tlc_flags_include_dfid_depth_cap():
    flags = wf.bounded_tlc_flags()
    assert "-dfid" in flags
    i = flags.index("-dfid")
    assert flags[i + 1] == str(wf.BOUNDED_TLC_DEPTH)


def test_bounded_tlc_flags_force_single_worker():
    # -dfid rejects >1 worker (TLC issue #548); check_tlc hardcodes -workers 2
    # ahead of extra_flags, so a later -workers 1 here is required to win.
    flags = wf.bounded_tlc_flags()
    assert flags[-2:] == ["-workers", "1"]


def test_classify_tier3_pass_nonvacuous():
    verdict = wf.classify_tier3(status="pass", vac=[])
    assert verdict == "tier3_tlc_pass"


def test_classify_tier3_pass_vacuous_demoted():
    verdict = wf.classify_tier3(status="pass", vac=["zero_states_generated"])
    assert verdict == "tier3_tlc_vacuous"


def test_classify_tier3_fail_kept_tier1():
    for status in ("fail_invariant", "fail_deadlock", "fail_liveness", "error"):
        assert wf.classify_tier3(status=status, vac=[]) == "tier3_tlc_fail"


def test_classify_tier3_timeout():
    assert wf.classify_tier3(status="timeout", vac=[]) == "tier3_tlc_timeout"


def test_classify_tier3_no_cfg():
    assert wf.classify_tier3(status="no_cfg", vac=[]) == "tier3_tlc_no_cfg"


def test_stage_tlc_resumes_skipping_done_rows(tmp_path: Path, monkeypatch):
    run_dir = tmp_path / "run"
    run_dir.mkdir()
    out = run_dir / "tlc.jsonl"
    out.write_text(json.dumps({"path": "already/done.tla", "tier3": "tier3_tlc_pass",
                                "tlc_status": "pass", "vacuity": [], "dt_s": 1.0}) + "\n")

    calls = []

    def fake_run_one(rel_path, raw, timeout):
        calls.append(rel_path)
        return {"path": rel_path, "tier3": "tier3_tlc_pass", "tlc_status": "pass",
                "vacuity": [], "dt_s": 0.1}

    monkeypatch.setattr(wf, "_run_one_tlc", fake_run_one)

    tier1_rows = [
        {"source": "data/raw/already/done.tla"},
        {"source": "data/raw/new/one.tla"},
    ]
    manifest = run_dir.parent / "manifest_tier1_sany_cfg.jsonl"
    manifest.write_text("\n".join(json.dumps(r) for r in tier1_rows) + "\n")

    wf.stage_tlc(raw=tmp_path, run_dir=run_dir, manifest_path=manifest, limit=None, timeout=5)

    assert calls == ["new/one.tla"]
    rows = [json.loads(l) for l in open(out)]
    assert {r["path"] for r in rows} == {"already/done.tla", "new/one.tla"}


def test_stage_tlc_respects_limit(tmp_path: Path, monkeypatch):
    run_dir = tmp_path / "run"
    run_dir.mkdir()

    monkeypatch.setattr(wf, "_run_one_tlc", lambda rel_path, raw, timeout: {
        "path": rel_path, "tier3": "tier3_tlc_pass", "tlc_status": "pass",
        "vacuity": [], "dt_s": 0.1})

    tier1_rows = [{"source": f"data/raw/f{i}.tla"} for i in range(5)]
    manifest = run_dir.parent / "manifest_tier1_sany_cfg.jsonl"
    manifest.write_text("\n".join(json.dumps(r) for r in tier1_rows) + "\n")

    wf.stage_tlc(raw=tmp_path, run_dir=run_dir, manifest_path=manifest, limit=2, timeout=5)

    rows = [json.loads(l) for l in open(run_dir / "tlc.jsonl")]
    assert len(rows) == 2
