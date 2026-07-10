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


# --- stage_adequacy (W1 battery: re-derived states + mutation + structural) ----
#
# Real invariant so the mutation battery inside stage_adequacy has something to
# actually catch (mirrors test_mutation.py's SAFETY_SPEC): Dec's bound guard
# "x \in {0}" is the mutation site (in_to_notin flips it, letting x go negative
# and trip NonNegative).
_ADEQ_SPEC = """---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Dec == x \\in {0} \\/ x' = x - 1
Inc == x' = x + 1
Next == Dec \\/ Inc
Spec == Init /\\ [][Next]_x
NonNegative == x >= 0
====
"""
_ADEQ_CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"


def _build_adequacy_corpus(corpus_dir: Path, n: int = 1):
    """tier1_sany_cfg fixture specs under corpus_dir/tier1_sany_cfg/<name>/,
    matching stage_assemble's on-disk layout (source relative to data/raw/)."""
    rows = []
    for i in range(n):
        name = f"Counter{i}"
        d = corpus_dir / "tier1_sany_cfg" / name
        d.mkdir(parents=True)
        (d / f"{name}.tla").write_text(_ADEQ_SPEC.replace("Counter", name))
        (d / f"{name}.cfg").write_text(_ADEQ_CFG)
        rows.append({"source": f"data/raw/{name}/{name}.tla", "module": name,
                     "content_sha256": "deadbeef", "tier": "tier1_sany_cfg", "has_cfg": True})
    (corpus_dir / "manifest_tier1_sany_cfg.jsonl").write_text(
        "\n".join(json.dumps(r) for r in rows) + "\n")
    (corpus_dir / "manifest_tier3_tlc.jsonl").write_text("")
    return rows


def test_stage_adequacy_writes_expected_keys(tmp_path: Path):
    corpus_dir = tmp_path / "corpus"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    _build_adequacy_corpus(corpus_dir, n=1)

    wf.stage_adequacy(corpus_dir=corpus_dir, run_dir=run_dir, limit=None, timeout=30)

    rows = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows) == 1
    row = rows[0]
    for key in ("source", "module", "tier", "distinct_states", "vacuity",
                "safety_catch_rate", "quality_gold", "quality_fail_reasons",
                "complexity_score", "num_variables", "num_definitions"):
        assert key in row, key
    assert row["module"] == "Counter0"
    assert row["distinct_states"] is not None
    assert row["distinct_states"] >= 1


def test_stage_adequacy_resumable_skips_done_rows(tmp_path: Path):
    corpus_dir = tmp_path / "corpus"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    _build_adequacy_corpus(corpus_dir, n=2)

    wf.stage_adequacy(corpus_dir=corpus_dir, run_dir=run_dir, limit=None, timeout=30)
    rows_first = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows_first) == 2

    # re-run: no new rows should be appended (resumable, keyed by "source")
    wf.stage_adequacy(corpus_dir=corpus_dir, run_dir=run_dir, limit=None, timeout=30)
    rows_second = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows_second) == 2
    assert {r["source"] for r in rows_second} == {r["source"] for r in rows_first}


def test_stage_adequacy_respects_limit(tmp_path: Path):
    corpus_dir = tmp_path / "corpus"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    _build_adequacy_corpus(corpus_dir, n=3)

    wf.stage_adequacy(corpus_dir=corpus_dir, run_dir=run_dir, limit=1, timeout=30)
    rows = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows) == 1


# --- stage_quality_manifest (join adequacy.jsonl onto ALL 949, incl. tier2) ---

def test_stage_quality_manifest_covers_all_tiers(tmp_path: Path):
    corpus_dir = tmp_path / "corpus"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    corpus_dir.mkdir(parents=True)

    (corpus_dir / "manifest_tier1_sany_cfg.jsonl").write_text(
        json.dumps({"source": "data/raw/a.tla", "module": "A", "tier": "tier1_sany_cfg"}) + "\n")
    (corpus_dir / "manifest_tier2_sany.jsonl").write_text(
        json.dumps({"source": "data/raw/b.tla", "module": "B", "tier": "tier2_sany"}) + "\n")
    (corpus_dir / "manifest_tier3_tlc.jsonl").write_text(
        json.dumps({"source": "data/raw/c.tla", "module": "C", "tier": "tier3_tlc"}) + "\n")

    # tier2 has no on-disk battery source text needed here -- stage_quality_manifest
    # computes structural_features straight from the on-disk copy, so give it one.
    for tier, name in (("tier1_sany_cfg", "a"), ("tier2_sany", "b"), ("tier3_tlc", "c")):
        d = corpus_dir / tier
        d.mkdir(parents=True)
        (d / f"{name}.tla").write_text(_ADEQ_SPEC.replace("Counter", name.upper()))

    (run_dir / "adequacy.jsonl").write_text(json.dumps({
        "source": "data/raw/a.tla", "module": "A", "tier": "tier1_sany_cfg",
        "distinct_states": 4, "vacuity": [], "safety_catch_rate": 0.5,
        "quality_gold": True, "quality_fail_reasons": [],
        "complexity_score": 1.0, "num_variables": 1,
    }) + "\n" + json.dumps({
        "source": "data/raw/c.tla", "module": "C", "tier": "tier3_tlc",
        "distinct_states": 2, "vacuity": ["thin_model"], "safety_catch_rate": 0.0,
        "quality_gold": False, "quality_fail_reasons": ["thin_model", "weak_mutation"],
        "complexity_score": 0.5, "num_variables": 1,
    }) + "\n")

    wf.stage_quality_manifest(corpus_dir=corpus_dir, run_dir=run_dir)

    out = corpus_dir / "manifest_tier_quality.jsonl"
    rows = [json.loads(l) for l in open(out)]
    assert len(rows) == 3
    by_source = {r["source"]: r for r in rows}

    assert by_source["data/raw/a.tla"]["quality_gold"] is True
    assert by_source["data/raw/c.tla"]["quality_gold"] is False

    b = by_source["data/raw/b.tla"]
    assert b["quality_gold"] is False
    assert b["quality_fail_reasons"] == ["no_cfg_no_battery"]
    assert b["safety_catch_rate"] is None
    assert b["distinct_states"] is None
    assert "complexity_score" in b
    assert "num_variables" in b
