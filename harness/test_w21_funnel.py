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
import inspect
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

# EXTENDS-dependency case: an _MC-style harness that EXTENDS a sibling base
# module (mirrors the real Paxos_MC/PaxosPlusCal, MultiPaxos_MC/MultiPaxos
# tier3 rows). The base carries the state machine; the _MC pulls it in. This
# only resolves under SANY if the sibling base .tla is co-located -- which it
# is in the raw scrape tree but NOT in the incomplete corpus copy tree.
_ADEQ_BASE = """---- MODULE CounterBase ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Inc == x' = x + 1
====
"""
# The harness EXTENDS the base (needs the sibling .tla to resolve) AND carries
# its own mutable content (Dec's "x \in {0}" guard) so the mutation battery has
# a real site: this exercises BOTH resolution paths -- SANY/TLC of the harness,
# and run_mutation_on_module copying the base sibling into the mutant workdir.
_ADEQ_MC = """---- MODULE CounterMC ----
EXTENDS CounterBase
Dec == x \\in {0} \\/ x' = x - 1
Next == Dec \\/ Inc
Spec == Init /\\ [][Next]_x
NonNegative == x >= 0
====
"""


def _build_adequacy_corpus(corpus_dir: Path, raw: Path, n: int = 1):
    """Lay out fixture specs the way the real funnel does: manifests live under
    corpus_dir (referencing data/raw/<path> sources), while the actual .tla/.cfg
    (and EXTENDS siblings) live in the raw scrape tree under raw/<path>. Returns
    the manifest rows."""
    rows = []
    for i in range(n):
        name = f"Counter{i}"
        d = raw / name
        d.mkdir(parents=True)
        (d / f"{name}.tla").write_text(_ADEQ_SPEC.replace("Counter", name))
        (d / f"{name}.cfg").write_text(_ADEQ_CFG)
        rows.append({"source": f"data/raw/{name}/{name}.tla", "module": name,
                     "content_sha256": "deadbeef", "tier": "tier1_sany_cfg", "has_cfg": True})
    (corpus_dir).mkdir(parents=True, exist_ok=True)
    (corpus_dir / "manifest_tier1_sany_cfg.jsonl").write_text(
        "\n".join(json.dumps(r) for r in rows) + "\n")
    (corpus_dir / "manifest_tier3_tlc.jsonl").write_text("")
    return rows


def test_stage_adequacy_writes_expected_keys(tmp_path: Path):
    corpus_dir = tmp_path / "corpus"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    _build_adequacy_corpus(corpus_dir, raw, n=1)

    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir, limit=None, timeout=30)

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


def test_stage_adequacy_resolves_extends_dependency_from_raw(tmp_path: Path):
    """Regression: an _MC spec that EXTENDS a sibling base module must resolve
    (SANY passes, TLC produces a real state count) because the base .tla is
    co-located in the raw tree. Before the fix this resolved against the corpus
    copy tree, where the base was absent -> SANY 'cannot find source file' ->
    distinct_states/safety_catch_rate both null (battery measured nothing)."""
    corpus_dir = tmp_path / "corpus"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)

    d = raw / "counterproj"
    d.mkdir(parents=True)
    (d / "CounterBase.tla").write_text(_ADEQ_BASE)
    (d / "CounterMC.tla").write_text(_ADEQ_MC)
    (d / "CounterMC.cfg").write_text(_ADEQ_CFG)

    corpus_dir.mkdir(parents=True)
    (corpus_dir / "manifest_tier1_sany_cfg.jsonl").write_text("")
    (corpus_dir / "manifest_tier3_tlc.jsonl").write_text(json.dumps({
        "source": "data/raw/counterproj/CounterMC.tla", "module": "CounterMC",
        "tier": "tier3_tlc", "has_cfg": True}) + "\n")

    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir, limit=None, timeout=30)

    rows = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows) == 1
    row = rows[0]
    assert row["module"] == "CounterMC"
    # The whole point: the sibling base module resolved, so SANY passed and TLC
    # actually ran to a real state count -- before the fix this was null because
    # SANY could not find CounterBase in the copy tree.
    assert row["distinct_states"] is not None
    assert row["distinct_states"] >= 1
    # This fixture's real TLC run lands at 1 distinct state (thin model), which
    # the W2.1 throughput fix's gate-ordering skip (mutation_skipped_disqualified)
    # now short-circuits before the mutation battery -- safety_catch_rate is None
    # by design here, not because dependency resolution failed. The mutation
    # battery's OWN EXTENDS-sibling-copy behavior is covered directly by
    # test_mutation.py::test_run_mutation_on_module_mutates_extends_parent.
    assert row["mutation_skipped_disqualified"] is True
    assert row["safety_catch_rate"] is None


def test_stage_adequacy_resumable_skips_done_rows(tmp_path: Path):
    corpus_dir = tmp_path / "corpus"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    _build_adequacy_corpus(corpus_dir, raw, n=2)

    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir, limit=None, timeout=30)
    rows_first = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows_first) == 2

    # re-run: no new rows should be appended (resumable, keyed by "source")
    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir, limit=None, timeout=30)
    rows_second = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows_second) == 2
    assert {r["source"] for r in rows_second} == {r["source"] for r in rows_first}


def test_stage_adequacy_respects_limit(tmp_path: Path):
    corpus_dir = tmp_path / "corpus"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    _build_adequacy_corpus(corpus_dir, raw, n=3)

    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir, limit=1, timeout=30)
    rows = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(rows) == 1


# --- FIX 3: TLC budget ------------------------------------------------------
#
# 472/779 specs returned distinct_states=null at 30s plain TLC. Experiment
# (8 previously-null tier3 specs) showed 90s plain TLC recovers real exact
# state counts while -dfid under-reports (Paxos_MC: plain90=87 states vs
# dfid=1). Chose: bump the default budget to 90s, keep UNBOUNDED plain TLC.

def test_adequacy_default_budget_is_90s():
    assert wf.ADEQUACY_TLC_TIMEOUT_S == 90
    # stage_adequacy's default must track the constant, not a hardcoded 30.
    assert inspect.signature(wf.stage_adequacy).parameters["timeout"].default == 90


def test_run_one_adequacy_uses_unbounded_plain_tlc(monkeypatch, tmp_path):
    # Regression: the battery TLC run must NOT pass -dfid (which under-counts
    # states, the exact failure that made tier3's own tlc_states_found useless).
    d = tmp_path / "raw" / "P"
    d.mkdir(parents=True)
    (d / "Counter.tla").write_text(_ADEQ_SPEC)
    (d / "Counter.cfg").write_text(_ADEQ_CFG)

    seen_flags = {}

    from harness import runner as rn

    def fake_check_tlc(mod, cfg_text, workdir, timeout, extra_flags=(), jvm_flags=()):
        seen_flags["extra"] = list(extra_flags)
        return "pass", [], "3 distinct states found", 0.1

    monkeypatch.setattr(rn, "check_tlc", fake_check_tlc)
    # run_mutation_on_module also calls check_tlc; stub it out entirely so we
    # isolate the state-count TLC call's flags.
    monkeypatch.setattr("harness.mutation.run_mutation_on_module",
                        lambda *a, **k: {"safety_catch_rate": None, "mutants": []})

    rec = {"source": "data/raw/P/Counter.tla", "module": "Counter", "tier": "tier3_tlc"}
    row = wf._run_one_adequacy(tmp_path / "raw", rec, timeout=90)
    assert seen_flags["extra"] == []          # plain, unbounded -- no -dfid
    assert row["distinct_states"] == 3


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


# --- W2.1 throughput fix: --workers parallelism + mutation gate-ordering ---

def test_stage_adequacy_parallel_matches_serial_rows(tmp_path: Path):
    """--workers>1 must produce the same SET of rows as serial (order is not
    guaranteed under a process pool -- tests compare as sets)."""
    corpus_dir = tmp_path / "corpus"
    raw = tmp_path / "raw"
    run_dir_serial = tmp_path / "run_serial"
    run_dir_parallel = tmp_path / "run_parallel"
    run_dir_serial.mkdir(parents=True)
    run_dir_parallel.mkdir(parents=True)
    _build_adequacy_corpus(corpus_dir, raw, n=4)

    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir_serial,
                       limit=None, timeout=30, workers=1)
    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir_parallel,
                       limit=None, timeout=30, workers=2)

    def _normalize(rows):
        return sorted(
            ({k: v for k, v in r.items() if k not in ("dt_s",)} for r in rows),
            key=lambda r: r["source"])

    serial_rows = [json.loads(l) for l in open(run_dir_serial / "adequacy.jsonl")]
    parallel_rows = [json.loads(l) for l in open(run_dir_parallel / "adequacy.jsonl")]
    assert len(serial_rows) == len(parallel_rows) == 4
    assert _normalize(serial_rows) == _normalize(parallel_rows)


def test_stage_adequacy_parallel_resumes_after_partial_ledger(tmp_path: Path):
    """Simulate a crash after 1/3 rows were flushed; a --workers>1 restart must
    only process the remaining 2 and end with exactly 3 total rows."""
    corpus_dir = tmp_path / "corpus"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    rows = _build_adequacy_corpus(corpus_dir, raw, n=3)

    # Pre-seed the ledger with one row already "done" (as if a prior chunk ran).
    partial_row = wf._run_one_adequacy(raw, rows[0], timeout=30)
    (run_dir / "adequacy.jsonl").write_text(json.dumps(partial_row) + "\n")

    wf.stage_adequacy(corpus_dir=corpus_dir, raw=raw, run_dir=run_dir,
                       limit=None, timeout=30, workers=2)

    out_rows = [json.loads(l) for l in open(run_dir / "adequacy.jsonl")]
    assert len(out_rows) == 3
    assert {r["source"] for r in out_rows} == {r["source"] for r in rows}


def test_run_one_adequacy_skips_mutation_when_vacuous(monkeypatch, tmp_path):
    """Gate-ordering fix: a vacuous spec is already disqualified from
    quality_gold, so the (expensive) mutation battery must not run at all."""
    d = tmp_path / "raw" / "V"
    d.mkdir(parents=True)
    (d / "Counter.tla").write_text(_ADEQ_SPEC)
    (d / "Counter.cfg").write_text(_ADEQ_CFG)

    from harness import runner as rn

    def fake_check_tlc(mod, cfg_text, workdir, timeout, extra_flags=(), jvm_flags=()):
        return "pass", ["no_invariant"], "5 distinct states found", 0.1

    def _boom(*a, **k):
        raise AssertionError("mutation battery must not run for a disqualified spec")

    monkeypatch.setattr(rn, "check_tlc", fake_check_tlc)
    monkeypatch.setattr("harness.mutation.run_mutation_on_module", _boom)

    rec = {"source": "data/raw/V/Counter.tla", "module": "Counter", "tier": "tier1_sany_cfg"}
    row = wf._run_one_adequacy(tmp_path / "raw", rec, timeout=30)

    assert row["mutation_skipped_disqualified"] is True
    assert row["safety_catch_rate"] is None
    assert row["quality_gold"] is False
    assert "vacuous" in row["quality_fail_reasons"]
    assert "weak_mutation" in row["quality_fail_reasons"]


def test_run_one_adequacy_skips_mutation_when_thin_model(monkeypatch, tmp_path):
    """Same gate-ordering fix, thin-model branch (distinct_states < 3, no vacuity
    flag from TLC itself)."""
    d = tmp_path / "raw" / "T"
    d.mkdir(parents=True)
    (d / "Counter.tla").write_text(_ADEQ_SPEC)
    (d / "Counter.cfg").write_text(_ADEQ_CFG)

    from harness import runner as rn

    def fake_check_tlc(mod, cfg_text, workdir, timeout, extra_flags=(), jvm_flags=()):
        return "pass", [], "2 distinct states found", 0.1

    def _boom(*a, **k):
        raise AssertionError("mutation battery must not run for a disqualified spec")

    monkeypatch.setattr(rn, "check_tlc", fake_check_tlc)
    monkeypatch.setattr("harness.mutation.run_mutation_on_module", _boom)

    rec = {"source": "data/raw/T/Counter.tla", "module": "Counter", "tier": "tier1_sany_cfg"}
    row = wf._run_one_adequacy(tmp_path / "raw", rec, timeout=30)

    assert row["mutation_skipped_disqualified"] is True
    assert row["safety_catch_rate"] is None
    assert row["distinct_states"] == 2
    assert row["quality_gold"] is False


def test_run_one_adequacy_runs_mutation_when_qualified(monkeypatch, tmp_path):
    """Non-vacuous, non-thin specs must still run the mutation battery (no
    regression from the gate-ordering skip)."""
    d = tmp_path / "raw" / "Q"
    d.mkdir(parents=True)
    (d / "Counter.tla").write_text(_ADEQ_SPEC)
    (d / "Counter.cfg").write_text(_ADEQ_CFG)

    from harness import runner as rn

    def fake_check_tlc(mod, cfg_text, workdir, timeout, extra_flags=(), jvm_flags=()):
        return "pass", [], "10 distinct states found", 0.1

    called = {}

    def fake_mutation(*a, **k):
        called["ran"] = True
        return {"safety_catch_rate": 0.9, "kill_rate": 0.9, "attempted": 2,
                "safety_killed": 2, "mutants": []}

    monkeypatch.setattr(rn, "check_tlc", fake_check_tlc)
    monkeypatch.setattr("harness.mutation.run_mutation_on_module", fake_mutation)

    rec = {"source": "data/raw/Q/Counter.tla", "module": "Counter", "tier": "tier1_sany_cfg"}
    row = wf._run_one_adequacy(tmp_path / "raw", rec, timeout=30)

    assert called.get("ran") is True
    assert row["mutation_skipped_disqualified"] is False
    assert row["safety_catch_rate"] == 0.9
    assert row["quality_gold"] is True


def test_run_one_adequacy_workdir_unique_under_same_module_name_collision(tmp_path):
    """Two different spec directories both declaring `MODULE Foo` must not
    cross-talk: each _run_one_adequacy call gets its own private tempdir, so
    running them "concurrently" (here: interleaved in-process) can't have one
    call's Foo.tla/Foo.cfg leak into the other's workdir."""
    raw = tmp_path / "raw"
    d1 = raw / "proj1"
    d2 = raw / "proj2"
    d1.mkdir(parents=True)
    d2.mkdir(parents=True)

    spec1 = _ADEQ_SPEC.replace("Counter", "Foo")
    spec2 = spec1.replace("x = 0", "x = 0  \\* proj2 variant")
    (d1 / "Foo.tla").write_text(spec1)
    (d1 / "Foo.cfg").write_text(_ADEQ_CFG)
    (d2 / "Foo.tla").write_text(spec2)
    (d2 / "Foo.cfg").write_text(_ADEQ_CFG)

    rec1 = {"source": "data/raw/proj1/Foo.tla", "module": "Foo", "tier": "tier1_sany_cfg"}
    rec2 = {"source": "data/raw/proj2/Foo.tla", "module": "Foo", "tier": "tier1_sany_cfg"}

    row1 = wf._run_one_adequacy(raw, rec1, timeout=30)
    row2 = wf._run_one_adequacy(raw, rec2, timeout=30)

    # Both ran to completion against their OWN source directory's Foo.tla/.cfg
    # (comment-only difference, so both still report the same real state count)
    # -- proving neither read/wrote the other's temp workdir.
    assert row1["source"] == "data/raw/proj1/Foo.tla"
    assert row2["source"] == "data/raw/proj2/Foo.tla"
    assert row1["distinct_states"] is not None
    assert row2["distinct_states"] is not None

    # Confirm the raw tree itself was never mutated by _run_one_adequacy (both
    # source files are untouched, proving each call worked in an isolated copy).
    assert (d1 / "Foo.tla").read_text() == spec1
    assert (d2 / "Foo.tla").read_text() == spec2
    assert not (d1 / "states").exists()
    assert not (d2 / "states").exists()
