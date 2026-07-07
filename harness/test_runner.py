"""Tests for harness.runner -- eval_spec (existing corpus-reading path, locked)
and eval_module_text (E2.c Task 2: injected-text scorer feeding the future
gen_eval generation/repair callers). No real TLC/SANY/TLAPS is run here --
check_sany/check_tlc/check_tlapm are monkeypatched so these tests are fast and
deterministic; the real tools are exercised via the CLI sweeps only.
"""
import json

import pytest

from harness import runner


def _make_corpus(tmp_path, specs):
    """specs: {num: {"text": ..., "cfg": ... (optional)}}. Builds a minimal
    corpus/{tla_files,cfg,descriptions} tree runner.build_module_index and
    run_sweep-style callers expect."""
    corpus = tmp_path / "corpus"
    (corpus / "tla_files").mkdir(parents=True)
    (corpus / "cfg").mkdir(parents=True)
    (corpus / "descriptions").mkdir(parents=True)
    for num, d in specs.items():
        (corpus / "tla_files" / f"{num}.tla").write_text(d["text"])
        (corpus / "descriptions" / f"{num}.json").write_text("{}")
        if "cfg" in d:
            (corpus / "cfg" / f"{num}.cfg").write_text(d["cfg"])
    return corpus


STATE_MACHINE_MOD = """---- MODULE Foo ----
VARIABLES x
Init == x = 0
Next == x' = x
Spec == Init /\\ [][Next]_x
TypeOK == x \\in {0}
====
"""

STATE_MACHINE_CFG = "SPECIFICATION Spec\nINVARIANT TypeOK\n"


@pytest.fixture
def patched_checkers(monkeypatch):
    """Monkeypatch the three tool-invoking checkers to canned pass results and
    record every call for assertion. Returns the shared calls dict."""
    calls = {"sany": [], "tlc": [], "tlapm": []}

    def fake_sany(tla_file, workdir, timeout):
        # snapshot name+text at call time: eval_spec/eval_module_text rmtree
        # the workdir before returning, so the Path itself is unreadable after.
        calls["sany"].append((tla_file, workdir, timeout,
                              tla_file.name, tla_file.read_text()))
        return "pass", "SANY ok\n", 0.1

    def fake_tlc(mod, cfg_text, workdir, timeout, extra_flags=(), jvm_flags=()):
        calls["tlc"].append((mod, cfg_text, workdir, timeout, extra_flags, jvm_flags))
        return "pass", [], "Model checking completed. No error has been found.\n", 0.2

    def fake_tlapm(tla_file, workdir, timeout=300):
        calls["tlapm"].append((tla_file, workdir, timeout))
        return "pass", 3, 3, "All 3 obligations proved\n", 0.3

    monkeypatch.setattr(runner, "check_sany", fake_sany)
    monkeypatch.setattr(runner, "check_tlc", fake_tlc)
    monkeypatch.setattr(runner, "check_tlapm", fake_tlapm)
    return calls


# --------------------------------------------------------- eval_spec (locked)

def test_eval_spec_existing_corpus_reading_behavior_unchanged(tmp_path, patched_checkers):
    corpus = _make_corpus(tmp_path, {"1": {"text": STATE_MACHINE_MOD, "cfg": STATE_MACHINE_CFG}})
    num2mod, mod2path = runner.build_module_index(corpus)
    workroot = tmp_path / "work"
    logdir = tmp_path / "logs"
    logdir.mkdir()
    cfg_dirs = [("override", tmp_path / "no_override_dir"), ("original", corpus / "cfg")]

    row = runner.eval_spec("1", corpus, num2mod, mod2path, cfg_dirs, workroot,
                           logdir, timeout=120, stages=["sany", "tlc", "tlaps"])

    assert row["method"] == "oracle"
    assert row["sany"] == "pass"
    assert row["tlc"] == "pass"
    assert row["tlc_vacuity"] == "clean"
    assert row["cfg_origin"] == "original"
    # tlaps stage is a no-op here: spec "1" is not in PROOF_MODULES
    assert row["tlaps"] is None
    assert (logdir / "1.log").exists()
    # the module text scored was read from the corpus tla_files path, not injected
    _, _, _, name_used, text_used = patched_checkers["sany"][0]
    assert name_used == "Foo.tla"
    assert text_used == STATE_MACHINE_MOD


def test_eval_spec_missing_tla_file_reports_no_tla_file(tmp_path, patched_checkers):
    corpus = _make_corpus(tmp_path, {})
    num2mod, mod2path = runner.build_module_index(corpus)
    row = runner.eval_spec("99", corpus, num2mod, mod2path, [], tmp_path / "work",
                           tmp_path, timeout=120, stages=["sany"])
    assert row["sany"] == "no_tla_file"
    assert not patched_checkers["sany"]  # never reached the checker


# ---------------------------------------------------- eval_module_text (new)

def test_eval_module_text_scores_injected_text_not_corpus_file(tmp_path, patched_checkers):
    # corpus's on-disk spec 1 is deliberately broken; the injected candidate is
    # a different (valid) module text for the same spec number -- eval_module_text
    # must check what's injected, not what's on disk.
    broken = "---- MODULE Foo ----\nthis is not valid TLA+\n===="
    corpus = _make_corpus(tmp_path, {"1": {"text": broken, "cfg": STATE_MACHINE_CFG}})
    num2mod, mod2path = runner.build_module_index(corpus)
    workroot = tmp_path / "work"
    logdir = tmp_path / "logs"
    logdir.mkdir()
    cfg_dirs = [("override", tmp_path / "no_override_dir"), ("original", corpus / "cfg")]

    row = runner.eval_module_text("1", STATE_MACHINE_MOD, corpus, num2mod, mod2path,
                                  cfg_dirs, workroot, logdir, timeout=120,
                                  stages=["sany", "tlc"])

    assert row["method"] == "injected"
    assert row["sany"] == "pass"
    assert row["tlc"] == "pass"
    assert row["tlc_vacuity"] == "clean"
    _, _, _, _, text_used = patched_checkers["sany"][0]
    assert text_used == STATE_MACHINE_MOD  # injected text, not `broken`


def test_eval_module_text_uses_reference_cfg_for_spec_by_default(tmp_path, patched_checkers):
    corpus = _make_corpus(tmp_path, {"1": {"text": STATE_MACHINE_MOD, "cfg": STATE_MACHINE_CFG}})
    num2mod, mod2path = runner.build_module_index(corpus)
    cfg_dirs = [("override", tmp_path / "no_override_dir"), ("original", corpus / "cfg")]
    (tmp_path / "logs2").mkdir()

    row = runner.eval_module_text("1", STATE_MACHINE_MOD, corpus, num2mod, mod2path,
                                  cfg_dirs, tmp_path / "work", tmp_path / "logs2",
                                  timeout=120, stages=["sany", "tlc"])

    assert row["cfg_origin"] == "original"
    _, cfg_text_used, _, _, _, _ = patched_checkers["tlc"][0]
    assert cfg_text_used == STATE_MACHINE_CFG


def test_eval_module_text_override_cfg_replaces_reference_cfg(tmp_path, patched_checkers):
    corpus = _make_corpus(tmp_path, {"1": {"text": STATE_MACHINE_MOD, "cfg": STATE_MACHINE_CFG}})
    num2mod, mod2path = runner.build_module_index(corpus)
    cfg_dirs = [("override", tmp_path / "no_override_dir"), ("original", corpus / "cfg")]
    override_cfg = "SPECIFICATION Spec\nINVARIANT TypeOK\nCONSTANT Extra = 1\n"
    (tmp_path / "logs3").mkdir()

    row = runner.eval_module_text("1", STATE_MACHINE_MOD, corpus, num2mod, mod2path,
                                  cfg_dirs, tmp_path / "work", tmp_path / "logs3",
                                  timeout=120, stages=["sany", "tlc"],
                                  override_cfg=override_cfg)

    assert row["cfg_origin"] == "override_injected"
    _, cfg_text_used, _, _, _, _ = patched_checkers["tlc"][0]
    assert cfg_text_used == override_cfg


def test_eval_module_text_log_name_overrides_default_log_filename(tmp_path, patched_checkers):
    # Default behavior (log_name omitted) is unchanged: log file is f"{num}.log".
    # Callers scoring multiple candidates for the same spec (gen_eval) pass a
    # distinct log_name so repeated calls don't overwrite each other's log.
    corpus = _make_corpus(tmp_path, {"1": {"text": STATE_MACHINE_MOD, "cfg": STATE_MACHINE_CFG}})
    num2mod, mod2path = runner.build_module_index(corpus)
    cfg_dirs = [("override", tmp_path / "no_override_dir"), ("original", corpus / "cfg")]
    logdir = tmp_path / "logs5"
    logdir.mkdir()

    row = runner.eval_module_text("1", STATE_MACHINE_MOD, corpus, num2mod, mod2path,
                                  cfg_dirs, tmp_path / "work", logdir,
                                  timeout=120, stages=["sany", "tlc"],
                                  log_name="1-B-3.log")

    assert row["log_path"] == str(logdir / "1-B-3.log")
    assert (logdir / "1-B-3.log").exists()
    assert not (logdir / "1.log").exists()


def test_eval_module_text_no_module_header_is_reported(tmp_path, patched_checkers):
    corpus = _make_corpus(tmp_path, {})
    num2mod, mod2path = runner.build_module_index(corpus)
    (tmp_path / "logs4").mkdir()
    row = runner.eval_module_text("1", "not a module at all", corpus, num2mod, mod2path,
                                  [], tmp_path / "work", tmp_path / "logs4",
                                  timeout=120, stages=["sany"])
    assert row["sany"] == "no_module_header"
    assert not patched_checkers["sany"]


def test_eval_module_text_dispatches_library_population_sany_only(tmp_path, patched_checkers, monkeypatch):
    corpus = _make_corpus(tmp_path, {"29": {"text": STATE_MACHINE_MOD, "cfg": STATE_MACHINE_CFG}})
    num2mod, mod2path = runner.build_module_index(corpus)
    monkeypatch.setattr(runner, "LIBRARIES", {"29"})
    (tmp_path / "logs5").mkdir()

    row = runner.eval_module_text("29", STATE_MACHINE_MOD, corpus, num2mod, mod2path,
                                  [("original", corpus / "cfg")], tmp_path / "work",
                                  tmp_path / "logs5", timeout=120,
                                  stages=["sany", "tlc", "tlaps"])

    assert row["sany"] == "pass"
    # library population: runner's stage dispatch is stage-driven, not
    # population-gated for tlc itself -- but the population criterion (verdict)
    # lives in repair.verdict_of/gen_eval scoring layers built on this row; here
    # we only assert the machinery that IS population-gated in eval_module_text
    # (tlaps only runs for PROOF_MODULES membership).
    assert row["tlaps"] is None
    assert not patched_checkers["tlapm"]


def test_eval_module_text_dispatches_proof_module_population_runs_tlaps(tmp_path, patched_checkers, monkeypatch):
    corpus = _make_corpus(tmp_path, {"67": {"text": STATE_MACHINE_MOD}})
    num2mod, mod2path = runner.build_module_index(corpus)
    monkeypatch.setattr(runner, "PROOF_MODULES", {"67"})
    (tmp_path / "logs6").mkdir()

    row = runner.eval_module_text("67", STATE_MACHINE_MOD, corpus, num2mod, mod2path,
                                  [], tmp_path / "work", tmp_path / "logs6",
                                  timeout=120, stages=["sany", "tlaps"])

    assert row["sany"] == "pass"
    assert row["tlaps"] == "pass"
    assert row["tlaps_obligations"] == "3/3"
    assert len(patched_checkers["tlapm"]) == 1


def test_eval_module_text_expected_violation_normalizes_tlc_status(tmp_path, patched_checkers, monkeypatch):
    corpus = _make_corpus(tmp_path, {"4": {"text": STATE_MACHINE_MOD, "cfg": STATE_MACHINE_CFG}})
    num2mod, mod2path = runner.build_module_index(corpus)
    monkeypatch.setattr(runner, "EXPECTED_VIOLATIONS", {"4": "TypeOK"})

    def fake_tlc_violated(mod, cfg_text, workdir, timeout, extra_flags=(), jvm_flags=()):
        return ("fail_invariant", [],
                "Invariant TypeOK is violated.\n1 states generated\n", 0.2)
    monkeypatch.setattr(runner, "check_tlc", fake_tlc_violated)
    (tmp_path / "logs7").mkdir()

    row = runner.eval_module_text("4", STATE_MACHINE_MOD, corpus, num2mod, mod2path,
                                  [("original", corpus / "cfg")], tmp_path / "work",
                                  tmp_path / "logs7", timeout=120,
                                  stages=["sany", "tlc"])

    assert row["tlc"] == "pass_expected_violation"
    assert row["expected_violation"] == "TypeOK"
    assert row["tlc_vacuity"] == "clean"


def test_eval_module_text_writes_local_deps_into_workdir(tmp_path, monkeypatch):
    dep_text = "---- MODULE Bar ----\nBarOp == TRUE\n====\n"
    main_text = "---- MODULE Foo ----\nEXTENDS Bar\nInit == TRUE\nNext == TRUE\n====\n"
    corpus = _make_corpus(tmp_path, {
        "1": {"text": main_text},
        "2": {"text": dep_text},
    })
    num2mod, mod2path = runner.build_module_index(corpus)

    seen_dep_present = {}

    def fake_sany(tla_file, workdir, timeout):
        # assert on the state of the workdir DURING the check, before cleanup
        seen_dep_present["Bar.tla"] = (workdir / "Bar.tla").exists()
        seen_dep_present["Bar.tla_text"] = (workdir / "Bar.tla").read_text() \
            if (workdir / "Bar.tla").exists() else None
        return "pass", "SANY ok\n", 0.1

    monkeypatch.setattr(runner, "check_sany", fake_sany)
    (tmp_path / "logs8").mkdir()

    workroot = tmp_path / "work"
    runner.eval_module_text("1", main_text, corpus, num2mod, mod2path, [],
                            workroot, tmp_path / "logs8", timeout=120,
                            stages=["sany"])

    assert seen_dep_present["Bar.tla"] is True
    assert seen_dep_present["Bar.tla_text"] == dep_text
    assert not (workroot / "1").exists()  # cleaned up after run
