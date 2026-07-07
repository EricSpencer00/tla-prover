"""Tests for harness.gen_eval — E2.c Gate-2 baseline eval (PLAN Amendment 12).

Deterministic units (prompt build, cfg-signature parse, response parse, pass@k
aggregation) are tested here with no network. The Sophia sweep and oracle
scoring are exercised separately via the CLI with --model local-stub.
"""
import hashlib
import json

import pytest

from harness import gen_eval

REALISH_MODULE = """---- MODULE Counter ----
EXTENDS Naturals
VARIABLE x

Init == x = 0
Next == x' = x + 1
TypeOK == x \\in Nat
Safe == /\\ TypeOK
        /\\ x >= 0
====
"""


def test_required_signature_extracts_constants_spec_and_properties():
    cfg = (
        "CONSTANT\n"
        "  Clients = {c1,c2,c3}\n"
        "  Resources = {r1,r2}\n"
        "SPECIFICATION\n"
        "  Allocator\n"
        "PROPERTIES\n"
        "  SimpleAllocator\n"
    )
    sig = gen_eval.required_signature(cfg)
    assert sig["constants"] == ["Clients", "Resources"]
    assert sig["specification"] == "Allocator"
    assert sig["properties"] == ["SimpleAllocator"]
    assert sig["invariants"] == []
    assert sig["init"] is None
    assert sig["next"] is None


def test_required_signature_init_next_invariant_form():
    cfg = (
        "CONSTANT N = 3  \\* comment\n"
        "INIT Init\n"
        "NEXT Next\n"
        "INVARIANT TypeOK Safety\n"
    )
    sig = gen_eval.required_signature(cfg)
    assert sig["constants"] == ["N"]
    assert sig["init"] == "Init"
    assert sig["next"] == "Next"
    assert sig["invariants"] == ["TypeOK", "Safety"]
    assert sig["specification"] is None


def test_extract_module_from_fenced_response():
    resp = (
        "Here is the spec:\n"
        "```tla\n"
        "---- MODULE Foo ----\n"
        "EXTENDS Naturals\n"
        "Init == x = 0\n"
        "====\n"
        "```\n"
        "Hope that helps!\n"
    )
    mod = gen_eval.extract_module(resp)
    assert mod.startswith("---- MODULE Foo ----")
    assert mod.rstrip().endswith("====")
    assert "Hope that helps" not in mod
    assert "```" not in mod


def test_extract_module_unfenced_and_missing():
    resp = "---- MODULE Bar ----\nInit == TRUE\n===="
    assert gen_eval.extract_module(resp).startswith("---- MODULE Bar ----")
    assert gen_eval.extract_module("no module here at all") is None


def test_build_generation_prompt_includes_description_and_signature():
    description_json = {
        "system_overview": "A simple allocator that hands out resources to clients.",
        "state_variables": "unsat, alloc: mappings from client to requested/held resources.",
        "safety_properties": "No resource is double-allocated (mutual exclusion).",
    }
    cfg = (
        "CONSTANT\n"
        "  Clients = {c1,c2,c3}\n"
        "  Resources = {r1,r2}\n"
        "SPECIFICATION\n"
        "  Spec\n"
        "INVARIANT\n"
        "  TypeOK Mutex\n"
    )
    prompt = gen_eval.build_generation_prompt(description_json, cfg, "SimpleAllocator")
    # description content is present
    assert "A simple allocator that hands out resources to clients." in prompt
    assert "No resource is double-allocated (mutual exclusion)." in prompt
    # required signature (computed from cfg) is present
    sig = gen_eval.required_signature(cfg)
    assert "Clients" in prompt and "Resources" in prompt
    assert sig["specification"] in prompt
    assert "TypeOK" in prompt and "Mutex" in prompt
    # module-naming instructions target extract_module's expected wrapper
    assert "SimpleAllocator" in prompt
    assert "---- MODULE" in prompt
    assert "====" in prompt


def test_build_generation_prompt_module_name_is_exact_target():
    description_json = {"system_overview": "Trivial counter."}
    cfg = "INIT\n  Init\nNEXT\n  Next\n"
    prompt = gen_eval.build_generation_prompt(description_json, cfg, "Counter")
    assert "Counter" in prompt
    # sanity: a model following instructions would produce something extract_module parses
    fake_reply = f"---- MODULE Counter ----\nInit == TRUE\nNext == TRUE\n===="
    mod = gen_eval.extract_module(fake_reply)
    assert mod is not None and "Counter" in mod


def test_build_repair_prompt_includes_spec_and_error_evidence():
    broken_module = "---- MODULE Foo ----\nInit == x = 0\nNext == x' = x + 1\n===="
    error_evidence = (
        "===== SANY (fail) =====\n"
        "line 3, col 5: Unknown operator y\n"
    )
    prompt = gen_eval.build_repair_prompt(broken_module, error_evidence)
    assert broken_module in prompt
    assert "Unknown operator y" in prompt
    assert "Foo" in prompt


def test_summarize_passk_counts_greedy_and_any():
    # per spec: (greedy_pass, [sample passes...])
    results = {
        "8":  {"greedy": True,  "samples": [False, True, False]},
        "10": {"greedy": False, "samples": [False, False, True]},   # only best-of-N
        "22": {"greedy": False, "samples": [False, False, False]},  # never
    }
    s = gen_eval.summarize_passk(results, k=3)
    assert s["pass@1"] == 1       # only spec 8 greedy-passed
    assert s["pass@3"] == 2       # specs 8 and 10 have some sample pass
    assert s["n"] == 3
    assert s["pass@1_specs"] == ["8"]
    assert s["pass@3_specs"] == ["8", "10"]


def test_corrupt_is_deterministic_for_same_seed():
    c1, r1 = gen_eval.corrupt(REALISH_MODULE, seed=42)
    c2, r2 = gen_eval.corrupt(REALISH_MODULE, seed=42)
    assert c1 == c2
    assert r1 == r2


def test_corrupt_different_seeds_usually_differ():
    seen = set()
    for seed in range(20):
        c, _ = gen_eval.corrupt(REALISH_MODULE, seed=seed)
        seen.add(c)
    # different seeds should not all collapse onto the same single mutation site
    assert len(seen) > 1


def test_corrupt_changes_exactly_one_site_and_record_matches():
    corrupted, record = gen_eval.corrupt(REALISH_MODULE, seed=7)
    assert corrupted != REALISH_MODULE
    # the record's offset/original/replacement must be consistent with the diff
    original_fragment = REALISH_MODULE[record["offset"]:record["offset"] + len(record["original"])]
    assert original_fragment == record["original"]
    reconstructed = (REALISH_MODULE[:record["offset"]] + record["replacement"]
                      + REALISH_MODULE[record["offset"] + len(record["original"]):])
    assert reconstructed == corrupted
    # exactly one mutation applied: reconstructing from the *other* direction
    # (corrupted with replacement swapped back to original at the recorded
    # offset) must reproduce the original exactly -- proving nothing else changed.
    undone = (corrupted[:record["offset"]] + record["original"]
              + corrupted[record["offset"] + len(record["replacement"]):])
    assert undone == REALISH_MODULE
    assert record["mutation"] in [label for label, _, _ in gen_eval.MUTATIONS]


def test_corrupt_no_candidates_raises():
    text_with_no_mutation_sites = "---- MODULE Empty ----\n====\n"
    with pytest.raises(gen_eval.NoCandidateMutation):
        gen_eval.corrupt(text_with_no_mutation_sites, seed=1)


def test_in_to_notin_mutation_does_not_touch_definition_delimiter():
    # Regression for the \in -> \notin operator added to close the
    # NoCandidateMutation gap on MC-stub/library holdout specs (13, 14, 105,
    # 106, 132, 133, 135, 181) that have no /\ or "n + m" site. The tricky
    # part: "\in" must never be confused with "==" (definition delimiter) --
    # they share no characters, but a naive "=" -> "#" mutation (tried and
    # dropped, see mutation.py) WOULD corrupt "==". This module has both a
    # "==" definition and a "\in" membership test with nothing else
    # mutation-eligible (no /\, no "n + m", no \cup), so seed=0 must pick
    # \in and must leave every "==" untouched.
    module = (
        "---- MODULE OnlyIn ----\n"
        "EXTENDS Naturals\n"
        "CONSTANT MaxNat\n"
        "ASSUME MaxNat \\in Nat\n"
        "NatOverride == 0 .. MaxNat\n"
        "====\n"
    )
    corrupted, record = gen_eval.corrupt(module, seed=0)
    assert record["mutation"] == "in_to_notin"
    assert record["original"] == "\\in"
    assert record["replacement"] == "\\notin"
    # every "==" definition delimiter survives untouched
    assert corrupted.count("==") == module.count("==")
    assert "NatOverride == 0 .. MaxNat" in corrupted
    # the membership test itself is negated
    assert "MaxNat \\notin Nat" in corrupted
    assert "MaxNat \\in Nat" not in corrupted


# ------------------------------------------------------ seed derivation

def test_holdout_specs_and_hash_matches_frozen_ledger_digest():
    # PLAN ledger entry 11 / E2C_HANDOFF.md record this exact digest for
    # corpus/holdout_30.json; it must never drift silently.
    specs, digest = gen_eval.holdout_specs_and_hash()
    assert digest == "ecfc20533b9dc9a6e727ab989732310659d469eefbcc3705df72e3094ef54f78"
    assert len(specs) == 30
    assert all(isinstance(s, str) for s in specs)


def test_corruption_seed_is_deterministic_and_spec_sensitive():
    h = "deadbeef" * 8
    s1 = gen_eval.corruption_seed(h, "2")
    s2 = gen_eval.corruption_seed(h, "2")
    s3 = gen_eval.corruption_seed(h, "5")
    assert s1 == s2
    assert s1 != s3
    assert s1 == int(hashlib.sha256(f"{h}:2".encode()).hexdigest()[:8], 16)


def test_corruption_seed_changes_with_holdout_hash():
    s_a = gen_eval.corruption_seed("aaaa", "2")
    s_b = gen_eval.corruption_seed("bbbb", "2")
    assert s_a != s_b


# ------------------------------------------------------ row/resume logic

def test_load_existing_rows_reads_spec_sample_pairs(tmp_path):
    p = tmp_path / "rows.jsonl"
    p.write_text(
        json.dumps({"spec": "2", "sample": "greedy", "verdict": "pass"}) + "\n"
        + json.dumps({"spec": "2", "sample": 1, "verdict": "fail:tlc=fail"}) + "\n"
    )
    done = gen_eval.load_existing_rows(p)
    assert done == {("2", "greedy"), ("2", 1)}


def test_load_existing_rows_missing_file_is_empty(tmp_path):
    assert gen_eval.load_existing_rows(tmp_path / "nope.jsonl") == set()


# ------------------------------------------------------ end-to-end dry run

class _FixedModel:
    """Deterministic model stub for tests: always emits the same fixed module
    reply, so extract_module/scoring/ledger logic is exercised without any
    real model or TLC call (eval_module_text itself is monkeypatched below)."""
    id = "test-fixed-v1"

    def __init__(self, reply):
        self.reply = reply

    def generate(self, prompt, n, temperature, max_tokens):
        return [self.reply] * n


def test_gen_eval_spec_framing_a_dry_run_with_monkeypatched_scoring(monkeypatch, tmp_path):
    reply = "---- MODULE Foo ----\nInit == x = 0\nNext == x' = x + 1\n===="

    def fake_eval_module_text(num, module_text, corpus, num2mod, mod2path, cfg_dirs,
                              workroot, logdir, timeout, stages, override_cfg=None,
                              log_name=None):
        log_path = logdir / (log_name or f"{num}.log")
        log_path.write_text("fake sany/tlc log\n")
        return {"spec": num, "sany": "pass", "tlc": "pass", "tlc_vacuity": "clean",
                "tlaps": None, "budget_used": {}, "log_path": str(log_path)}

    monkeypatch.setattr(gen_eval, "eval_module_text", fake_eval_module_text)

    logdir = tmp_path / "logs"
    logdir.mkdir()
    model = _FixedModel(reply)
    description_json = {"system_overview": "A trivial counter."}
    cfg_text = "INIT\n  Init\nNEXT\n  Next\n"

    rows = list(gen_eval.gen_eval_spec_framing_a(
        "999", description_json, cfg_text, "Foo", model, "test-run", 2,
        corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=set()))

    # greedy + k=2 samples = 3 rows total
    assert len(rows) == 3
    sample_ids = {r["sample"] for r in rows}
    assert sample_ids == {"greedy", 1, 2}
    for r in rows:
        assert r["framing"] == "A"
        assert r["spec"] == "999"
        assert r["model"] == "test-fixed-v1"
        assert r["verdict"] == "pass"
        assert "prompt_sha256" in r
        assert "timestamp" in r


def test_gen_eval_spec_framing_a_resume_skips_done_pairs(monkeypatch, tmp_path):
    reply = "---- MODULE Foo ----\nInit == x = 0\n===="

    def fake_eval_module_text(num, module_text, corpus, num2mod, mod2path, cfg_dirs,
                              workroot, logdir, timeout, stages, override_cfg=None,
                              log_name=None):
        log_path = logdir / (log_name or f"{num}.log")
        log_path.write_text("log\n")
        return {"spec": num, "sany": "pass", "tlc": "pass", "tlc_vacuity": "clean",
                "tlaps": None, "budget_used": {}, "log_path": str(log_path)}

    monkeypatch.setattr(gen_eval, "eval_module_text", fake_eval_module_text)
    logdir = tmp_path / "logs"
    logdir.mkdir()
    model = _FixedModel(reply)
    done = {("999", "greedy"), ("999", 1)}

    rows = list(gen_eval.gen_eval_spec_framing_a(
        "999", {"system_overview": "x"}, "INIT\n Init\n", "Foo", model, "test-run",
        2, corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=done))

    assert {r["sample"] for r in rows} == {2}


def test_gen_eval_spec_framing_b_records_mutation_and_seed(monkeypatch, tmp_path):
    reply = "---- MODULE OnlyIn ----\nEXTENDS Naturals\nCONSTANT MaxNat\n" \
            "ASSUME MaxNat \\in Nat\nNatOverride == 0 .. MaxNat\n===="

    def fake_eval_module_text(num, module_text, corpus, num2mod, mod2path, cfg_dirs,
                              workroot, logdir, timeout, stages, override_cfg=None,
                              log_name=None):
        log_path = logdir / (log_name or f"{num}.log")
        log_path.write_text("fake corrupted-spec sany/tlc failure log\n")
        return {"spec": num, "sany": "fail", "tlc": None, "tlc_vacuity": None,
                "tlaps": None, "budget_used": {}, "log_path": str(log_path)}

    monkeypatch.setattr(gen_eval, "eval_module_text", fake_eval_module_text)
    logdir = tmp_path / "logs"
    logdir.mkdir()
    model = _FixedModel(reply)
    corrupted = reply.replace("\\in", "\\notin")
    mutation_record = {"mutation": "in_to_notin", "offset": 60,
                       "original": "\\in", "replacement": "\\notin",
                       "candidate_index": 0, "seeded_index": 0,
                       "candidates_total": 1, "rejected": [],
                       "corrupted_verdict": "fail:sany=fail"}
    seed = gen_eval.corruption_seed("some-frozen-hash", "999")

    rows = list(gen_eval.gen_eval_spec_framing_b(
        "999", corrupted, mutation_record, seed, "sany error evidence", model,
        "test-run", 1, corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=set()))

    assert len(rows) == 2  # greedy + k=1
    for r in rows:
        assert r["framing"] == "B"
        assert r["mutation_record"]["mutation"] == "in_to_notin"
        assert r["seed"] == seed


# --------------------------------------------- candidate persistence (Rule 9)

def _fake_pass_eval_module_text(num, module_text, corpus, num2mod, mod2path,
                                cfg_dirs, workroot, logdir, timeout, stages,
                                override_cfg=None, log_name=None):
    log_path = logdir / (log_name or f"{num}.log")
    log_path.write_text("fake pass log\n")
    return {"spec": num, "sany": "pass", "tlc": "pass", "tlc_vacuity": "clean",
            "tlaps": None, "budget_used": {}, "log_path": str(log_path)}


def test_framing_a_persists_candidate_with_matching_sha(monkeypatch, tmp_path):
    reply = "---- MODULE Foo ----\nInit == x = 0\nNext == x' = x + 1\n===="
    monkeypatch.setattr(gen_eval, "eval_module_text", _fake_pass_eval_module_text)

    logdir = tmp_path / "logs"
    logdir.mkdir()
    candidates_dir = tmp_path / "candidates"
    model = _FixedModel(reply)

    rows = list(gen_eval.gen_eval_spec_framing_a(
        "999", {"system_overview": "x"}, "INIT\n Init\n", "Foo", model,
        "test-run", 0, corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=set(),
        candidates_dir=candidates_dir))

    assert len(rows) == 1  # greedy only (k=0)
    row = rows[0]
    expected_text = gen_eval.extract_module(reply)
    expected_path = candidates_dir / "999-A-greedy.tla"
    assert expected_path.exists()
    assert expected_path.read_text() == expected_text
    assert row["candidate_path"] == "candidates/999-A-greedy.tla"
    assert row["candidate_sha256"] == hashlib.sha256(expected_text.encode()).hexdigest()


def test_framing_a_extraction_failure_writes_response_txt(monkeypatch, tmp_path):
    reply = "I refuse to write a module today, sorry."
    monkeypatch.setattr(gen_eval, "eval_module_text", _fake_pass_eval_module_text)

    logdir = tmp_path / "logs"
    logdir.mkdir()
    candidates_dir = tmp_path / "candidates"
    model = _FixedModel(reply)

    rows = list(gen_eval.gen_eval_spec_framing_a(
        "999", {"system_overview": "x"}, "INIT\n Init\n", "Foo", model,
        "test-run", 0, corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=set(),
        candidates_dir=candidates_dir))

    assert len(rows) == 1
    row = rows[0]
    assert row["verdict"] == "no_module_extracted"
    expected_path = candidates_dir / "999-A-greedy.response.txt"
    assert expected_path.exists()
    assert expected_path.read_text() == reply
    # extraction failed -- nothing was scored, so no candidate fields on the row
    assert "candidate_path" not in row
    assert "candidate_sha256" not in row


def test_framing_b_persists_candidate_for_both_greedy_and_sample(monkeypatch, tmp_path):
    reply = "---- MODULE OnlyIn ----\nEXTENDS Naturals\nCONSTANT MaxNat\n" \
            "ASSUME MaxNat \\in Nat\nNatOverride == 0 .. MaxNat\n===="
    monkeypatch.setattr(gen_eval, "eval_module_text", _fake_pass_eval_module_text)
    logdir = tmp_path / "logs"
    logdir.mkdir()
    candidates_dir = tmp_path / "candidates"
    model = _FixedModel(reply)
    corrupted = reply.replace("\\in", "\\notin")
    mutation_record = {"mutation": "in_to_notin", "offset": 60,
                       "original": "\\in", "replacement": "\\notin",
                       "candidate_index": 0, "seeded_index": 0,
                       "candidates_total": 1, "rejected": [],
                       "corrupted_verdict": "fail:sany=fail"}
    seed = gen_eval.corruption_seed("some-frozen-hash", "999")

    rows = list(gen_eval.gen_eval_spec_framing_b(
        "999", corrupted, mutation_record, seed, "sany error evidence", model,
        "test-run", 1, corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=set(),
        candidates_dir=candidates_dir))

    assert len(rows) == 2  # greedy + k=1
    expected_text = gen_eval.extract_module(reply)
    expected_sha = hashlib.sha256(expected_text.encode()).hexdigest()
    by_sample = {r["sample"]: r for r in rows}
    for sample_id, fname in (("greedy", "999-B-greedy.tla"), (1, "999-B-1.tla")):
        r = by_sample[sample_id]
        path = candidates_dir / fname
        assert path.exists()
        assert path.read_text() == expected_text
        assert r["candidate_path"] == f"candidates/{fname}"
        assert r["candidate_sha256"] == expected_sha


def test_candidates_not_persisted_when_candidates_dir_omitted(monkeypatch, tmp_path):
    # Backward-compat / opt-in: callers that don't pass candidates_dir (e.g.
    # any future caller of these generators) must not have rows mutated with
    # candidate fields, and no candidates/ dir should be created as a side effect.
    reply = "---- MODULE Foo ----\nInit == x = 0\n===="
    monkeypatch.setattr(gen_eval, "eval_module_text", _fake_pass_eval_module_text)
    logdir = tmp_path / "logs"
    logdir.mkdir()
    model = _FixedModel(reply)

    rows = list(gen_eval.gen_eval_spec_framing_a(
        "999", {"system_overview": "x"}, "INIT\n Init\n", "Foo", model,
        "test-run", 0, corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=set()))

    assert "candidate_path" not in rows[0]
    assert not (tmp_path / "candidates").exists()


def test_framing_a_per_sample_log_paths_are_distinct(monkeypatch, tmp_path):
    reply = "---- MODULE Foo ----\nInit == x = 0\n===="
    captured = []

    def fake_eval_module_text(num, module_text, corpus, num2mod, mod2path,
                              cfg_dirs, workroot, logdir, timeout, stages,
                              override_cfg=None, log_name=None):
        captured.append((logdir, log_name))
        log_path = logdir / (log_name or f"{num}.log")
        log_path.write_text("log\n")
        return {"spec": num, "sany": "pass", "tlc": "pass", "tlc_vacuity": "clean",
                "tlaps": None, "budget_used": {}, "log_path": str(log_path)}

    monkeypatch.setattr(gen_eval, "eval_module_text", fake_eval_module_text)
    logdir = tmp_path / "logs"
    logdir.mkdir()
    model = _FixedModel(reply)

    list(gen_eval.gen_eval_spec_framing_a(
        "999", {"system_overview": "x"}, "INIT\n Init\n", "Foo", model,
        "test-run", 2, corpus=tmp_path, num2mod={}, mod2path={}, cfg_dirs=[],
        workroot=tmp_path / "work", logdir=logdir, done=set()))

    assert len(captured) == 3  # greedy + 2 samples
    log_names = [ln for _, ln in captured]
    assert len(set(log_names)) == 3  # all distinct -- no overwrite
    assert log_names == ["999-A-greedy.log", "999-A-1.log", "999-A-2.log"]


# --------------------------------------- corruption precondition (E2C §4.3)

def test_find_valid_corruption_accepts_seeded_candidate_when_valid():
    # REALISH_MODULE seeded pick must be accepted when it sany-parses and fails.
    def scorer(text):
        return {"sany": "pass"}, "fail:tlc=fail_invariant", "tlc log"
    corrupted, record, evidence = gen_eval.find_valid_corruption(
        REALISH_MODULE, seed=42, scorer=scorer)
    ref_corrupted, ref_record = gen_eval.corrupt(REALISH_MODULE, seed=42)
    assert corrupted == ref_corrupted  # first candidate tried == corrupt()'s pick
    assert record["mutation"] == ref_record["mutation"]
    assert record["offset"] == ref_record["offset"]
    assert record["candidate_index"] == record["seeded_index"]
    assert record["rejected"] == []
    assert record["corrupted_verdict"] == "fail:tlc=fail_invariant"
    assert evidence == "tlc log"


def test_find_valid_corruption_falls_back_past_sany_breaking_candidates():
    # first candidate breaks SANY -> must be rejected (reason recorded) and the
    # next candidate in rotation accepted.
    state = {"n": 0}

    def scorer(text):
        state["n"] += 1
        if state["n"] == 1:
            return {"sany": "fail"}, "fail:sany=fail", "sany parse error"
        return {"sany": "pass"}, "fail:tlc=fail_invariant", "tlc log"

    corrupted, record, evidence = gen_eval.find_valid_corruption(
        REALISH_MODULE, seed=42, scorer=scorer)
    assert corrupted is not None
    assert len(record["rejected"]) == 1
    assert record["rejected"][0]["reason"] == "sany_fail"
    assert record["candidate_index"] == \
        (record["seeded_index"] + 1) % record["candidates_total"]


def test_find_valid_corruption_rejects_still_passing_candidates():
    state = {"n": 0}

    def scorer(text):
        state["n"] += 1
        if state["n"] == 1:
            return {"sany": "pass"}, "pass", "clean tlc log"  # mutation is a no-op
        return {"sany": "pass"}, "fail:tlc=fail_invariant", "tlc log"

    corrupted, record, _ = gen_eval.find_valid_corruption(
        REALISH_MODULE, seed=42, scorer=scorer)
    assert corrupted is not None
    assert record["rejected"][0]["reason"] == "still_passes"


def test_find_valid_corruption_no_mutation_site():
    def scorer(text):
        raise AssertionError("scorer must not be called with zero candidates")
    corrupted, record, evidence = gen_eval.find_valid_corruption(
        "---- MODULE Empty ----\n====\n", seed=1, scorer=scorer)
    assert corrupted is None
    assert record["skip"] == "no_mutation_site"
    assert evidence is None


def test_find_valid_corruption_no_valid_candidate_returns_skip_record():
    def scorer(text):
        return {"sany": "fail"}, "fail:sany=fail", "parse error"
    corrupted, record, evidence = gen_eval.find_valid_corruption(
        REALISH_MODULE, seed=3, scorer=scorer)
    assert corrupted is None
    assert record["skip"] == "no_valid_corruption"
    assert record["candidates_total"] == len(record["rejected"])
    assert all(r["reason"] == "sany_fail" for r in record["rejected"])
    assert evidence is None


def test_find_valid_corruption_is_deterministic():
    def scorer(text):
        return {"sany": "pass"}, "fail:tlc=fail_invariant", "log"
    a = gen_eval.find_valid_corruption(REALISH_MODULE, seed=9, scorer=scorer)
    b = gen_eval.find_valid_corruption(REALISH_MODULE, seed=9, scorer=scorer)
    assert a == b


# ------------------------------------------------- canonical text (158/183)

def test_canonical_spec_text_reads_duplicate_numbered_specs(tmp_path):
    # Regression: specs 158/183 are byte-identical duplicates of 164/86 (same
    # module name -> mod2path keeps only one path per module name), so any
    # mod2path-based lookup loses them. canonical_spec_text must read
    # tla_files/{num}.tla directly.
    (tmp_path / "tla_files").mkdir()
    (tmp_path / "tla_files" / "158.tla").write_text("---- MODULE Voting ----\n====")
    (tmp_path / "tla_files" / "164.tla").write_text("---- MODULE Voting ----\n====")
    text = gen_eval.canonical_spec_text("158", tmp_path)
    assert "MODULE Voting" in text


def test_canonical_spec_text_missing_raises(tmp_path):
    (tmp_path / "tla_files").mkdir()
    with pytest.raises(FileNotFoundError):
        gen_eval.canonical_spec_text("120", tmp_path)


# --------------------------------------------- corruption cache + skip rows

def test_corruption_for_spec_caches_and_resumes(monkeypatch, tmp_path):
    calls = {"n": 0}

    def fake_score(num, text, corpus, num2mod, mod2path, cfg_dirs, workroot,
                   logdir, timeout):
        calls["n"] += 1
        return {"sany": "pass"}, "fail:tlc=fail_invariant", "tlc log"

    monkeypatch.setattr(gen_eval, "_score", fake_score)
    rundir = tmp_path / "run"
    rundir.mkdir()
    args = ("999", REALISH_MODULE, 42, rundir, None, {}, {}, [], None, None)

    c1, r1, e1 = gen_eval._corruption_for_spec(*args)
    n_after_first = calls["n"]
    assert c1 is not None and n_after_first >= 1
    assert (rundir / "corruptions" / "999.json").exists()

    # second call (resume): served from cache, zero additional scoring
    c2, r2, e2 = gen_eval._corruption_for_spec(*args)
    assert calls["n"] == n_after_first
    assert (c2, r2, e2) == (c1, r1, e1)


def test_corruption_for_spec_caches_skip_outcome(monkeypatch, tmp_path):
    def fake_score(num, text, corpus, num2mod, mod2path, cfg_dirs, workroot,
                   logdir, timeout):
        return {"sany": "fail"}, "fail:sany=fail", "parse error"

    monkeypatch.setattr(gen_eval, "_score", fake_score)
    rundir = tmp_path / "run"
    rundir.mkdir()
    args = ("999", REALISH_MODULE, 42, rundir, None, {}, {}, [], None, None)
    c, record, e = gen_eval._corruption_for_spec(*args)
    assert c is None and record["skip"] == "no_valid_corruption"
    # cached skip survives resume
    monkeypatch.setattr(gen_eval, "_score",
                        lambda *a: (_ for _ in ()).throw(AssertionError("no rescore")))
    c2, record2, _ = gen_eval._corruption_for_spec(*args)
    assert c2 is None and record2["skip"] == "no_valid_corruption"


def test_run_gen_eval_framing_b_ledgers_skip_rows(monkeypatch, tmp_path):
    # A spec whose every corruption candidate breaks SANY must yield a
    # "skipped:no_valid_corruption" ROW in rows.jsonl, not a console-only skip.
    corpus = tmp_path / "corpus"
    (corpus / "tla_files").mkdir(parents=True)
    (corpus / "descriptions").mkdir()
    (corpus / "cfg").mkdir()
    (corpus / "tla_files" / "2.tla").write_text(REALISH_MODULE)

    def fake_score(num, text, corpus_, num2mod, mod2path, cfg_dirs, workroot,
                   logdir, timeout):
        return {"sany": "fail"}, "fail:sany=fail", "parse error"

    monkeypatch.setattr(gen_eval, "_score", fake_score)
    rundir = tmp_path / "results-run"
    monkeypatch.setattr(gen_eval, "REPO", tmp_path)  # results/runs under tmp
    monkeypatch.setattr(gen_eval, "HOLDOUT_FILE", tmp_path / "holdout.json")
    (tmp_path / "holdout.json").write_text(json.dumps({"holdout_specs": [2]}))

    gen_eval.run_gen_eval(corpus, "skiprow-test", "B", "local-stub", 1,
                          specs=["2"])

    rows_path = tmp_path / "results" / "runs" / "skiprow-test" / "rows.jsonl"
    rows = [json.loads(l) for l in rows_path.read_text().splitlines() if l]
    assert len(rows) == 1
    assert rows[0]["spec"] == "2"
    assert rows[0]["sample"] == "corruption"
    assert rows[0]["verdict"] == "skipped:no_valid_corruption"
    assert rows[0]["mutation_record"]["skip"] == "no_valid_corruption"
