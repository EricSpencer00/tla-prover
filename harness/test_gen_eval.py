"""Tests for harness.gen_eval — E2.c Gate-2 baseline eval (PLAN Amendment 12).

Deterministic units (prompt build, cfg-signature parse, response parse, pass@k
aggregation) are tested here with no network. The Sophia sweep and oracle
scoring are exercised separately via the CLI with --model local-stub.
"""
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
