"""Tests for harness.gen_eval — E2.c Gate-2 baseline eval (PLAN Amendment 12).

Deterministic units (prompt build, cfg-signature parse, response parse, pass@k
aggregation) are tested here with no network. The Sophia sweep and oracle
scoring are exercised separately via the CLI with --model local-stub.
"""
from harness import gen_eval


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
