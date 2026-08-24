"""Tests for harness.loop_eval -- framing L (verifier in the loop).

No network and no TLC: the model is a scripted stub and _score is monkeypatched,
so every test here pins CONTROL FLOW and BUDGET, which is what the framing-L
claim rests on. The signature checker's accuracy is not a unit-test claim -- it
was validated against 169 real TLC-passing candidates (0 false positives) and
192 real tlc=error candidates (27% caught with zero tool calls); see the module
docstring.
"""
import hashlib
import json

import pytest

from harness import loop_eval
from harness.gen_eval import build_generation_prompt

MODULE = """---- MODULE Counter ----
EXTENDS Naturals
CONSTANTS
    MaxN,     \\* an inline comment on a continuation line
    Start
VARIABLE x
Init == x = Start
Next == x' = x + 1
TypeOK == x \\in Nat
Spec == Init /\\ [][Next]_x
====
"""

CFG = ("CONSTANTS\n  MaxN = 3\n  Start = 0\n"
       "SPECIFICATION Spec\nINVARIANTS TypeOK\n")

DESC = {"description": "a counter"}


# ------------------------------------------------------- signature extraction

def test_multiline_constants_with_comments_are_declared():
    have = loop_eval.declared_and_defined(MODULE)
    assert have["MaxN"] == 0 and have["Start"] == 0
    assert have["Init"] == 0 and have["Spec"] == 0


def test_operator_arity_is_recorded():
    have = loop_eval.declared_and_defined("Foo(a, b) == a + b\nBar == 1\n")
    assert have["Foo"] == 2 and have["Bar"] == 0


def test_substitution_rhs_is_required_not_the_lhs():
    need = loop_eval.signature_requirements("CONSTANT\n  NumActors <- n\n")
    assert "n" in need and "NumActors" in need


def test_complete_module_has_no_missing_signature():
    assert loop_eval.missing_signature(MODULE, CFG) == []


def test_missing_identifier_is_reported():
    assert loop_eval.missing_signature(MODULE, CFG + "INVARIANT Safety\n") == ["Safety"]


def test_wrapper_supplied_name_is_not_missing():
    """Spec-168 shape: the .cfg substitutes `NumActors <- n` and `n` lives in the
    MC wrapper module, never in the candidate."""
    cfg = "CONSTANT\n  NumActors <- n\nSPECIFICATION Spec\n"
    mod = "---- MODULE R ----\nCONSTANTS NumActors\nSpec == TRUE\n====\n"
    assert loop_eval.missing_signature(mod, cfg) == ["n"]
    assert loop_eval.missing_signature(mod, cfg, wrapper_text="n == 3\n") == []


# ------------------------------------------------------------------ diagnosis

def _row(**kw):
    base = {"sany": "pass", "tlc": None, "verdict": "fail:tlc=error"}
    base.update(kw)
    return base


def test_pass_diagnoses_to_nothing():
    rung, ev = loop_eval.diagnose(_row(verdict="pass", tlc="pass"), MODULE, CFG,
                                  "Counter", "")
    assert rung is None and ev is None


def test_signature_outranks_sany():
    """A module that both fails to parse AND omits a required identifier is told
    about the identifier first: the parse error is often a downstream symptom."""
    rung, ev = loop_eval.diagnose(_row(sany="fail", verdict="fail:sany=fail"),
                                  MODULE, CFG + "INVARIANT Safety\n", "Counter",
                                  "some sany error")
    assert rung == "signature" and "Safety" in ev


def test_sany_outranks_tlc():
    rung, _ = loop_eval.diagnose(_row(sany="fail", verdict="fail:sany=fail"),
                                 MODULE, CFG, "Counter", "parse error here")
    assert rung == "sany"


def test_violation_and_error_are_distinguished():
    r1, _ = loop_eval.diagnose(_row(tlc="fail_invariant",
                                    verdict="fail:tlc=fail_invariant"),
                               MODULE, CFG, "Counter", "Invariant TypeOK is violated.")
    r2, _ = loop_eval.diagnose(_row(tlc="error"), MODULE, CFG, "Counter", "Error: boom")
    assert r1 == "tlc_violation" and r2 == "tlc_error"


# ------------------------------------------------------------------- the loop

class ScriptedModel:
    """Returns replies in order; records every prompt it was given."""
    id = "scripted"

    def __init__(self, replies):
        self.replies = list(replies)
        self.prompts = []

    def generate_traced(self, prompt, n, temperature, max_tokens, seed=None):
        self.prompts.append(prompt)
        reply = self.replies.pop(0) if self.replies else self.replies_default()
        return [(reply, {"decode_seed": seed})]

    def replies_default(self):
        return MODULE


def _run(monkeypatch, tmp_path, model, verdicts, chains=2, rounds=3):
    """Drive loop_eval_spec with a scripted scorer. verdicts is consumed in order."""
    seq = list(verdicts)

    def fake_score(num, text, *a, **kw):
        v = seq.pop(0) if seq else "fail:tlc=error"
        row = {"spec": num, "sany": "pass" if not v.startswith("fail:sany") else "fail",
               "tlc": "pass" if v == "pass" else "error", "tlaps": None,
               "tlc_vacuity": "clean" if v == "pass" else None,
               "budget_used": {}, "log_path": str(tmp_path / "x.log")}
        return row, v, "Error: scripted"

    monkeypatch.setattr(loop_eval, "_score", fake_score)
    return list(loop_eval.loop_eval_spec(
        "2", DESC, CFG, "Counter", model, "run", tmp_path, {}, {},
        [("draft", tmp_path)], tmp_path, tmp_path, set(), tmp_path / "cand",
        chains=chains, rounds=rounds))


def test_budget_is_exactly_chains_times_rounds_when_never_passing(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert len(rows) == 6                      # 2 chains x 3 rounds
    assert len(m.prompts) == 6
    assert rows[-1]["calls_used"] == 6


def test_loop_stops_on_first_pass(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error", "pass"])
    assert [r["verdict"] for r in rows] == ["fail:tlc=error", "pass"]
    assert rows[-1]["calls_used"] == 2
    assert len(m.prompts) == 2                 # budget not spent after a pass


def test_round0_prompt_is_byte_identical_to_framing_a(monkeypatch, tmp_path):
    """The comparability claim: an L round-0 draw and an A draw come from the same
    prompt, so their ledger prompt_sha256 must match."""
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    expect = hashlib.sha256(
        build_generation_prompt(DESC, CFG, "Counter").encode()).hexdigest()
    r0 = [r for r in rows if r["round"] == 0]
    assert len(r0) == 2 and all(r["prompt_sha256"] == expect for r in r0)


def test_repair_rounds_carry_the_diagnosis_into_the_prompt(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert "WHAT WENT WRONG" in m.prompts[1]
    assert "===BEGIN SPEC===" in m.prompts[1]
    assert m.prompts[0] != m.prompts[1]


def test_chain_1_round_0_is_a_fresh_generation_not_a_repair(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert m.prompts[3] == m.prompts[0]        # chain 1 restarts from scratch
    assert rows[3]["chain"] == 1 and rows[3]["round"] == 0
    assert rows[3]["parent_candidate_sha256"] is None


def test_greedy_only_on_the_first_chain(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert rows[0]["temperature"] == 0.0
    assert all(r["temperature"] == loop_eval.TEMPERATURE for r in rows[1:])


def test_extraction_failure_abandons_the_chain(monkeypatch, tmp_path):
    """A reply with no module ends that chain (nothing to repair) and the next
    chain restarts from generation -- the budget must never stall."""
    m = ScriptedModel(["no module here", MODULE, MODULE, MODULE])
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert rows[0]["verdict"] == "no_module_extracted"
    assert rows[1]["chain"] == 1 and rows[1]["round"] == 0
