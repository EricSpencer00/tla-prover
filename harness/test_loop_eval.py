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


def test_chains_advance_in_lock_step(monkeypatch, tmp_path):
    """Round-major order: every live chain takes its round-r call before any
    chain takes round r+1. That is what lets the round's calls be issued
    concurrently while TLC stays serialized."""
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert [(r["round"], r["chain"]) for r in rows] == [
        (0, 0), (0, 1), (1, 0), (1, 1), (2, 0), (2, 1)]


def test_round0_of_every_chain_is_a_fresh_generation(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert m.prompts[1] == m.prompts[0]        # chain 1 also starts from scratch
    assert rows[1]["chain"] == 1 and rows[1]["round"] == 0
    assert rows[1]["parent_candidate_sha256"] is None
    assert rows[2]["parent_candidate_sha256"] == rows[0]["candidate_sha256"]


def test_repair_rounds_carry_the_diagnosis_into_the_prompt(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert "WHAT WENT WRONG" in m.prompts[2]   # first repair call
    assert "===BEGIN SPEC===" in m.prompts[2]
    assert m.prompts[0] != m.prompts[2]


def test_greedy_only_on_chain0_round0(monkeypatch, tmp_path):
    m = ScriptedModel([MODULE] * 6)
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert rows[0]["temperature"] == 0.0
    assert all(r["temperature"] == loop_eval.TEMPERATURE for r in rows[1:])


def test_extraction_failure_makes_the_chain_regenerate(monkeypatch, tmp_path):
    """A reply with no module leaves that chain nothing to repair, so its next
    round generates from scratch instead of stalling or spending a wasted call."""
    m = ScriptedModel(["no module here", MODULE, MODULE, MODULE, MODULE, MODULE])
    rows = _run(monkeypatch, tmp_path, m, ["fail:tlc=error"] * 6)
    assert rows[0]["verdict"] == "no_module_extracted"
    assert rows[2]["chain"] == 0 and rows[2]["round"] == 1
    assert rows[2]["rung_in"] == "generate"
    assert m.prompts[2] == m.prompts[0]


def test_concurrent_rounds_produce_the_same_ledger(monkeypatch, tmp_path):
    """GEN_EVAL_CONCURRENCY only overlaps network calls: row order, prompts and
    verdicts must be identical to the serial path."""
    m1 = ScriptedModel([MODULE] * 6)
    serial = _run(monkeypatch, tmp_path, m1, ["fail:tlc=error"] * 6)
    monkeypatch.setattr(loop_eval, "GEN_EVAL_CONCURRENCY", 8)
    m2 = ScriptedModel([MODULE] * 6)
    conc = _run(monkeypatch, tmp_path, m2, ["fail:tlc=error"] * 6)
    keys = ("chain", "round", "verdict", "prompt_sha256", "calls_used")
    assert [tuple(r[k] for k in keys) for r in serial] == \
           [tuple(r[k] for k in keys) for r in conc]
    assert m1.prompts == m2.prompts


# ------------------------------------------------- signature-rung fragment

def test_declaration_block_covers_extends_and_declarations():
    block = loop_eval.declaration_block(MODULE)
    assert "EXTENDS Naturals" in block and "MaxN" in block and "VARIABLE x" in block
    assert "Next ==" not in block          # stops at the declarations


def test_signature_rung_falls_back_to_the_declaration_block():
    """`signature` failures have no error location to point at -- the identifier
    is missing -- so an empty fragment would waste 20% of the loop's feedback."""
    p = loop_eval.build_loop_repair_prompt("d", "s", "Counter", MODULE,
                                           "signature", "MISSING: Safety", "")
    assert "module header" in p and "VARIABLE x" in p


def test_other_rungs_keep_the_explicit_no_localization_note():
    p = loop_eval.build_loop_repair_prompt("d", "s", "Counter", MODULE,
                                           "sany", "boom", "")
    assert "did not localize" in p


def test_a_real_fragment_is_never_replaced():
    p = loop_eval.build_loop_repair_prompt("d", "s", "Counter", MODULE,
                                           "signature", "MISSING: Safety",
                                           "(lines 3-5)\nreal fragment")
    assert "real fragment" in p and "module header" not in p


def test_init_violation_hint_is_flag_gated(monkeypatch):
    """Arm A6 (docs/RALPH_STAIRCASE.md it3): when TLC rejects the INITIAL state,
    the models' shared mistake on holdout 121/135/141 is an unguarded
    postcondition (canonical specs write `pc = "Done" => ...`). With
    TLA_LOOP_INIT_HINT=1 the evidence gains one guidance line; without the
    flag the evidence is byte-identical to the frozen behavior."""
    log = 'Error: Invariant Correctness is violated by the initial state:\n/\\ pc = "L3"'
    row = _row(tlc="fail_invariant", verdict="fail:tlc=fail_invariant")

    monkeypatch.delenv("TLA_LOOP_INIT_HINT", raising=False)
    rung, ev = loop_eval.diagnose(row, MODULE, CFG, "Counter", log)
    assert rung == "tlc_violation" and "every state" not in ev

    monkeypatch.setenv("TLA_LOOP_INIT_HINT", "1")
    rung2, ev2 = loop_eval.diagnose(row, MODULE, CFG, "Counter", log)
    assert rung2 == "tlc_violation"
    assert "every state" in ev2 and "pc =" in ev2
    assert ev2.startswith(ev)  # hint appends; frozen evidence unchanged

    # a violation found later in the search (not at init) gets no hint
    log2 = "Error: Invariant TypeOK is violated.\nState 7:"
    _, ev3 = loop_eval.diagnose(row, MODULE, CFG, "Counter", log2)
    assert "every state" not in ev3


def test_resumed_run_skips_ledger_solved_specs(tmp_path):
    """A restarted loop run must not spend calls on a spec whose ledger already
    holds a pass: stop-on-first-pass only fires on passes the live process
    sees, so without this a restart re-runs up to chains*rounds-1 samples of an
    already-solved spec (measured: specs 2/5/13 after the 2026-08-30 restart)."""
    p = tmp_path / "rows.jsonl"
    p.write_text(
        json.dumps({"spec": "2", "sample": "c0r0", "verdict": "pass"}) + "\n"
        + json.dumps({"spec": "5", "sample": "c0r0", "verdict": "fail:tlc=error"}) + "\n"
        + json.dumps({"spec": "13", "sample": "c1r2", "verdict": "api_error"}) + "\n"
    )
    assert loop_eval.ledger_solved_specs(p) == {"2"}
    assert loop_eval.ledger_solved_specs(tmp_path / "nope.jsonl") == set()


def test_init_hint_does_not_hardcode_a_terminal_state_literal(monkeypatch):
    """The candidates behind real init violations name their terminal pc state
    "done" (12), "Done" (9) or "terminated" (4) (it34). A hint hardcoding
    `pc = "Done"` invites a model whose state is "done" to copy the literal,
    producing a guard that never fires -- vacuously true, which the Rule-5 gate
    then rejects. The hint must point at the model's OWN terminal value."""
    monkeypatch.setenv("TLA_LOOP_INIT_HINT", "1")
    import importlib
    from harness import loop_eval as le
    importlib.reload(le)
    row = {"verdict": "fail", "sany": "pass", "tlc": "fail_invariant"}
    _, ev = le.diagnose(row, "", "", "M", "Invariant Foo is violated by the initial state.")
    assert "HINT:" in ev
    assert '"Done"' not in ev, "must not hardcode a terminal-state literal"
    assert "your" in ev.lower() or "whatever" in ev.lower()
