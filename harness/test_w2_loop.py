"""Tests for harness.w2_loop -- the W2 Ralph-loop RFT generation sampler
(docs/superpowers/specs/2026-07-09-w21-quality-corpus-design.md, Workstream 2)
+ the 2026-07-10 audit-fix quality gates (mutation floor, invariant-fidelity
contract, liveness gate).

ALL model calls are mocked via a scripted FakeModel -- no live Sophia spend at
any point in this test module. Where a test needs a real SANY/TLC pass, a tiny
valid spec+cfg fixture is used directly (matching test_w21_funnel.py / test_
mutation.py convention); other tests monkeypatch the gate functions.
"""
import json
from pathlib import Path

import pytest

from harness import w2_loop as wl


# --------------------------------------------------------------------- fixtures

# A tiny real, valid TLA+ spec + cfg (mirrors test_w21_funnel.py's _ADEQ_SPEC):
# used for tests that exercise the real SANY/TLC/mutation gates end to end.
_GOOD_SPEC = """---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Dec == x > 0 /\\ x' = x - 1
Inc == x < 3 /\\ x' = x + 1
Next == Dec \\/ Inc
Spec == Init /\\ [][Next]_x
NonNegative == x >= 0
====
"""
_GOOD_CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"

_GOOD_REPLY = f"""Here is the module and config:

```tla
{_GOOD_SPEC}
```

```cfg
{_GOOD_CFG}
```
PROPERTY_INVARIANT: NonNegative
"""

# A spec with a syntax error (unbalanced conjunct) -- SANY fails. Still
# defines NonNegative so the (pre-SANY) invariant-fidelity gate passes and
# the SANY gate is what fires.
_BAD_SANY_SPEC = """---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
NonNegative == x >= 0
Next == x' = x +
====
"""

_BAD_SANY_REPLY = f"""```tla
{_BAD_SANY_SPEC}
```
```cfg
{_GOOD_CFG}
```
PROPERTY_INVARIANT: NonNegative
"""

# A genuinely vacuous spec that passes the static invariant-fidelity gates
# (invariant declared, defined, non-TypeOK-named) but whose invariant body is
# syntactically TRUE -> runner.vacuity_flags fires trivial_invariant at TLC.
_VACUOUS_SPEC = _GOOD_SPEC.replace("NonNegative == x >= 0", "AlwaysFine == TRUE")
_VACUOUS_CFG = "INIT Init\nNEXT Next\nINVARIANT AlwaysFine\n"
_VACUOUS_REPLY = f"""```tla
{_VACUOUS_SPEC}
```
```cfg
{_VACUOUS_CFG}
```
PROPERTY_INVARIANT: AlwaysFine
"""

_NL_BODY = ("A simple bounded counter system. The variable x starts at 0 and "
            "each step either increments or decrements it, guarded so it never "
            "decrements below zero.")
_NL_REPLY = (_NL_BODY + "\n\nSAFETY PROPERTY: the counter value x is always "
             "greater than or equal to zero.")
_NL_NO_PROP = _NL_BODY  # no SAFETY PROPERTY: section -> parse_nl must reject


class FakeModel:
    """Scripted Model: each call to generate() pops the next canned reply list
    off a queue (one list of n replies per call), in order. id is fixed so rows
    are reproducible."""
    id = "fake-test-model"

    def __init__(self, script):
        self.script = list(script)
        self.calls = []

    def generate(self, prompt, n, temperature, max_tokens):
        self.calls.append({"prompt": prompt, "n": n, "temperature": temperature,
                            "max_tokens": max_tokens})
        if not self.script:
            raise AssertionError("FakeModel script exhausted")
        replies = self.script.pop(0)
        return replies if isinstance(replies, list) else [replies] * n


# --------------------------------------------------------------------- prompts

def test_backtranslate_prompt_forbids_tla_syntax_and_includes_spec():
    p = wl.backtranslate_prompt(_GOOD_SPEC, _GOOD_CFG)
    assert "Counter" in p or "x = 0" in p
    assert "no TLA+" in p.lower() or "natural language" in p.lower()


def test_backtranslate_prompt_requires_safety_property_section():
    p = wl.backtranslate_prompt(_GOOD_SPEC, _GOOD_CFG)
    assert "SAFETY PROPERTY:" in p


def test_parse_nl_extracts_plain_text():
    nl = wl.parse_nl(_NL_REPLY)
    assert "counter" in nl.lower()
    assert "----" not in nl


def test_parse_nl_strips_markdown_fences():
    reply = f"Here's the description:\n\n```\n{_NL_REPLY}\n```\n"
    nl = wl.parse_nl(reply)
    assert "```" not in nl
    assert "counter" in nl.lower()


def test_parse_nl_missing_property_section_raises():
    with pytest.raises(wl.NLMissingProperty):
        wl.parse_nl(_NL_NO_PROP)


def test_generation_prompt_includes_nl_and_module_name():
    p = wl.generation_prompt(_NL_REPLY, "Counter7")
    assert "Counter7" in p
    assert "counter" in p.lower()


def test_generation_prompt_requires_property_invariant_line():
    p = wl.generation_prompt(_NL_REPLY, "Counter7")
    assert "PROPERTY_INVARIANT:" in p


def test_generation_prompt_includes_repair_context_when_given():
    p = wl.generation_prompt(_NL_REPLY, "Counter7", error_context="SANY: Parse error at line 5")
    assert "Parse error" in p


def test_extract_module_and_cfg_parses_both_blocks():
    mod, cfg = wl.extract_module_and_cfg(_GOOD_REPLY)
    assert mod is not None and "MODULE Counter" in mod
    assert cfg is not None and "INVARIANT" in cfg


def test_extract_module_and_cfg_missing_cfg_returns_none():
    reply = "```tla\n" + _GOOD_SPEC + "\n```\n"
    mod, cfg = wl.extract_module_and_cfg(reply)
    assert mod is not None
    assert cfg is None


def test_parse_property_invariant():
    assert wl.parse_property_invariant(_GOOD_REPLY) == "NonNegative"
    assert wl.parse_property_invariant("no such line here") is None


# --------------------------------------------------------------------- run_loop_for_seed

def test_run_loop_converges_first_iter(tmp_path):
    model = FakeModel([[_GOOD_REPLY]])
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert result["survived"] is True
    assert result["iters"] == 1
    assert result["distinct_states"] >= 1
    assert result["vacuity"] == []
    assert result["rejection_reason"] is None
    assert result["safety_catch_rate"] is not None
    assert result["reward_weight"] == pytest.approx(
        result["complexity_score"] * (1 + result["safety_catch_rate"]))
    assert result["property_invariant"] == "NonNegative"
    assert len(model.calls) == 1


def test_run_loop_converges_after_sany_repair_iter(tmp_path):
    model = FakeModel([[_BAD_SANY_REPLY], [_GOOD_REPLY]])
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert result["survived"] is True
    assert result["iters"] == 2
    assert len(model.calls) == 2
    # second call must carry SANY error evidence from iter 1 as repair context
    assert "sany" in model.calls[1]["prompt"].lower() or "error" in model.calls[1]["prompt"].lower()


def test_run_loop_exhausts_max_iters_rejected(tmp_path):
    model = FakeModel([[_BAD_SANY_REPLY]] * 3)
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=3)
    assert result["survived"] is False
    assert result["iters"] == 3
    assert result["rejection_reason"] is not None
    assert len(model.calls) == 3


def test_run_loop_vacuous_spec_rejected_but_iterates(tmp_path):
    # trivially-TRUE invariant on every iter -> exhausts max_iters,
    # rejection_reason names the vacuity (runner's trivial_invariant flag)
    model = FakeModel([[_VACUOUS_REPLY]] * 2)
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=2)
    assert result["survived"] is False
    assert result["iters"] == 2
    assert "vacu" in result["rejection_reason"].lower() or \
           "trivial" in result["rejection_reason"].lower()


def test_run_loop_no_module_in_reply_iterates_with_parse_error(tmp_path):
    model = FakeModel([["no module here, sorry"], [_GOOD_REPLY]])
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert result["survived"] is True
    assert result["iters"] == 2


# --------------------------------------------------------------------- FIX 1: mutation floor

def _mut_result(attempted, killed, safety_killed):
    return {"attempted": attempted, "killed": killed, "safety_killed": safety_killed,
            "kill_rate": round(killed / attempted, 2) if attempted else None,
            "safety_catch_rate": round(safety_killed / attempted, 2) if attempted else None,
            "mutants": []}


def test_mutation_floor_no_site_accepts(tmp_path, monkeypatch):
    monkeypatch.setattr(wl, "run_mutation_on_module", lambda *a, **k: _mut_result(0, 0, 0))
    model = FakeModel([[_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["mutation_evidence"] == "no_site"


def test_mutation_floor_typeok_only_rejects_and_iterates(tmp_path, monkeypatch):
    # every catch was TypeOK-style -> reject THIS candidate, feed evidence
    # back, iterate; second iter's battery finds a real safety catch -> accept.
    results = iter([_mut_result(2, 2, 0), _mut_result(2, 2, 1)])
    monkeypatch.setattr(wl, "run_mutation_on_module", lambda *a, **k: next(results))
    model = FakeModel([[_GOOD_REPLY], [_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["iters"] == 2
    assert r["mutation_evidence"] == "safety_catch"
    # repair context of the 2nd call names the gaming surface
    assert "invariant" in model.calls[1]["prompt"].lower()


def test_mutation_floor_typeok_only_exhausts_to_rejection(tmp_path, monkeypatch):
    monkeypatch.setattr(wl, "run_mutation_on_module", lambda *a, **k: _mut_result(2, 2, 0))
    model = FakeModel([[_GOOD_REPLY]] * 2)
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=2)
    assert r["survived"] is False
    assert r["rejection_reason"] == "typeok_only_invariant"


def test_mutation_floor_no_kill_accepts_with_tag(tmp_path, monkeypatch):
    # mutants ran, none killed: weak signal but NOT proof of gaming -- accept,
    # record. (This is also the reward-not-gate decision: catch rate 0 with no
    # kills at all does not reject.)
    monkeypatch.setattr(wl, "run_mutation_on_module", lambda *a, **k: _mut_result(3, 0, 0))
    model = FakeModel([[_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["mutation_evidence"] == "no_kill"
    assert r["safety_catch_rate"] == 0.0
    assert r["reward_weight"] == pytest.approx(r["complexity_score"] * 1.0)


def test_mutation_floor_safety_catch_accepts(tmp_path, monkeypatch):
    monkeypatch.setattr(wl, "run_mutation_on_module", lambda *a, **k: _mut_result(2, 2, 2))
    model = FakeModel([[_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["mutation_evidence"] == "safety_catch"
    assert r["safety_catch_rate"] == 1.0


# --------------------------------------------------------------------- FIX 2: cfg semantic-invariant gate

_TYPEOK_ONLY_CFG = "INIT Init\nNEXT Next\nINVARIANT TypeOK\n"
_TYPEOK_SPEC = _GOOD_SPEC.replace("NonNegative == x >= 0", "TypeOK == x \\in Int")
_TYPEOK_ONLY_REPLY = f"""```tla
{_TYPEOK_SPEC}
```
```cfg
{_TYPEOK_ONLY_CFG}
```
PROPERTY_INVARIANT: TypeOK
"""


def test_semantic_invariant_names():
    assert wl.semantic_invariant_names(_GOOD_CFG) == ["NonNegative"]
    assert wl.semantic_invariant_names(_TYPEOK_ONLY_CFG) == []
    assert wl.semantic_invariant_names("INIT Init\nNEXT Next\nINVARIANT TypeOK Safety\n") == ["Safety"]
    assert wl.semantic_invariant_names("INIT Init\nNEXT Next\n") == []


def test_cfg_only_typeok_invariant_rejected_and_iterates(tmp_path):
    model = FakeModel([[_TYPEOK_ONLY_REPLY], [_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["iters"] == 2
    p = model.calls[1]["prompt"].lower()
    assert "semantic" in p or "type" in p


def test_cfg_only_typeok_exhausts_to_rejection(tmp_path):
    model = FakeModel([[_TYPEOK_ONLY_REPLY]] * 2)
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=2)
    assert r["survived"] is False
    assert "typeok" in r["rejection_reason"].lower() or \
           "semantic" in r["rejection_reason"].lower()


# --------------------------------------------------------------------- FIX 3: NL<->invariant fidelity

_NO_PI_REPLY = f"""```tla
{_GOOD_SPEC}
```
```cfg
{_GOOD_CFG}
```
"""


def test_loop_property_invariant_missing_iterates(tmp_path):
    model = FakeModel([[_NO_PI_REPLY], [_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["iters"] == 2
    assert "PROPERTY_INVARIANT" in model.calls[1]["prompt"]


def test_loop_property_invariant_mismatch_iterates(tmp_path):
    # names an invariant that is not defined/checked
    bad = _NO_PI_REPLY + "PROPERTY_INVARIANT: SomethingElse\n"
    model = FakeModel([[bad], [_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["iters"] == 2


def test_loop_property_invariant_typeok_named_rejected(tmp_path):
    model = FakeModel([[_TYPEOK_ONLY_REPLY]] * 2)
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=2)
    assert r["survived"] is False


def test_loop_records_property_invariant_on_survivor(tmp_path):
    model = FakeModel([[_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["property_invariant"] == "NonNegative"


# --------------------------------------------------------------------- FIX 4: liveness gate

_LIVENESS_SPEC = _GOOD_SPEC.replace(
    "Spec == Init /\\ [][Next]_x",
    "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\nEventuallyPositive == <>(x > 0)")
_LIVENESS_UNCHECKED_REPLY = f"""```tla
{_LIVENESS_SPEC}
```
```cfg
{_GOOD_CFG}
```
PROPERTY_INVARIANT: NonNegative
"""
_LIVENESS_CHECKED_CFG = "SPECIFICATION Spec\nINVARIANT NonNegative\nPROPERTY EventuallyPositive\n"
_LIVENESS_CHECKED_REPLY = f"""```tla
{_LIVENESS_SPEC}
```
```cfg
{_LIVENESS_CHECKED_CFG}
```
PROPERTY_INVARIANT: NonNegative
"""


def test_uses_liveness_operators_detector():
    assert wl.uses_liveness_operators(_LIVENESS_SPEC) is True
    # bare [][Next]_x skeleton is NOT liveness; tuples <<x>> are not diamonds
    assert wl.uses_liveness_operators(_GOOD_SPEC) is False
    assert wl.uses_liveness_operators("v' = <<1, 2>>") is False


def test_liveness_unchecked_gate_fails_and_iterates(tmp_path):
    model = FakeModel([[_LIVENESS_UNCHECKED_REPLY], [_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["iters"] == 2
    assert "PROPERTY" in model.calls[1]["prompt"]


def test_liveness_unchecked_exhausts_to_rejection(tmp_path):
    model = FakeModel([[_LIVENESS_UNCHECKED_REPLY]] * 2)
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=2)
    assert r["survived"] is False
    assert r["rejection_reason"] == "liveness_unchecked"


def test_liveness_checked_survives_with_flag(tmp_path):
    model = FakeModel([[_LIVENESS_CHECKED_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=60, max_iters=8)
    assert r["survived"] is True
    assert r["liveness_checked"] is True


def test_safety_only_spec_has_liveness_checked_false(tmp_path):
    model = FakeModel([[_GOOD_REPLY]])
    r = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert r["survived"] is True
    assert r["liveness_checked"] is False


# --------------------------------------------------------------------- decontam_survivor

def test_decontam_survivor_rejects_near_dup():
    from harness.corpora import shingle_set, normalize_tla, SHINGLE_K
    canon = {"bench:Counter": shingle_set(normalize_tla(_GOOD_SPEC), SHINGLE_K)}
    verdict, score = wl.decontam_survivor(_GOOD_SPEC, canon)
    assert verdict == "rejected_contaminated"
    assert score >= wl.NEAR_DUP_THRESHOLD


def test_decontam_survivor_accepts_novel_spec():
    other = """---- MODULE Totally ----
EXTENDS Naturals
VARIABLE y
InitY == y = 5
NextY == y' = y + 3
SpecY == InitY /\\ [][NextY]_y
Bound == y < 1000
====
"""
    from harness.corpora import shingle_set, normalize_tla, SHINGLE_K
    canon = {"bench:Other": shingle_set(normalize_tla(other), SHINGLE_K)}
    verdict, score = wl.decontam_survivor(_GOOD_SPEC, canon)
    assert verdict == "clean"
    assert score < wl.NEAR_DUP_THRESHOLD


# --------------------------------------------------------------------- run_w2 (end to end, resumable)

def _write_seeds(path, n=2):
    rows = []
    for i in range(n):
        rows.append({
            "source": f"data/raw/proj/Counter{i}.tla",
            "module": f"Counter{i}", "tier": "tier1_sany_cfg",
            "distinct_states": 4, "complexity_score": 10.0,
            "safety_catch_rate": 0.5, "quality_gold": False,
            "reward_weight": 10.0,
            "features": {"num_variables": 1},
        })
    path.write_text("\n".join(json.dumps(r) for r in rows) + "\n")


def _write_raw_specs(raw, n=2):
    for i in range(n):
        d = raw / "proj"
        d.mkdir(parents=True, exist_ok=True)
        (d / f"Counter{i}.tla").write_text(_GOOD_SPEC.replace("Counter", f"Counter{i}"))
        (d / f"Counter{i}.cfg").write_text(_GOOD_CFG)


def test_run_w2_end_to_end_writes_ledgers(tmp_path, monkeypatch):
    seeds_path = tmp_path / "manifest_w2_seeds.jsonl"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    _write_seeds(seeds_path, n=2)
    _write_raw_specs(raw, n=2)

    # backtranslate reply then a converging generation reply, per seed
    good_reply_0 = _GOOD_REPLY.replace("Counter", "Counter0")
    good_reply_1 = _GOOD_REPLY.replace("Counter", "Counter1")
    model = FakeModel([
        [_NL_REPLY], [good_reply_0],
        [_NL_REPLY], [good_reply_1],
    ])

    wl.run_w2(model, seeds_path, raw, run_dir, seed_cap=None, k=1, timeout=30, max_iters=8)

    attempts = [json.loads(l) for l in open(run_dir / "w2_attempts.jsonl")]
    survivors = [json.loads(l) for l in open(run_dir / "w2_survivors.jsonl")]
    assert len(attempts) == 2
    assert len(survivors) == 2
    assert all("reward_weight" in s for s in survivors)
    assert all(s.get("property_invariant") == "NonNegative" for s in survivors)


def test_run_w2_nl_missing_property_records_skip(tmp_path):
    seeds_path = tmp_path / "manifest_w2_seeds.jsonl"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    _write_seeds(seeds_path, n=1)
    _write_raw_specs(raw, n=1)

    model = FakeModel([[_NL_NO_PROP]])  # backtranslation lacks SAFETY PROPERTY:
    wl.run_w2(model, seeds_path, raw, run_dir, seed_cap=None, k=1, timeout=30, max_iters=8)

    attempts = [json.loads(l) for l in open(run_dir / "w2_attempts.jsonl")]
    assert len(attempts) == 1
    assert attempts[0]["survived"] is False
    assert attempts[0]["rejection_reason"] == "nl_missing_property"
    # only the backtranslation call was spent; no generation iterations
    assert len(model.calls) == 1


def test_run_w2_resumable_skips_done_seed_k(tmp_path):
    seeds_path = tmp_path / "manifest_w2_seeds.jsonl"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    run_dir.mkdir(parents=True)
    _write_seeds(seeds_path, n=2)
    _write_raw_specs(raw, n=2)

    # pre-seed attempts ledger as if seed 0 (k=0) already ran
    (run_dir / "w2_attempts.jsonl").write_text(json.dumps({
        "seed_key": "data/raw/proj/Counter0.tla::k0", "survived": True,
    }) + "\n")

    good_reply_1 = _GOOD_REPLY.replace("Counter", "Counter1")
    model = FakeModel([[_NL_REPLY], [good_reply_1]])

    wl.run_w2(model, seeds_path, raw, run_dir, seed_cap=None, k=1, timeout=30, max_iters=8)

    attempts = [json.loads(l) for l in open(run_dir / "w2_attempts.jsonl")]
    assert len(attempts) == 2
    keys = {a["seed_key"] for a in attempts}
    assert "data/raw/proj/Counter0.tla::k0" in keys
    assert "data/raw/proj/Counter1.tla::k0" in keys
    # only one new model call-pair issued (for seed 1)
    assert len(model.calls) == 2


def test_run_w2_respects_seed_cap(tmp_path):
    seeds_path = tmp_path / "manifest_w2_seeds.jsonl"
    raw = tmp_path / "raw"
    run_dir = tmp_path / "run"
    _write_seeds(seeds_path, n=2)
    _write_raw_specs(raw, n=2)

    good_reply_0 = _GOOD_REPLY.replace("Counter", "Counter0")
    model = FakeModel([[_NL_REPLY], [good_reply_0]])

    wl.run_w2(model, seeds_path, raw, run_dir, seed_cap=1, k=1, timeout=30, max_iters=8)

    attempts = [json.loads(l) for l in open(run_dir / "w2_attempts.jsonl")]
    assert len(attempts) == 1


# --------------------------------------------------------------------- Extra-2: yield report

def test_w2_yield_report_aggregates_multiple_dirs(tmp_path, capsys):
    d1, d2 = tmp_path / "r1", tmp_path / "r2"
    d1.mkdir(), d2.mkdir()
    (d1 / "w2_attempts.jsonl").write_text(
        json.dumps({"seed_key": "a::k0", "survived": True}) + "\n" +
        json.dumps({"seed_key": "b::k0", "survived": False}) + "\n")
    (d1 / "w2_survivors.jsonl").write_text(json.dumps({"seed_key": "a::k0"}) + "\n")
    (d2 / "w2_attempts.jsonl").write_text(
        json.dumps({"seed_key": "c::k0", "survived": False}) + "\n")
    stats = wl.w2_yield_report([d1, d2])
    assert stats["attempts"] == 3
    assert stats["survivors"] == 1
    assert stats["yield_rate"] == pytest.approx(1 / 3)
    out = capsys.readouterr().out
    assert "1/3" in out


# --------------------------------------------------------------------- dry-run model

def test_dry_run_fake_model_produces_valid_module_and_cfg():
    model = wl.DryRunModel()
    prompt = wl.generation_prompt("some description", "Gen")
    reply = model.generate(prompt, 1, 0.8, 4096)[0]
    mod, cfg = wl.extract_module_and_cfg(reply)
    assert mod is not None
    assert cfg is not None
    assert wl.parse_property_invariant(reply) is not None


def test_dry_run_nl_reply_carries_safety_property_section():
    model = wl.DryRunModel()
    reply = model.generate(wl.backtranslate_prompt(_GOOD_SPEC, _GOOD_CFG), 1, 0.8, 4096)[0]
    nl = wl.parse_nl(reply)  # must not raise NLMissingProperty
    assert "SAFETY PROPERTY:" in nl
