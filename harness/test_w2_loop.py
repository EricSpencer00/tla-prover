"""Tests for harness.w2_loop -- the W2 Ralph-loop RFT generation sampler
(docs/superpowers/specs/2026-07-09-w21-quality-corpus-design.md, Workstream 2).

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
"""

# A spec with a syntax error (unbalanced conjunct) -- SANY fails.
_BAD_SANY_SPEC = """---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x +
====
"""

_BAD_SANY_REPLY = f"""```tla
{_BAD_SANY_SPEC}
```
```cfg
{_GOOD_CFG}
```
"""

# A vacuous spec: no INVARIANT in the cfg at all -> vacuity_flags fires.
_VACUOUS_CFG = "INIT Init\nNEXT Next\n"
_VACUOUS_REPLY = f"""```tla
{_GOOD_SPEC}
```
```cfg
{_VACUOUS_CFG}
```
"""

_NL_REPLY = ("A simple bounded counter system. The variable x starts at 0 and "
             "each step either increments or decrements it, guarded so it never "
             "decrements below zero. Safety property: x is always non-negative.")


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


def test_parse_nl_extracts_plain_text():
    nl = wl.parse_nl(_NL_REPLY)
    assert "counter" in nl.lower()
    assert "----" not in nl


def test_parse_nl_strips_markdown_fences():
    reply = f"Here's the description:\n\n```\n{_NL_REPLY}\n```\n"
    nl = wl.parse_nl(reply)
    assert "```" not in nl
    assert "counter" in nl.lower()


def test_generation_prompt_includes_nl_and_module_name():
    p = wl.generation_prompt(_NL_REPLY, "Counter7")
    assert "Counter7" in p
    assert "counter" in p.lower()


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
    # vacuous on every iter -> exhausts max_iters, rejection_reason mentions vacuity
    model = FakeModel([[_VACUOUS_REPLY]] * 2)
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=2)
    assert result["survived"] is False
    assert result["iters"] == 2
    assert "vacu" in result["rejection_reason"].lower()


def test_run_loop_no_module_in_reply_iterates_with_parse_error(tmp_path):
    model = FakeModel([["no module here, sorry"], [_GOOD_REPLY]])
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert result["survived"] is True
    assert result["iters"] == 2


def test_run_loop_records_safety_catch_rate_not_gate(tmp_path, monkeypatch):
    # Per project decision: safety_catch_rate is reward weighting, NOT a hard
    # gate -- a spec with catch rate 0 still survives if SANY/TLC/vacuity pass.
    from harness import w2_loop as wl_mod

    def fake_mutation(*a, **k):
        return {"safety_catch_rate": 0.0, "kill_rate": 0.0, "attempted": 4}

    monkeypatch.setattr(wl_mod, "run_mutation_on_module", fake_mutation)
    model = FakeModel([[_GOOD_REPLY]])
    result = wl.run_loop_for_seed(model, _NL_REPLY, "Counter", tmp_path, timeout=30, max_iters=8)
    assert result["survived"] is True
    assert result["safety_catch_rate"] == 0.0
    assert result["reward_weight"] == pytest.approx(result["complexity_score"] * 1.0)


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


def test_dry_run_fake_model_produces_valid_module_and_cfg():
    model = wl.DryRunModel()
    prompt = wl.generation_prompt("some description", "Gen")
    reply = model.generate(prompt, 1, 0.8, 4096)[0]
    mod, cfg = wl.extract_module_and_cfg(reply)
    assert mod is not None
    assert cfg is not None
