"""Tests for harness.repair_harvest (W2.6 minimal-diff trace harvest).
Zero model spend: scripted model; real SANY/TLC on the tiny Counter fixture."""
import json
from pathlib import Path

import pytest

from harness import repair_harvest as rh
from harness.gen_eval import corrupt

_SPEC = """---- MODULE Counter ----
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
_CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"


class Scripted:
    id = "scripted"

    def __init__(self, replies):
        self.replies = list(replies)

    def generate(self, prompt, n, temperature, max_tokens):
        return [self.replies.pop(0)]


def _survivor():
    import hashlib
    return {"spec_text": _SPEC, "cfg_text": _CFG, "module": "Counter",
            "seed_key": "t::k0",
            "spec_sha": hashlib.sha256(_SPEC.encode()).hexdigest()}


def test_diff_minimality_metric():
    assert rh.diff_minimality(_SPEC, _SPEC) == 0.0
    one_line = _SPEC.replace("x >= 0", "x > -1")
    assert rh.diff_minimality(_SPEC, one_line) < 0.15
    assert rh.diff_minimality(_SPEC, "---- MODULE Other ----\n====\n") > 0.5


def test_harvest_accepts_minimal_repair(tmp_path):
    surv = _survivor()
    broken, _ = corrupt(_SPEC, rh.corruption_seed_for(_SPEC))
    # the exact minimal repair: give back the original spec
    model = Scripted([f"```tla\n{_SPEC}\n```"])
    rows = list(rh.harvest_one(surv, model, k=1, workroot=tmp_path, timeout=30))
    acc = [r for r in rows if r.get("accepted")]
    # corruption may be TLC-undetectable for some seeds; only assert accept
    # when the corruption produced a real repair task
    if any(r.get("reject_reason") == "corruption_not_detected_by_tlc" for r in rows):
        pytest.skip("seeded corruption not TLC-detectable on this fixture")
    assert len(acc) == 1
    t = acc[0]
    assert t["broken_text"] == broken
    assert t["fixed_text"].strip() == _SPEC.strip()
    assert t["diff_ratio"] <= rh.DIFF_MINIMALITY_THRESHOLD
    assert "error_evidence" in t and t["error_evidence"]


def test_harvest_rejects_wholesale_rewrite(tmp_path):
    surv = _survivor()
    rewrite = """---- MODULE Counter ----
EXTENDS Naturals
VARIABLE y
Init == y = 0
Next == y' = (y + 1) % 4
NonNegative == y >= 0
====
"""
    model = Scripted([f"```tla\n{rewrite}\n```"])
    rows = list(rh.harvest_one(surv, model, k=1, workroot=tmp_path, timeout=30))
    if any(r.get("reject_reason") == "corruption_not_detected_by_tlc" for r in rows):
        pytest.skip("seeded corruption not TLC-detectable on this fixture")
    assert not any(r.get("accepted") for r in rows)
    assert any(r.get("reject_reason") == "not_minimal_diff" for r in rows)


def test_run_harvest_ledgers_and_resumes(tmp_path):
    d = tmp_path / "survrun"
    d.mkdir()
    (d / "w2_survivors.jsonl").write_text(json.dumps(
        {"survived": True, "spec_text": _SPEC, "cfg_text": _CFG,
         "module": "Counter", "seed_key": "t::k0"}) + "\n")
    out = tmp_path / "harvest"
    model = Scripted([f"```tla\n{_SPEC}\n```"])
    rh.run_harvest(model, [str(d)], out, k=1, timeout=30)
    attempts = (out / "harvest_attempts.jsonl").read_text().splitlines()
    assert attempts
    # resume: no replies left in the scripted model; must not call it again
    rh.run_harvest(Scripted([]), [str(d)], out, k=1, timeout=30)
    assert len((out / "harvest_attempts.jsonl").read_text().splitlines()) == len(attempts)
