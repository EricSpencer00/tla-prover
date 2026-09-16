"""Tests for harness.w27_scaffold -- the W2.7 structural scaffolding tier-1
experiment (prompt-level, no training). ALL model calls in the run_w27 tests
are mocked via a scripted FakeModel (matching test_w2_loop.py's convention)
-- no live Sophia spend. Real-gate tests use a tiny valid Counter-like spec
fixture, same convention as test_w2_loop.py.
"""
import json

import pytest

from harness import w27_scaffold as ws


# --------------------------------------------------------------------- fixtures

_COUNTER_SPEC = """---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Inc == x < 3 /\\ x' = x + 1
Dec == x > 0 /\\ x' = x - 1
Next == Inc \\/ Dec
Spec == Init /\\ [][Next]_x
NonNegative == x >= 0
====
"""
_COUNTER_CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"

_GOOD_REPLY = f"""```tla
{_COUNTER_SPEC}
```
```cfg
{_COUNTER_CFG}
```
PROPERTY_INVARIANT: NonNegative
"""


class FakeModel:
    """Scripted Model matching test_w2_loop.py's FakeModel convention."""
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


# --------------------------------------------------------------------- extract_structure

def test_extract_structure_counter_fixture():
    s = ws.extract_structure(_COUNTER_SPEC)
    assert s["module"] == "Counter"
    assert s["variables"] == ["x"]
    assert "Inc" in s["actions"]
    assert "Dec" in s["actions"]
    assert s["primes"]["Inc"] == ["x"]
    assert s["primes"]["Dec"] == ["x"]
    assert s["init_ops"] == ["Init"]
    assert s["next_ops"] == ["Next"]
    assert s["spec_ops"] == ["Spec"]
    # Init/Next/Spec/NonNegative do not prime x -> not actions
    assert "Init" not in s["actions"]
    assert "NonNegative" not in s["actions"]


def test_extract_structure_constants():
    spec = """---- MODULE Foo ----
CONSTANT N, M
VARIABLES a, b
Init == a = 0 /\\ b = 0
Bump == a' = a + N
Next == Bump
====
"""
    s = ws.extract_structure(spec)
    assert s["module"] == "Foo"
    assert s["constants"] == ["N", "M"]
    assert s["variables"] == ["a", "b"]
    assert s["primes"]["Bump"] == ["a"]


def test_extract_structure_no_module_is_none():
    s = ws.extract_structure("garbage text, not a spec")
    assert s["module"] is None
    assert s["variables"] == []
    assert s["actions"] == []


def test_extract_structure_pure_no_io():
    # calling twice on the same text yields identical results (pure fn)
    assert ws.extract_structure(_COUNTER_SPEC) == ws.extract_structure(_COUNTER_SPEC)


# --------------------------------------------------------------------- scaffold_block

def test_scaffold_block_renders_module_vars_and_actions():
    s = ws.extract_structure(_COUNTER_SPEC)
    block = ws.scaffold_block(s)
    assert "Counter" in block
    assert "x" in block
    assert "Action Inc updates: x" in block
    assert "Action Dec updates: x" in block


def test_scaffold_block_none_detected_when_no_actions():
    s = {"module": "Empty", "variables": [], "constants": [], "actions": [], "primes": {}}
    block = ws.scaffold_block(s)
    assert "Empty" in block
    assert "(none detected)" in block


# --------------------------------------------------------------------- resolve_spec_path

def test_resolve_spec_path_raw_prefix(tmp_path):
    raw = tmp_path / "raw"
    (raw / "proj").mkdir(parents=True)
    (raw / "proj" / "Foo.tla").write_text(_COUNTER_SPEC)
    p = ws.resolve_spec_path("data/raw/proj/Foo.tla", raw_roots=[raw])
    assert p is not None
    assert p.read_text() == _COUNTER_SPEC


def test_resolve_spec_path_wide_prefix(tmp_path):
    wide = tmp_path / "raw-wide-20260710"
    (wide / "proj").mkdir(parents=True)
    (wide / "proj" / "Bar.tla").write_text(_COUNTER_SPEC)
    p = ws.resolve_spec_path("data/raw-wide-20260710/proj/Bar.tla", raw_roots=[tmp_path / "raw", wide])
    assert p is not None


def test_resolve_spec_path_missing_returns_none(tmp_path):
    p = ws.resolve_spec_path("data/raw/nope/Missing.tla", raw_roots=[tmp_path / "raw"])
    assert p is None


# --------------------------------------------------------------------- build_testbed

def _write_ledger(run_dir, rows):
    run_dir.mkdir(parents=True, exist_ok=True)
    with open(run_dir / "w2_attempts.jsonl", "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")


def test_build_testbed_determinism_and_stratification(tmp_path):
    run_root = tmp_path / "runs"
    raw = tmp_path / "raw"
    (raw / "p").mkdir(parents=True)

    # create real spec files for the valid candidates only
    n_sany = 6
    n_tlc = 4
    rows = []
    for i in range(n_sany):
        src = f"data/raw/p/Sany{i}.tla"
        (raw / "p" / f"Sany{i}.tla").write_text(_COUNTER_SPEC)
        rows.append({"seed_key": f"{src}::k0", "source": src, "module": f"Sany{i}",
                     "survived": False, "rejection_reason": "sany_fail",
                     "nl": f"nl description {i}"})
    for i in range(n_tlc):
        src = f"data/raw/p/Tlc{i}.tla"
        (raw / "p" / f"Tlc{i}.tla").write_text(_COUNTER_SPEC)
        rows.append({"seed_key": f"{src}::k0", "source": src, "module": f"Tlc{i}",
                     "survived": False, "rejection_reason": "tlc_error",
                     "nl": f"tlc nl {i}"})
    # a survived seed -> must be excluded even though reason matches
    src_surv = "data/raw/p/Survivor.tla"
    (raw / "p" / "Survivor.tla").write_text(_COUNTER_SPEC)
    rows.append({"seed_key": f"{src_surv}::k0", "source": src_surv, "module": "Survivor",
                 "survived": False, "rejection_reason": "sany_fail", "nl": "will survive"})
    rows.append({"seed_key": f"{src_surv}::k0", "source": src_surv, "module": "Survivor",
                 "survived": True, "rejection_reason": None, "nl": "will survive"})
    # empty nl -> excluded
    src_empty = "data/raw/p/EmptyNL.tla"
    (raw / "p" / "EmptyNL.tla").write_text(_COUNTER_SPEC)
    rows.append({"seed_key": f"{src_empty}::k0", "source": src_empty, "module": "EmptyNL",
                 "survived": False, "rejection_reason": "sany_fail", "nl": ""})
    # nonexistent spec file -> excluded
    src_missing = "data/raw/p/Missing.tla"
    rows.append({"seed_key": f"{src_missing}::k0", "source": src_missing, "module": "Missing",
                 "survived": False, "rejection_reason": "sany_fail", "nl": "nl missing"})
    # wrong reason -> excluded
    src_wrong = "data/raw/p/WrongReason.tla"
    (raw / "p" / "WrongReason.tla").write_text(_COUNTER_SPEC)
    rows.append({"seed_key": f"{src_wrong}::k0", "source": src_wrong, "module": "WrongReason",
                 "survived": False, "rejection_reason": "cosmetic_fail", "nl": "wrong reason"})

    _write_ledger(run_root / "runA", rows)

    out1 = tmp_path / "testbed1.json"
    out2 = tmp_path / "testbed2.json"
    r1 = ws.build_testbed([str(run_root / "runA")], out1, n=8, raw_roots=[raw])
    r2 = ws.build_testbed([str(run_root / "runA")], out2, n=8, raw_roots=[raw])

    assert r1 == r2  # determinism
    assert json.loads(out1.read_text()) == json.loads(out2.read_text())

    assert r1["candidate_pool_size"] == n_sany + n_tlc  # 10
    assert r1["n"] == 8
    seed_keys = {s["seed_key"] for s in r1["seeds"]}
    assert f"{src_surv}::k0" not in seed_keys
    assert f"{src_empty}::k0" not in seed_keys
    assert f"{src_missing}::k0" not in seed_keys
    assert f"{src_wrong}::k0" not in seed_keys

    # proportional stratification: pool is 6 sany / 4 tlc = 60%/40% of 8 -> ~5/3
    counts = r1["per_reason_counts"]
    assert counts["sany_fail"] + counts["tlc_error"] == 8
    assert counts["sany_fail"] >= counts["tlc_error"]


def test_build_testbed_n_capped_at_pool_size(tmp_path):
    run_root = tmp_path / "runs"
    raw = tmp_path / "raw"
    (raw / "p").mkdir(parents=True)
    rows = []
    for i in range(3):
        src = f"data/raw/p/S{i}.tla"
        (raw / "p" / f"S{i}.tla").write_text(_COUNTER_SPEC)
        rows.append({"seed_key": f"{src}::k0", "source": src, "module": f"S{i}",
                     "survived": False, "rejection_reason": "sany_fail", "nl": "nl"})
    _write_ledger(run_root / "runA", rows)

    out = tmp_path / "testbed.json"
    r = ws.build_testbed([str(run_root / "runA")], out, n=70, raw_roots=[raw])
    assert r["candidate_pool_size"] == 3
    assert r["n"] == 3
    assert len(r["seeds"]) == 3


def test_build_testbed_last_row_wins_for_dup_seed_key(tmp_path):
    run_root = tmp_path / "runs"
    raw = tmp_path / "raw"
    (raw / "p").mkdir(parents=True)
    src = "data/raw/p/Dup.tla"
    (raw / "p" / "Dup.tla").write_text(_COUNTER_SPEC)
    rows = [
        {"seed_key": f"{src}::k0", "source": src, "module": "Dup",
         "survived": False, "rejection_reason": "cosmetic_fail", "nl": "first"},
        {"seed_key": f"{src}::k0", "source": src, "module": "Dup",
         "survived": False, "rejection_reason": "sany_fail", "nl": "second"},
    ]
    _write_ledger(run_root / "runA", rows)

    out = tmp_path / "testbed.json"
    r = ws.build_testbed([str(run_root / "runA")], out, n=10, raw_roots=[raw])
    assert r["candidate_pool_size"] == 1
    assert r["seeds"][0]["nl"] == "second"
    assert r["seeds"][0]["rejection_reason"] == "sany_fail"


# --------------------------------------------------------------------- run_w27

def _write_testbed(path, seeds):
    data = {"derivation": "test", "n": len(seeds), "candidate_pool_size": len(seeds),
            "reasons": ["sany_fail"], "per_reason_counts": {"sany_fail": len(seeds)},
            "seeds": seeds}
    path.write_text(json.dumps(data))
    return data


def test_run_w27_control_arm_writes_rows(tmp_path):
    testbed_path = tmp_path / "testbed.json"
    seeds = [{"source": "data/raw/p/Foo.tla", "seed_key": "data/raw/p/Foo.tla::k0",
              "module": "Foo", "rejection_reason": "sany_fail", "nl": "a counter nl"}]
    _write_testbed(testbed_path, seeds)

    run_dir = tmp_path / "run"
    model = FakeModel([[_GOOD_REPLY]])
    n_survived, n_total = ws.run_w27(model, testbed_path, run_dir, "control",
                                      timeout=30, max_iters=4)
    assert n_total == 1
    assert n_survived == 1

    rows = [json.loads(l) for l in open(run_dir / "w27_rows.jsonl")]
    assert len(rows) == 1
    assert rows[0]["seed_key"] == "data/raw/p/Foo.tla::k0"
    assert rows[0]["arm"] == "control"
    assert rows[0]["survived"] is True


def test_run_w27_scaffold_arm_appends_structural_block(tmp_path):
    raw = tmp_path / "raw"
    (raw / "p").mkdir(parents=True)
    (raw / "p" / "Foo.tla").write_text(_COUNTER_SPEC)

    testbed_path = tmp_path / "testbed.json"
    seeds = [{"source": "data/raw/p/Foo.tla", "seed_key": "data/raw/p/Foo.tla::k0",
              "module": "Foo", "rejection_reason": "sany_fail", "nl": "a counter nl"}]
    _write_testbed(testbed_path, seeds)

    run_dir = tmp_path / "run"
    model = FakeModel([[_GOOD_REPLY]])
    ws.run_w27(model, testbed_path, run_dir, "scaffold", timeout=30, max_iters=4,
               raw_roots=[raw])

    # the generation prompt sent to the model must contain the scaffold block
    prompt = model.calls[0]["prompt"]
    assert "STRUCTURAL SKELETON" in prompt
    assert "Action Inc updates: x" in prompt


def test_run_w27_resume_skips_completed_seed_arm(tmp_path):
    testbed_path = tmp_path / "testbed.json"
    seeds = [{"source": "data/raw/p/Foo.tla", "seed_key": "data/raw/p/Foo.tla::k0",
              "module": "Foo", "rejection_reason": "sany_fail", "nl": "a counter nl"}]
    _write_testbed(testbed_path, seeds)

    run_dir = tmp_path / "run"
    model1 = FakeModel([[_GOOD_REPLY]])
    ws.run_w27(model1, testbed_path, run_dir, "control", timeout=30, max_iters=4)
    assert len(model1.calls) == 1

    rows_after_first = [json.loads(l) for l in open(run_dir / "w27_rows.jsonl")]
    assert len(rows_after_first) == 1

    # second run, same run_dir, same arm -> should skip, no new model calls
    model2 = FakeModel([])
    n_survived, n_total = ws.run_w27(model2, testbed_path, run_dir, "control",
                                      timeout=30, max_iters=4)
    assert len(model2.calls) == 0
    assert n_total == 1

    rows_after_second = [json.loads(l) for l in open(run_dir / "w27_rows.jsonl")]
    assert len(rows_after_second) == 1  # no duplicate row


def test_run_w27_different_arm_not_skipped(tmp_path):
    testbed_path = tmp_path / "testbed.json"
    seeds = [{"source": "data/raw/p/Foo.tla", "seed_key": "data/raw/p/Foo.tla::k0",
              "module": "Foo", "rejection_reason": "sany_fail", "nl": "a counter nl"}]
    _write_testbed(testbed_path, seeds)

    run_dir = tmp_path / "run"
    model1 = FakeModel([[_GOOD_REPLY]])
    ws.run_w27(model1, testbed_path, run_dir, "control", timeout=30, max_iters=4)

    model2 = FakeModel([[_GOOD_REPLY]])
    ws.run_w27(model2, testbed_path, run_dir, "scaffold", timeout=30, max_iters=4)
    assert len(model2.calls) == 1  # different arm -> runs

    rows = [json.loads(l) for l in open(run_dir / "w27_rows.jsonl")]
    assert len(rows) == 2
    arms = {r["arm"] for r in rows}
    assert arms == {"control", "scaffold"}
