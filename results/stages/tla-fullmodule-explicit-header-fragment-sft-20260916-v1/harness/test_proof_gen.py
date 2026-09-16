import json

import pytest

from . import proof_gen as pg

SYNTHETIC_MODULE = """---- MODULE Synth ----
EXTENDS Naturals

VARIABLE x

Init == x = 0
Next == x' = x + 1

THEOREM Inductiveness == Init /\\ Next => x' >= 0
====
"""


class ScriptedModel:
    """Returns queued replies in order, one per call; records prompts seen."""
    id = "scripted-test-model"

    def __init__(self, replies):
        self.replies = list(replies)
        self.prompts = []

    def generate(self, prompt, n, temperature, max_tokens):
        self.prompts.append(prompt)
        reply = self.replies.pop(0) if self.replies else ""
        return [reply] * n


def fake_certifier_factory(statuses):
    """statuses: list of (status, proved, total) consumed in call order."""
    calls = []

    def checker(tla_file, workdir, timeout=300):
        status, proved, total = statuses[len(calls)]
        calls.append((tla_file, workdir))
        out = "All %d obligations proved." % total if status == "pass" and proved == total \
            else "1/%d obligations failed.\n<some tlapm failure text>" % total
        return status, proved, total, out, 0.1
    checker.calls = calls
    return checker


# ---------------------------------------------------------------- extraction

def test_extract_proof_block_fenced():
    reply = "Here is the proof:\n```tla\nPROOF\n<1>1. QED\n```\nThanks."
    block = pg.extract_proof_block(reply)
    assert block is not None
    assert block.startswith("PROOF")


def test_extract_proof_block_raw_fallback():
    reply = "Sure, here you go:\nOBVIOUS\n"
    block = pg.extract_proof_block(reply)
    assert block == "OBVIOUS"


def test_extract_proof_block_none_when_no_proof_shape():
    reply = "I cannot produce a proof for this theorem."
    assert pg.extract_proof_block(reply) is None


# ---------------------------------------------------------------- splicing

def test_splice_proof_round_trip():
    spliced = pg.splice_proof(SYNTHETIC_MODULE, "Inductiveness", "PROOF\n<1>1. QED")
    assert "THEOREM Inductiveness ==" in spliced
    assert "PROOF" in spliced
    assert "<1>1. QED" in spliced
    # theorem statement itself preserved
    assert "Init /\\ Next => x' >= 0" in spliced


def test_splice_proof_replaces_existing_proof():
    with_proof = pg.splice_proof(SYNTHETIC_MODULE, "Inductiveness", "OBVIOUS")
    resliced = pg.splice_proof(with_proof, "Inductiveness", "PROOF\n<1>1. QED")
    assert resliced.count("THEOREM Inductiveness ==") == 1
    assert "OBVIOUS" not in resliced
    assert "<1>1. QED" in resliced


def test_splice_proof_missing_theorem_raises():
    with pytest.raises(ValueError):
        pg.splice_proof(SYNTHETIC_MODULE, "NoSuchTheorem", "OBVIOUS")


# ---------------------------------------------------------------- prompt

def test_build_proof_prompt_includes_retrieval_and_module():
    hits = [{"backend": "zenon", "score": 0.42, "goal_text_normalized": "x = 0",
             "by_facts": ["BY DEF Init"]}]
    prompt = pg.build_proof_prompt(SYNTHETIC_MODULE, "Inductiveness", hits)
    assert "Inductiveness" in prompt
    assert SYNTHETIC_MODULE in prompt
    assert "zenon" in prompt
    assert "BY DEF Init" in prompt
    assert "TLAPM OUTPUT" not in prompt  # no error evidence on iter 1


def test_build_proof_prompt_includes_error_evidence_on_iter2():
    prompt = pg.build_proof_prompt(SYNTHETIC_MODULE, "Inductiveness", [],
                                    error_evidence="1/2 obligations failed.")
    assert "TLAPM OUTPUT" in prompt
    assert "1/2 obligations failed." in prompt


# ---------------------------------------------------------------- run loop

def test_run_one_theorem_certifies_on_first_iter(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    mod_dir = lmgpa_root / "benchmarks" / "cat"
    mod_dir.mkdir(parents=True)
    (mod_dir / "Synth.tla").write_text(SYNTHETIC_MODULE)
    entry = {"id": "synth1", "category": "cat", "module_file": "benchmarks/cat/Synth.tla",
             "theorem_name": "Inductiveness"}

    model = ScriptedModel(["```tla\nOBVIOUS\n```"])
    checker = fake_certifier_factory([("pass", 1, 1)])
    run_dir = tmp_path / "run"

    rows = pg.run_one_theorem(model, entry, lmgpa_root, index=None, run_dir=run_dir,
                               k_iters=4, checker=checker)
    assert len(rows) == 1
    assert rows[0]["certified"] is True
    assert rows[0]["tlapm_status"] == "pass"
    proof_file = run_dir / "proofs" / "synth1.tla"
    assert proof_file.exists()
    assert "OBVIOUS" in proof_file.read_text()


def test_run_one_theorem_feeds_back_error_and_retries(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    mod_dir = lmgpa_root / "benchmarks" / "cat"
    mod_dir.mkdir(parents=True)
    (mod_dir / "Synth.tla").write_text(SYNTHETIC_MODULE)
    entry = {"id": "synth2", "category": "cat", "module_file": "benchmarks/cat/Synth.tla",
             "theorem_name": "Inductiveness"}

    model = ScriptedModel(["```tla\nBY DEF Init\n```", "```tla\nOBVIOUS\n```"])
    checker = fake_certifier_factory([("partial", 0, 2), ("pass", 1, 1)])
    run_dir = tmp_path / "run"

    rows = pg.run_one_theorem(model, entry, lmgpa_root, index=None, run_dir=run_dir,
                               k_iters=4, checker=checker)
    assert len(rows) == 2
    assert rows[0]["certified"] is False
    assert rows[1]["certified"] is True
    # second prompt must have carried the first attempt's tlapm failure text
    assert "obligations failed" in model.prompts[1]


def test_run_one_theorem_stops_at_k_iters_without_certifying(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    mod_dir = lmgpa_root / "benchmarks" / "cat"
    mod_dir.mkdir(parents=True)
    (mod_dir / "Synth.tla").write_text(SYNTHETIC_MODULE)
    entry = {"id": "synth3", "category": "cat", "module_file": "benchmarks/cat/Synth.tla",
             "theorem_name": "Inductiveness"}

    model = ScriptedModel(["```tla\nBY DEF Init\n```"] * 3)
    checker = fake_certifier_factory([("partial", 0, 2)] * 3)
    run_dir = tmp_path / "run"

    rows = pg.run_one_theorem(model, entry, lmgpa_root, index=None, run_dir=run_dir,
                               k_iters=3, checker=checker)
    assert len(rows) == 3
    assert all(r["certified"] is False for r in rows)
    assert not (run_dir / "proofs" / "synth3.tla").exists()


def test_run_proof_gen_resume_skips_certified_ids(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    mod_dir = lmgpa_root / "benchmarks" / "cat"
    mod_dir.mkdir(parents=True)
    (mod_dir / "Synth.tla").write_text(SYNTHETIC_MODULE)

    manifest = [{"id": "synth1", "category": "cat", "module_file": "benchmarks/cat/Synth.tla",
                 "theorem_name": "Inductiveness"},
                {"id": "synth2", "category": "cat", "module_file": "benchmarks/cat/Synth.tla",
                 "theorem_name": "Inductiveness"}]
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps(manifest))

    run_dir = tmp_path / "run"
    run_dir.mkdir()
    # pre-seed rows.jsonl: synth1 already certified.
    (run_dir / "rows.jsonl").write_text(
        json.dumps({"id": "synth1", "iter": 1, "certified": True,
                    "proved": 1, "total": 1, "tlapm_status": "pass",
                    "proof_sha": "x"}) + "\n")

    model = ScriptedModel(["```tla\nOBVIOUS\n```"])
    checker = fake_certifier_factory([("pass", 1, 1)])

    result = pg.run_proof_gen(model, manifest_path=manifest_path, run_dir=run_dir,
                               k_iters=4, index_path=tmp_path / "no_index.jsonl",
                               lmgpa_root=lmgpa_root, checker=checker)

    # only synth2 should have been attempted (one call to generate).
    assert len(model.prompts) == 1
    assert result["n_certified"] == 2
    assert result["n_total"] == 2

    rows = [json.loads(l) for l in (run_dir / "rows.jsonl").read_text().splitlines()]
    ids_attempted = [r["id"] for r in rows if r["id"] != "synth1"]
    assert ids_attempted == ["synth2"]


def test_run_proof_gen_ledger_rows_complete(tmp_path):
    lmgpa_root = tmp_path / "lmgpa"
    mod_dir = lmgpa_root / "benchmarks" / "cat"
    mod_dir.mkdir(parents=True)
    (mod_dir / "Synth.tla").write_text(SYNTHETIC_MODULE)

    manifest = [{"id": "synth1", "category": "cat", "module_file": "benchmarks/cat/Synth.tla",
                 "theorem_name": "Inductiveness"}]
    manifest_path = tmp_path / "manifest.json"
    manifest_path.write_text(json.dumps(manifest))

    run_dir = tmp_path / "run"
    model = ScriptedModel(["```tla\nOBVIOUS\n```"])
    checker = fake_certifier_factory([("pass", 1, 1)])

    pg.run_proof_gen(model, manifest_path=manifest_path, run_dir=run_dir, k_iters=4,
                      index_path=tmp_path / "no_index.jsonl", lmgpa_root=lmgpa_root,
                      checker=checker)

    rows = [json.loads(l) for l in (run_dir / "rows.jsonl").read_text().splitlines()]
    assert len(rows) == 1
    row = rows[0]
    for field in ("id", "iter", "certified", "proved", "total", "tlapm_status", "proof_sha"):
        assert field in row
