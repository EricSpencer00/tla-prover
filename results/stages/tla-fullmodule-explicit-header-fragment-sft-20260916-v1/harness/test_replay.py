"""Tests for `harness replay` (harness/replay.py).

No network: the prompt-rebuild and model call are monkeypatched. The point under
test is the decision logic -- especially that replay REFUSES to make a request
when it cannot prove the prompt is the same one the run used.
"""
import hashlib
import json

import pytest

from . import replay as replay_mod

MODULE = "---- MODULE Foo ----\nInit == x = 0\n===="
PROMPT = "generate a spec for Foo"
PROMPT_SHA = hashlib.sha256(PROMPT.encode()).hexdigest()


def _run_dir(tmp_path, rows, candidate=MODULE):
    d = tmp_path / "run"
    (d / "candidates").mkdir(parents=True)
    (d / "rows.jsonl").write_text("".join(json.dumps(r) + "\n" for r in rows))
    (d / "config.json").write_text(json.dumps(
        {"run_id": "test-run", "corpus": str(tmp_path)}))
    if candidate is not None:
        (d / "candidates" / "30-A-greedy.tla").write_text(candidate)
    return d


def _row(**over):
    row = {"spec": "30", "framing": "A", "sample": "greedy", "model": "m",
           "temperature": 0.0, "prompt_sha256": PROMPT_SHA, "decode_seed": 4242,
           "candidate_path": "candidates/30-A-greedy.tla", "verdict": "pass"}
    row.update(over)
    return row


@pytest.fixture
def stub_prompt(monkeypatch):
    monkeypatch.setattr(replay_mod, "_rebuild_prompt",
                        lambda row, corpus, run_dir: PROMPT)


def _stub_model(monkeypatch, text):
    monkeypatch.setattr(replay_mod, "make_model", lambda name: object())
    monkeypatch.setattr(replay_mod, "generate_traced_compat",
                        lambda *a, **k: [(text, {"provider_seed_echo": 4242})])


def test_identical_replay(tmp_path, monkeypatch, stub_prompt):
    d = _run_dir(tmp_path, [_row()])
    _stub_model(monkeypatch, f"here:\n{MODULE}\n")
    out = replay_mod.replay(d, "30", "greedy")
    assert out["verdict"] == "IDENTICAL"
    assert out["seed"] == 4242
    assert out["stored_sha256"] == out["replay_sha256"]


def test_divergent_replay_carries_a_diff(tmp_path, monkeypatch, stub_prompt):
    d = _run_dir(tmp_path, [_row()])
    _stub_model(monkeypatch, "---- MODULE Foo ----\nInit == x = 99\n====")
    out = replay_mod.replay(d, "30", "greedy")
    assert out["verdict"] == "DIVERGENT"
    assert out["stored_sha256"] != out["replay_sha256"]
    assert "x = 99" in out["diff"]


def test_prompt_drift_blocks_the_request(tmp_path, monkeypatch):
    """The whole point: if the corpus moved, replaying measures nothing, so no
    API call may be made."""
    d = _run_dir(tmp_path, [_row(prompt_sha256="0" * 64)])
    monkeypatch.setattr(replay_mod, "_rebuild_prompt",
                        lambda row, corpus, run_dir: PROMPT)

    def explode(*a, **k):
        raise AssertionError("replay must not call the model on prompt drift")

    monkeypatch.setattr(replay_mod, "make_model", explode)
    monkeypatch.setattr(replay_mod, "generate_traced_compat", explode)

    out = replay_mod.replay(d, "30", "greedy")
    assert out["verdict"] == "PROMPT_DRIFT"
    assert out["rebuilt_prompt_sha256"] == PROMPT_SHA
    assert out["recorded_prompt_sha256"] == "0" * 64


def test_pre_provenance_row_is_reported_not_faked(tmp_path, monkeypatch):
    """A row with no decode_seed predates this feature. Replaying it at a freshly
    derived seed would look like a reproduction while being nothing of the kind."""
    d = _run_dir(tmp_path, [_row(decode_seed=None)])

    def explode(*a, **k):
        raise AssertionError("must not call the model without a recorded seed")

    monkeypatch.setattr(replay_mod, "make_model", explode)

    out = replay_mod.replay(d, "30", "greedy")
    assert out["verdict"] == "SEED_UNSUPPORTED"
    assert "NOT what the original run sent" in out["note"]
    assert isinstance(out["derived_seed"], int)


def test_missing_candidate_is_reported(tmp_path, monkeypatch, stub_prompt):
    d = _run_dir(tmp_path, [_row(candidate_path=None)], candidate=None)
    out = replay_mod.replay(d, "30", "greedy")
    assert out["verdict"] == "NO_CANDIDATE"


def test_ambiguous_framing_is_rejected(tmp_path):
    """Append-only ledgers can hold the same (spec, sample) in both framings."""
    d = _run_dir(tmp_path, [_row(), _row(framing="B")])
    with pytest.raises(SystemExit, match="both framings"):
        replay_mod.replay(d, "30", "greedy")


def test_last_row_wins_for_a_resumed_pair(tmp_path, monkeypatch, stub_prompt):
    """Rule 8 append-only means a resumed run can hold duplicates; the last is
    what the summary re-score used."""
    d = _run_dir(tmp_path, [_row(decode_seed=1), _row(decode_seed=2)])
    _stub_model(monkeypatch, MODULE)
    assert replay_mod.replay(d, "30", "greedy")["seed"] == 2


def test_unknown_pair_exits(tmp_path):
    d = _run_dir(tmp_path, [_row()])
    with pytest.raises(SystemExit, match="no row for"):
        replay_mod.replay(d, "31", "greedy")
