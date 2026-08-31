"""Tests for harness/private_data.py and the answer-key leak check (ticket #11).

The point of both is that a mistake is loud. A stripped artifact quietly
reappearing in the tracked tree, or a missing holdout manifest quietly scoring
as an empty holdout, are the two ways this goes wrong without anyone noticing.
"""
import importlib
import json
import subprocess
from pathlib import Path

import pytest

from harness import private_data

REPO = Path(__file__).resolve().parent.parent


def test_stripped_artifacts_are_not_tracked():
    tracked = subprocess.run(["git", "ls-files", "-z"], cwd=REPO,
                             capture_output=True, text=True, check=True).stdout.split("\0")
    for path in tracked:
        for s in private_data.STRIPPED:
            assert not (path == s or path.startswith(s + "/")), \
                f"{path} is the Gate-2 answer key; it belongs in the private root"


def test_resolve_prefers_the_repo_copy(monkeypatch, tmp_path):
    monkeypatch.setattr(private_data, "PRIVATE", tmp_path)
    # policy.json was never stripped, so it is still in the repo.
    assert private_data.resolve("corpus/configs/policy.json") == REPO / "corpus/configs/policy.json"


def test_resolve_falls_back_to_the_private_root(monkeypatch, tmp_path):
    monkeypatch.setattr(private_data, "PRIVATE", tmp_path)
    got = private_data.resolve("corpus/configs/patches/30.tla")
    assert got == tmp_path / "corpus/configs/patches/30.tla"


def test_holdout_specs_is_empty_without_a_private_root(monkeypatch, tmp_path):
    monkeypatch.setattr(private_data, "HOLDOUT_FILE", tmp_path / "nope.json")
    assert private_data.holdout_specs() == []


def test_require_holdout_fails_loudly_without_a_private_root(monkeypatch, tmp_path):
    monkeypatch.setattr(private_data, "HOLDOUT_FILE", tmp_path / "nope.json")
    with pytest.raises(SystemExit, match="TLA_PROVER_PRIVATE"):
        private_data.require_holdout()


def test_require_holdout_returns_thirty_specs_when_mounted(monkeypatch, tmp_path):
    f = tmp_path / "holdout.json"
    f.write_text(json.dumps({"holdout_specs": list(range(1, 31))}))
    monkeypatch.setattr(private_data, "HOLDOUT_FILE", f)
    assert len(private_data.require_holdout()) == 30


def test_env_var_overrides_the_default_private_root(monkeypatch, tmp_path):
    monkeypatch.setenv("TLA_PROVER_PRIVATE", str(tmp_path))
    reloaded = importlib.reload(private_data)
    try:
        assert reloaded.PRIVATE == tmp_path
    finally:
        monkeypatch.delenv("TLA_PROVER_PRIVATE")
        importlib.reload(private_data)


def test_leak_check_has_power(monkeypatch):
    """Positive control: with the known-leak allowlist emptied, the membership
    check must find the Gate-2 run ledgers. A check that never fires is not a
    check."""
    spec = importlib.util.spec_from_file_location(
        "check_holdout_leak", REPO / "tools" / "check_holdout_leak.py")
    chk = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(chk)
    if not chk.private_data.holdout_specs():
        pytest.skip("no private root mounted")
    monkeypatch.setattr(chk, "KNOWN_MEMBERSHIP_LEAKS", ())
    assert len(chk.check_membership(chk.tracked_files())) > 20
