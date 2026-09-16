"""Fail-closed reward checks for the constrained online TLC curriculum."""
import pytest

from tools import online_tlc_rl as trainer


SOURCE = """---- MODULE AdaptiveK ----
VARIABLE k
Next == k' = AdaptiveK(newCat)
InvAllowedSet == k \\in ALLOWED_SET
====
"""
CFG = "INIT Init\nNEXT Next\nINVARIANT InvAllowedSet\n"


def test_known_model_comparison_error_is_not_infrastructure():
    assert trainer.known_model_type_error('Error: The first argument of < should be an integer, but instead it is:\n"bugfix"')
    assert not trainer.known_model_type_error('Error: Java heap space')
    assert not trainer.known_model_type_error('Error: Worker disconnected')


def test_known_model_type_error_receives_rejection_reward(monkeypatch, tmp_path):
    monkeypatch.setattr(trainer, 'verify', lambda *args: dict(sany='pass', tlc='error',
                        model_type_error=True, vacuity=[]))
    row = trainer.reward_candidate(SOURCE, SOURCE, CFG, 'AdaptiveK', tmp_path)
    assert row['reward'] == .25 and not row['terminal_pass']


def verdict(tlc="pass", *, safety=True, **extra):
    return dict(sany="pass", tlc=tlc, vacuity=[], explicit_tlc_completion=True,
                mutation_verdict={"safety_killed": safety}, **extra)


def install_verifier(monkeypatch, original=None, mutant=None):
    original = verdict() if original is None else original
    mutant = verdict("fail_invariant") if mutant is None else mutant
    monkeypatch.setattr(trainer, "verify", lambda text, cfg, mod, work:
                        dict(original if text == SOURCE else mutant))


@pytest.mark.parametrize("field,value", [
    ("sany", "timeout"), ("sany", "fail_missing_module"),
    ("tlc", "timeout"), ("tlc", "error"),
    ("vacuity", ["only_1_distinct_states"]), ("explicit_tlc_completion", False),
])
def test_unverified_or_vacuous_candidate_never_gets_reward(monkeypatch, tmp_path, field, value):
    original = verdict()
    original[field] = value
    install_verifier(monkeypatch, original)
    row = trainer.reward_candidate(SOURCE, SOURCE, CFG, "AdaptiveK", tmp_path)
    assert row["reward"] is None
    assert not row["terminal_pass"]


def test_changed_property_is_excluded_even_when_tlc_passes(monkeypatch, tmp_path):
    monkeypatch.setattr(trainer, "verify", lambda *args: verdict())
    changed = SOURCE.replace("k \\in ALLOWED_SET", "TRUE")
    row = trainer.reward_candidate(changed, SOURCE, CFG, "AdaptiveK", tmp_path)
    assert row["reward"] is None
    assert not row["terminal_pass"]


@pytest.mark.parametrize("mutant", [
    verdict("pass"), verdict("timeout"), verdict("error"),
    verdict("fail_deadlock"), {**verdict("fail_invariant"), "sany": "fail"},
])
def test_surviving_or_invalid_mutants_cannot_earn_pass(monkeypatch, tmp_path, mutant):
    install_verifier(monkeypatch, mutant=mutant)
    row = trainer.reward_candidate(SOURCE, SOURCE, CFG, "AdaptiveK", tmp_path)
    assert row["reward"] is None
    assert not row["terminal_pass"]


def test_type_only_mutation_catch_is_partial(monkeypatch, tmp_path):
    install_verifier(monkeypatch, mutant=verdict("fail_invariant", safety=False))
    row = trainer.reward_candidate(SOURCE, SOURCE, CFG, "AdaptiveK", tmp_path)
    assert row["reward"] == 0.6
    assert not row["terminal_pass"]
    assert not row["safety_mutation_adequate"]


def test_missing_mutation_sites_cannot_earn_pass(monkeypatch, tmp_path):
    install_verifier(monkeypatch)
    monkeypatch.setattr(trainer, "action_mutants", lambda *args: [])
    row = trainer.reward_candidate(SOURCE, SOURCE, CFG, "AdaptiveK", tmp_path)
    assert row["reward"] is None
    assert not row["terminal_pass"]


def test_action_mutation_preserves_checked_property():
    mutants = trainer.action_mutants(SOURCE, "AdaptiveK")
    assert len(mutants) == 2
    for _, mutated in mutants:
        assert mutated != SOURCE
        assert mutated.split("InvAllowedSet ==")[1] == SOURCE.split("InvAllowedSet ==")[1]


@pytest.mark.parametrize("increase,decrease", [
    ("number' = number  + 1", "number' = number - 1"),
    ("number' = number +  1", "number' = number  -  1"),
    ("number' = number\t+\t1", "number' = number -\t1"),
])
def test_action_mutants_accept_sampled_whitespace(increase, decrease):
    source = ("---- MODULE Arithmetic ----\n"
              f"Increase == {increase}\nDecrease == {decrease}\n"
              "TypeOK == number \\in {22, 23}\n====\n")
    mutants = trainer.action_mutants(source, "Arithmetic")
    assert len(mutants) == 2
    for _, mutated in mutants:
        assert mutated != source
        assert mutated.split("TypeOK ==")[1] == source.split("TypeOK ==")[1]
