"""Tests for decoder provenance (harness/decoding.py, Model.generate_traced).

Zero API spend, zero network: everything runs against LocalStub and in-process
fakes. See docs/designs/2026-08-08-decode-provenance-design.md.
"""
import json
import os
import subprocess
import sys

import pytest

from .decoding import (SEED_MASK, derive_seed, effective_params_sha256,
                       extraction_divergence, generate_traced_compat, url_sha256)
from .repair import AnthropicModel, LocalStub, Model, OpenAICompatModel

# --------------------------------------------------------------- derive_seed


def test_derive_seed_is_deterministic():
    assert derive_seed("run-a", "30", "A", "greedy") == \
        derive_seed("run-a", "30", "A", "greedy")


def test_derive_seed_is_stable_across_processes():
    """Must not depend on PYTHONHASHSEED -- replay in a later process has to
    recompute the same seed, which rules out hash()."""
    code = ("from harness.decoding import derive_seed;"
            "print(derive_seed('run-a', '30', 'A', 'greedy'))")
    env = {**os.environ, "PYTHONHASHSEED": "1"}
    out = subprocess.run([sys.executable, "-c", code], capture_output=True,
                         text=True, env=env, cwd=os.path.dirname(
                             os.path.dirname(os.path.abspath(__file__))))
    assert int(out.stdout.strip()) == derive_seed("run-a", "30", "A", "greedy")


@pytest.mark.parametrize("a,b", [
    (("r1", "30", "A", "greedy"), ("r2", "30", "A", "greedy")),   # run_id
    (("r1", "30", "A", "greedy"), ("r1", "31", "A", "greedy")),   # spec
    (("r1", "30", "A", "greedy"), ("r1", "30", "B", "greedy")),   # framing
    (("r1", "30", "A", "greedy"), ("r1", "30", "A", 1)),          # sample_id
])
def test_derive_seed_varies_in_every_input(a, b):
    assert derive_seed(*a) != derive_seed(*b)


def test_derive_seed_in_provider_accepted_range():
    """vLLM / OpenAI / the ALCF router all take a signed-32-bit-positive seed."""
    for spec in range(300):
        s = derive_seed("run", str(spec), "A", spec % 33)
        assert 0 <= s <= SEED_MASK


def test_derive_seed_accepts_int_and_str_sample_ids():
    """sample_id is "greedy" for the pass@1 arm and an int for the rest."""
    assert derive_seed("r", "30", "A", 1) == derive_seed("r", "30", "A", "1")


# ------------------------------------------------- effective_params_sha256


def test_params_hash_ignores_the_prompt():
    """prompt_sha256 already covers the prompt; including it would make the
    params hash useless for grouping rows by budget."""
    a = {"model": "m", "temperature": 0.8, "messages": [{"content": "one"}]}
    b = {"model": "m", "temperature": 0.8, "messages": [{"content": "two"}]}
    assert effective_params_sha256(a) == effective_params_sha256(b)


def test_params_hash_is_key_order_insensitive():
    a = {"model": "m", "temperature": 0.8, "max_tokens": 10}
    b = {"max_tokens": 10, "temperature": 0.8, "model": "m"}
    assert effective_params_sha256(a) == effective_params_sha256(b)


@pytest.mark.parametrize("extra", [
    {"reasoning_effort": "medium"},
    {"top_p": 0.9},
    {"seed": 7},
])
def test_params_hash_changes_when_a_knob_changes(extra):
    base = {"model": "m", "temperature": 0.8, "max_tokens": 10}
    assert effective_params_sha256(base) != effective_params_sha256({**base, **extra})


def test_url_sha256_never_leaks_the_url():
    secret = "https://router.example/v1?token=hunter2"
    h = url_sha256(secret)
    assert "hunter2" not in h and "example" not in h
    assert h == url_sha256(secret) and h != url_sha256("https://other/v1")


# --------------------------------------------------- Model API / recursion


def test_bare_subclass_raises_not_implemented_not_recursion():
    """The ABC defines generate_traced in terms of generate. If a subclass ever
    made generate delegate back to generate_traced, the cycle would close and
    this would be RecursionError. Pin the direction."""
    class Bare(Model):
        id = "bare"

    with pytest.raises(NotImplementedError):
        Bare().generate_traced("p", 1, 0.0, 10)


def test_generate_only_subclass_works_through_traced_path():
    class GenOnly(Model):
        id = "gen-only"

        def generate(self, prompt, n, temperature, max_tokens, seed=None):
            return ["out"] * n

    assert GenOnly().generate_traced("p", 2, 0.0, 10) == [("out", {}), ("out", {})]


def test_generate_and_generate_traced_agree_on_text():
    stub = LocalStub()
    prompt = "===BEGIN SPEC===\n---- MODULE M ----\n====\n===END SPEC==="
    plain = stub.generate(prompt, 3, 0.0, 100)
    traced = [t for t, _ in stub.generate_traced(prompt, 3, 0.0, 100)]
    assert plain == traced


def test_local_stub_reports_seed_supported():
    meta = LocalStub().generate_traced("p", 1, 0.0, 10, seed=42)[0][1]
    assert meta["seed_supported"] is True
    assert meta["decode_seed"] == 42 and meta["provider_seed_echo"] == 42


def test_anthropic_reports_seed_unsupported_rather_than_faking_one(monkeypatch):
    """The Messages API has no seed parameter. Recording a seed it never sent
    would make an irreproducible row look reproducible -- worse than no seed."""
    monkeypatch.setenv("ANTHROPIC_API_KEY", "test-key")
    m = AnthropicModel()
    monkeypatch.setattr(m, "_one", lambda p, t, mt: "reply")
    _, meta = m.generate_traced("p", 1, 0.2, 10, seed=42)[0]
    assert meta["seed_supported"] is False
    assert meta["decode_seed"] is None


# ------------------------------------- OPENAI_EXTRA_BODY override (Landmine 3)


def _openai_model(monkeypatch, extra_body=None):
    monkeypatch.setenv("OPENAI_BASE_URL", "https://endpoint.test/v1")
    monkeypatch.setenv("OPENAI_API_KEY", "k")
    if extra_body is None:
        monkeypatch.delenv("OPENAI_EXTRA_BODY", raising=False)
    else:
        monkeypatch.setenv("OPENAI_EXTRA_BODY", json.dumps(extra_body))
    return OpenAICompatModel("some-model")


def _capture_body(monkeypatch, model):
    """Run _one against a stubbed urlopen, returning (sent_body, meta)."""
    sent = {}

    class _Resp:
        def __enter__(self):
            return self

        def __exit__(self, *a):
            return False

        def read(self):
            return json.dumps({"choices": [{"message": {"content": "ok"}}],
                               "usage": {}}).encode()

    def fake_urlopen(req, timeout=None):
        sent.update(json.loads(req.data))
        return _Resp()

    monkeypatch.setattr("harness.repair.urllib.request.urlopen", fake_urlopen)
    monkeypatch.setattr(model, "_throttle", lambda: None)
    _, meta = model._one("prompt", 0.8, 100, seed=1234)
    return sent, meta


def test_seed_is_actually_sent(monkeypatch):
    model = _openai_model(monkeypatch)
    sent, meta = _capture_body(monkeypatch, model)
    assert sent["seed"] == 1234
    assert meta["decode_seed"] == 1234 and meta["seed_supported"] is True


def test_extra_body_seed_override_is_reported_not_the_requested_seed(monkeypatch):
    """OPENAI_EXTRA_BODY merges after the base body, so a stale one silently wins.
    The row must record what was SENT (9999), not what was asked for (1234)."""
    model = _openai_model(monkeypatch, {"seed": 9999})
    sent, meta = _capture_body(monkeypatch, model)
    assert sent["seed"] == 9999
    assert meta["decode_seed"] == 9999


def test_params_hash_reflects_extra_body(monkeypatch):
    plain = _capture_body(monkeypatch, _openai_model(monkeypatch))[1]
    effort = _capture_body(
        monkeypatch, _openai_model(monkeypatch, {"reasoning_effort": "high"}))[1]
    assert plain["decode_params_sha256"] != effort["decode_params_sha256"]


def test_api_error_still_carries_provenance(monkeypatch):
    """A failed call must not produce a row with null provenance -- otherwise an
    error run looks like a pre-seed run."""
    import urllib.error

    model = _openai_model(monkeypatch)
    monkeypatch.setattr(model, "_throttle", lambda: None)
    model.max_retries = 1

    def boom(req, timeout=None):
        raise urllib.error.URLError("down")

    monkeypatch.setattr("harness.repair.urllib.request.urlopen", boom)
    text, meta = model._one("prompt", 0.8, 100, seed=77)
    assert text.startswith("[api_error")
    assert meta["decode_seed"] == 77


# ------------------------------------------------------- compat shim


def test_compat_shim_handles_a_four_arg_duck_typed_model():
    """Eleven stand-ins in the harness expose only the original four-arg
    generate and do not subclass Model."""
    class Legacy:
        id = "legacy"

        def generate(self, prompt, n, temperature, max_tokens):
            return ["legacy"] * n

    out = generate_traced_compat(Legacy(), "p", 2, 0.8, 10, seed=5)
    assert out == [("legacy", {}), ("legacy", {})]


def test_compat_shim_prefers_traced_when_available():
    meta = generate_traced_compat(LocalStub(), "p", 1, 0.0, 10, seed=8)[0][1]
    assert meta["decode_seed"] == 8


# ------------------------------------------------- extraction divergence


ONE_MODULE = "---- MODULE M ----\nVARIABLE x\n===="


def test_no_divergence_on_a_single_clean_module():
    divergent, _, _ = extraction_divergence(f"here you go:\n{ONE_MODULE}\n")
    assert divergent is False


def test_no_divergence_when_neither_extractor_finds_anything():
    """Verdict is already no_module_extracted; that is not a divergence."""
    divergent, first, last = extraction_divergence("sorry, I cannot help")
    assert divergent is False and first is None and last is None


def test_divergent_when_a_draft_precedes_the_final_module():
    """gen_eval takes the FIRST match, repair takes the LAST."""
    reply = (f"draft:\n{ONE_MODULE}\n\nfinal:\n"
             "---- MODULE M ----\nVARIABLE y\n====\n")
    divergent, first, last = extraction_divergence(reply)
    assert divergent is True
    assert "VARIABLE x" in first and "VARIABLE y" in last


def test_divergent_when_only_one_extractor_parses():
    """An unnamed module parses under gen_eval's regex but not repair's, which
    requires `\\w+` plus trailing dashes. Exactly-one-None is the most
    interesting divergence, not an exclusion from it."""
    divergent, first, last = extraction_divergence("---- MODULE ----\nx\n====")
    assert divergent is True
    assert first is not None and last is None
