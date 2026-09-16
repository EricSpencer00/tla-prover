"""TLA_GUIDED_GRAMMAR wiring: the grammar must reach the request body, be
recorded in decode provenance, and fail loudly when its path is wrong."""
import json
import os

import pytest

from harness.repair import OpenAICompatModel


@pytest.fixture
def model(monkeypatch):
    monkeypatch.setenv("OPENAI_BASE_URL", "http://localhost:1/v1")
    monkeypatch.setenv("OPENAI_API_KEY", "x")
    monkeypatch.delenv("OPENAI_EXTRA_BODY", raising=False)
    monkeypatch.delenv("TLA_GUIDED_GRAMMAR", raising=False)
    return OpenAICompatModel("m")


def _body(model, monkeypatch):
    """Run _one far enough to capture the request body, without a network call."""
    captured = {}

    def fake_request(url, data=None, headers=None):
        captured["body"] = json.loads(data)
        raise RuntimeError("stop before send")

    monkeypatch.setattr("urllib.request.Request", fake_request)
    with pytest.raises(RuntimeError):
        model._one("p", 0.0, 16, seed=7)
    return captured["body"]


def test_no_grammar_by_default(model, monkeypatch):
    assert "structured_outputs" not in _body(model, monkeypatch)
    assert "guided_grammar" not in _body(model, monkeypatch)


def test_grammar_file_reaches_the_request_body(model, monkeypatch, tmp_path):
    g = tmp_path / "g.ebnf"
    g.write_text('root ::= "ok"\n')
    monkeypatch.setenv("TLA_GUIDED_GRAMMAR", str(g))
    b = _body(model, monkeypatch)
    assert b["structured_outputs"] == {"grammar": 'root ::= "ok"\n'}
    # the legacy key is accepted and IGNORED by vLLM 0.22; sending it
    # would silently produce an ungated arm
    assert "guided_grammar" not in b


def test_grammar_changes_decode_params_hash(model, monkeypatch, tmp_path):
    plain = _body(model, monkeypatch)
    g = tmp_path / "g.ebnf"
    g.write_text('root ::= "ok"\n')
    monkeypatch.setenv("TLA_GUIDED_GRAMMAR", str(g))
    gated = _body(model, monkeypatch)
    from harness.decoding import effective_params_sha256
    assert effective_params_sha256(plain) != effective_params_sha256(gated)


def test_a_wrong_path_fails_loudly(model, monkeypatch):
    """A run that believes it is grammar-gated and silently is not would be
    scored as if it were. Better to crash."""
    monkeypatch.setenv("TLA_GUIDED_GRAMMAR", "/nonexistent/g.ebnf")
    with pytest.raises(FileNotFoundError):
        _body(model, monkeypatch)
