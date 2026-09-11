import importlib.metadata
import sys
import types

import pytest

from tools import protected_checkpoint_preflight as preflight


class Tokenizer:
    def apply_chat_template(self, messages, **kwargs):
        return messages[0]["content"]

    def encode(self, text, **kwargs):
        return [ord(char) for char in text]


def packet():
    rows, encodings = [], []
    for index in range(108):
        ident = preflight.WANTED_IDS.get(index, f"other-{index}")
        prompt = f"prompt-{index}"
        rows.append({"id": ident, "prompt": prompt})
        encodings.append({"input_ids": [ord(char) for char in prompt], "prompt_tokens": len(prompt)})
    return {"rows": rows, "encodings": encodings}


def test_protected_rows_and_prompt_tokens_are_exact():
    selected = preflight.protected_rows(packet())
    assert set(selected) == {47, 107}
    assert preflight.verify_prompt_tokens(Tokenizer(), selected)["47"]["prompt_tokens"] == 9


def test_protected_rows_reject_missing_or_mismatched_prompt_tokens():
    bad = packet()
    bad["encodings"][47]["input_ids"] = [1]
    with pytest.raises(ValueError, match="tokenizer/prompt mismatch"):
        preflight.verify_prompt_tokens(Tokenizer(), preflight.protected_rows(bad))


def test_restore_exact_reloads_tensor_state():
    torch = pytest.importorskip("torch")
    parameter = torch.nn.Parameter(torch.zeros(2))
    saved = {"trainable_state": {"weight": torch.tensor([1.0, 2.0])}}
    preflight.restore_exact({"weight": parameter}, saved)
    assert torch.equal(parameter, saved["trainable_state"]["weight"])


def test_xgrammar_is_loaded_and_exercised_before_model_work(monkeypatch, tmp_path):
    grammar = tmp_path / "grammar.ebnf"
    grammar.write_text("root ::= \"ok\"")
    seen = []

    class Grammar:
        @staticmethod
        def from_ebnf(source):
            seen.append(source)
            return object()

    fake = types.SimpleNamespace(Grammar=Grammar, __version__="test")
    monkeypatch.setitem(sys.modules, "xgrammar", fake)
    monkeypatch.setattr(importlib.metadata, "version", lambda name: "0.2.4")
    _, version = preflight.load_xgrammar(None, grammar)
    assert version == "0.2.4"
    assert seen == ['root ::= "ok"']


def test_xgrammar_absence_fails_before_model_work(monkeypatch, tmp_path):
    grammar = tmp_path / "grammar.ebnf"
    grammar.write_text("root ::= \"ok\"")
    monkeypatch.delitem(sys.modules, "xgrammar", raising=False)
    real_import = preflight.importlib.import_module

    def without_xgrammar(name):
        if name == "xgrammar":
            raise ModuleNotFoundError("missing xgrammar")
        return real_import(name)

    monkeypatch.setattr(preflight.importlib, "import_module", without_xgrammar)
    with pytest.raises(ValueError, match="unavailable before model loading"):
        preflight.load_xgrammar(None, grammar)


def test_dependency_only_entrypoint_never_imports_torch(monkeypatch, tmp_path, capsys):
    grammar = tmp_path / "grammar.ebnf"
    grammar.write_text("root ::= \"ok\"")
    monkeypatch.setattr(preflight, "load_xgrammar", lambda site_path, grammar_path: (object(), "0.2.2"))
    monkeypatch.setattr(sys, "argv", ["preflight", "--dependency-only", "--grammar", str(grammar)])
    preflight.main()
    receipt = __import__("json").loads(capsys.readouterr().out)
    assert receipt["kind"] == "xgrammar_dependency_preflight_v1"
    assert receipt["cuda_touched"] is False
