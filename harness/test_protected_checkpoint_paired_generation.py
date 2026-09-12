from pathlib import Path
from types import SimpleNamespace
import sys
import pytest

from tools import protected_checkpoint_paired_generation as paired


def test_frozen_contract_has_exactly_two_rows_two_arms_two_generations():
    assert len(paired.plan()) == 8
    assert {(row, arm) for row, arm, _ in paired.plan()} == {
        (47, "existing_decoder"), (47, "grammar_enforced"),
        (107, "existing_decoder"), (107, "grammar_enforced"),
    }


def test_generation_contract_is_bounded_and_provenanced():
    assert paired.MAX_NEW_TOKENS == 1024
    assert paired.SEED == 20261011
    assert paired.sha("frozen") == paired.sha(b"frozen")


def test_repeats_are_labeled_deterministic_not_independent_samples():
    metadata = paired.generation_metadata(47, "existing_decoder", 1)
    assert metadata["sampling_mode"] == "greedy"
    assert metadata["generation_role"] == "deterministic_replicate"
    assert metadata["independent_sample"] is False
    assert metadata["generation_seed"] == 20261482


def test_real_grammar_mask_smoke_precedes_large_model_loading():
    source = Path("tools/protected_checkpoint_paired_generation.py").read_text()
    assert "def smoke_grammar_mask_kernel(" in source
    assert source.index("smoke_grammar_mask_kernel(") < source.index("AutoModelForCausalLM.from_pretrained")


def test_generation_tokens_disable_extra_bos_and_validate_actual_tensor():
    class TokenIds:
        def __init__(self, ids):
            self.ids = ids

        def tolist(self):
            return self.ids

    class Tokenizer:
        def apply_chat_template(self, *args, **kwargs):
            return "<bos>already-rendered-chat"

        def __call__(self, text, *, return_tensors, add_special_tokens=True):
            assert text == "<bos>already-rendered-chat"
            ids = [128000, 123, 456]
            if add_special_tokens:
                ids.insert(0, 128000)
            return {"input_ids": [TokenIds(ids)]}

    encoding = {"input_ids": [128000, 123, 456, 999], "prompt_tokens": 3}
    actual = paired.frozen_inputs(Tokenizer(), "prompt", encoding)
    assert actual["input_ids"][0].tolist() == encoding["input_ids"][:3]
    with pytest.raises(ValueError, match="generation input token IDs differ"):
        paired.frozen_inputs(Tokenizer(), "prompt", {"input_ids": [1], "prompt_tokens": 1})


def test_greedy_selector_is_opt_in_and_receives_exact_compiled_grammar(monkeypatch):
    class Compiler:
        def __init__(self, info):
            assert info == ('tokenizer', 128256)

        def compile_grammar(self, grammar):
            assert grammar == 'frozen grammar'
            return 'compiled'

    xgr = SimpleNamespace(
        TokenizerInfo=SimpleNamespace(from_huggingface=lambda tokenizer, vocab_size: (tokenizer, vocab_size)),
        GrammarCompiler=Compiler,
        contrib=SimpleNamespace(hf=SimpleNamespace(LogitsProcessor=lambda compiled: ('dense', compiled))))
    fake = SimpleNamespace(GreedyGrammarSelector=lambda xgrammar, compiled, audit_steps:
                           ('greedy', compiled, audit_steps))
    monkeypatch.setitem(sys.modules, 'protected_greedy_grammar_selector', fake)
    assert paired.build_processor(xgr, 'tokenizer', 128256, 'frozen grammar') == ('dense', 'compiled')
    assert paired.build_processor(xgr, 'tokenizer', 128256, 'frozen grammar', selector='greedy', audit_steps=4) == (
        'greedy', 'compiled', 4)
    with pytest.raises(ValueError, match='unknown grammar selector'):
        paired.build_processor(xgr, 'tokenizer', 128256, 'frozen grammar', selector='unsafe')
