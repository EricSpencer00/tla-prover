from pathlib import Path

from tools.proof_action_signature_cuda_train import prompt_encoding


class FakeTokenizer:
    def apply_chat_template(self, messages, tokenize, add_generation_prompt):
        assert tokenize is False
        assert add_generation_prompt is True
        assert messages[0]["role"] == "user"
        return "<user>" + messages[0]["content"] + "<assistant>"

    def __call__(self, rendered, add_special_tokens, truncation):
        assert add_special_tokens is False
        assert truncation is False
        return {"input_ids": list(range(1, len(rendered) + 1))}


def test_prompt_encoding_has_no_candidate_response():
    encoded = prompt_encoding(FakeTokenizer(), "theorem=TypeInvariant")
    assert encoded["input_ids"]
    assert encoded["prompt_sha256"]

