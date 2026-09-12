from pathlib import Path
import subprocess
import sys

import pytest

from tools import protected_reference_eos_replay as replay


class Tokenizer:
    def __init__(self, starts=None, decoded=None):
        self.starts = starts or [0, 1, 2, 7]
        self.decoded = decoded

    def __call__(self, text, *, add_special_tokens, return_offsets_mapping):
        assert not add_special_tokens and return_offsets_mapping
        return {"input_ids": [10, 11, 12, 13],
                "offset_mapping": [(s, s + 1) for s in self.starts]}

    def decode(self, ids):
        assert ids == [10, 11]
        return "A\n" if self.decoded is None else self.decoded


def test_split_reference_is_exact_token_boundary():
    ids, prefix_ids, prefix, split = replay.split_reference(Tokenizer(), "A\nNext == TRUE")
    assert ids == [10, 11, 12, 13]
    assert prefix_ids == [10, 11]
    assert prefix == "A\n" and split == 2


def test_marker_inside_token_is_rejected():
    with pytest.raises(ValueError, match="exact tokenizer boundary"):
        replay.split_reference(Tokenizer(starts=[0, 1, 3, 10]), "A\nNext == TRUE")


def test_decode_drift_is_rejected():
    with pytest.raises(ValueError, match="does not decode exactly"):
        replay.split_reference(Tokenizer(decoded="changed"), "A\nNext == TRUE")


def test_cli_help_needs_no_runtime_dependencies():
    script = Path(__file__).resolve().parents[1] / "tools/protected_reference_eos_replay.py"
    result = subprocess.run([sys.executable, str(script), "--help"], text=True, capture_output=True)
    assert result.returncode == 0, result.stderr
    assert all("--" + name in result.stdout for name in
               ("grammar", "corpus", "model", "xgrammar-site"))


def test_preflight_never_loads_model_weights():
    source = (Path(__file__).resolve().parents[1] /
              "tools/protected_reference_eos_replay.py").read_text()
    assert "AutoModel" not in source and "torch.load" not in source
    assert "model_weights_loaded=False" in source
