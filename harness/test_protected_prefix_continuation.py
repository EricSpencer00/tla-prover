from pathlib import Path
import shutil
import subprocess
import sys

import pytest

from tools import protected_prefix_continuation as continuation


class Vector:
    def __init__(self, values):
        self.values = values

    def __getitem__(self, index):
        return Vector(self.values[index])

    def tolist(self):
        return list(self.values)


class Tokenizer:
    def __init__(self, base, prefix):
        self.base = base
        self.prefix = prefix

    def apply_chat_template(self, messages, *, tokenize, add_generation_prompt):
        assert tokenize is False and add_generation_prompt is True
        return "HEADER:" + messages[0]["content"]

    def __call__(self, text, *, return_tensors, add_special_tokens):
        assert return_tensors == "pt" and add_special_tokens is False
        ids = self.base + (self.prefix if text.endswith("PREFIX") else [])
        return {"input_ids": Vector([ids]), "attention_mask": Vector([[1] * len(ids)])}


def test_frozen_plan_and_diagnostic_budget():
    assert continuation.plan() == [
        ("base", 47), ("base", 107),
        ("parent", 47), ("parent", 107),
        ("child", 47), ("child", 107),
    ]
    assert continuation.MAX_NEW_TOKENS == 256
    assert continuation.AUDIT_STEPS == 4
    assert continuation.PREFIX[47] == (
        "85691e1dd47493d3be2afd894e781bdaf6b77d3a8d43e9cae4fa26b8c0edbd5d",
        182, 226,
    )
    assert continuation.PREFIX[107] == (
        "2c70fbec2364b35a803dffb1b17b40b58abbc0c7ce34569cf015dbc6e9eb5326",
        488, 673,
    )
    assert all(prefix_tokens / reference_tokens > 0.70
               for _, prefix_tokens, reference_tokens in continuation.PREFIX.values())


def test_conditioned_input_preserves_frozen_user_tokens_and_exact_prefix():
    tokenizer = Tokenizer([1, 2, 3], [4, 5])
    encoding = {"input_ids": [1, 2, 3, 99], "prompt_tokens": 3}
    inputs, ids = continuation.conditioned_inputs(tokenizer, "prompt", encoding, "PREFIX")
    assert ids == [1, 2, 3, 4, 5]
    assert inputs["input_ids"][0].tolist() == ids


def test_conditioned_input_rejects_frozen_prompt_drift():
    tokenizer = Tokenizer([1, 2, 8], [4, 5])
    encoding = {"input_ids": [1, 2, 3], "prompt_tokens": 3}
    with pytest.raises(ValueError, match="unconditioned generation input"):
        continuation.conditioned_inputs(tokenizer, "prompt", encoding, "PREFIX")


def test_restricted_checkpoint_loading_has_no_unsafe_fallback(tmp_path):
    calls = []

    class Torch:
        @staticmethod
        def load(path, *, map_location, weights_only):
            calls.append((Path(path).name, map_location, weights_only))
            if Path(path).name == "parent.pt":
                raise RuntimeError("restricted loader rejected")

    parent, child = tmp_path / "parent.pt", tmp_path / "child.pt"
    parent.touch()
    child.touch()
    with pytest.raises(RuntimeError, match="restricted loader rejected"):
        continuation.load_states(Torch, parent, child, {})
    assert calls == [("parent.pt", "cpu", True)]


def test_source_is_fail_closed_and_diagnostic_only():
    source = (Path(__file__).resolve().parents[1] /
              "tools/protected_prefix_continuation.py").read_text()
    assert 'weights_only=True' in source
    assert 'weights_only=False' not in source
    assert 'training=False' in source
    assert 'supplied_reference_credit=False' in source
    assert 'gate_claim=False' in source and 'model_improvement_claim=False' in source
    assert source.index('if args.preflight_only:') < source.index('AutoModelForCausalLM')


def test_six_file_stage_help_needs_no_model_or_grammar_runtime(tmp_path):
    root = Path(__file__).resolve().parents[1]
    names = (
        "protected_prefix_continuation.py",
        "protected_checkpoint_preflight.py",
        "protected_checkpoint_paired_generation.py",
        "protected_reference_eos_replay.py",
        "protected_greedy_grammar_selector.py",
    )
    for name in names:
        shutil.copyfile(root / "tools" / name, tmp_path / name)
    result = subprocess.run(
        [sys.executable, "-B", "protected_prefix_continuation.py", "--help"],
        cwd=tmp_path, text=True, capture_output=True,
    )
    assert result.returncode == 0, result.stderr
    for name in ("packet", "corpus", "grammar", "model", "parent", "child",
                 "xgrammar-site", "output", "preflight-only"):
        assert "--" + name in result.stdout


def test_pbs_syntax_and_frozen_resource_contract():
    path = (Path(__file__).resolve().parents[1] /
            "tools/protected_prefix_continuation_polaris.pbs")
    subprocess.run(["bash", "-n", str(path)], check=True)
    source = path.read_text()
    assert "#PBS -q debug" in source and "ngpus=1" in source
    assert "walltime=00:15:00" in source and "840s" in source
    assert "--kill-after=10s" in source
    assert "STAGE=/home/eric-spencer/tla-prefix-continuation-20260912-v1" in source
    assert 'exec > "job.${PBS_JOBID%%.*}.log"' in source
    assert '--output "$STAGE/result.${PBS_JOBID%%.*}"' in source
    assert "qsub" not in source
