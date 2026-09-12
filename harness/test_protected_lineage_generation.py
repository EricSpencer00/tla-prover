"""CPU-only fake runtime exercises the actual lineage CLI and shared helpers."""
from contextlib import contextmanager
import copy
import json
import math
from pathlib import Path
import shutil
import struct
import subprocess
import sys
from types import SimpleNamespace

import pytest

from tools import protected_lineage_generation as lineage


class Tensor:
    def __init__(self, values, dtype="float32"):
        self.values = copy.deepcopy(values)
        self.dtype = dtype
        self.device = "cpu"

    @property
    def shape(self):
        return (len(self.values), len(self.values[0])) if self.values and isinstance(self.values[0], list) else (len(self.values),)

    def __getitem__(self, index):
        return Tensor(self.values[index], self.dtype)

    def tolist(self):
        return copy.deepcopy(self.values)

    def to(self, device=None, dtype=None):
        if device:
            self.device = device
        if dtype:
            self.dtype = dtype
        return self

    def detach(self):
        return self

    def cpu(self):
        return self.clone().to("cpu")

    def clone(self):
        return Tensor(self.values, self.dtype)

    def copy_(self, other):
        self.values = copy.deepcopy(other.values)
        return self

    def contiguous(self):
        return self

    def numpy(self):
        return SimpleNamespace(tobytes=lambda: struct.pack("<" + "f" * len(self.values), *self.values))


class Inputs(dict):
    def to(self, device):
        for tensor in self.values():
            tensor.to(device)
        return self


@pytest.fixture
def runtime(tmp_path, monkeypatch):
    state = SimpleNamespace(calls=[], loads=[], seeds=[], restores=[], model_loads=0,
                            fail_call=None, bad_actual=False, bad_generated_prefix=False,
                            beam=False, no_eos=False, bad_restore=False, inference=0, autocast=0,
                            parameter_count=9, decode_calls=[])
    model_dir = tmp_path / "model"
    model_dir.mkdir()
    (model_dir / "config.json").write_text('{}')
    (model_dir / "model.safetensors").write_bytes(b"tiny fake model")
    files = lineage.preflight.model_files(model_dir)
    packet = dict(rows=[], encodings=[])
    for row in lineage.ROWS:
        prompt = f"prompt-{row}"
        ids = [row] * lineage.PROMPT_TOKENS[row]
        packet["rows"].append(dict(id=lineage.preflight.WANTED_IDS[row], prompt=prompt,
                                   response="REFERENCE MUST NEVER REACH GENERATE"))
        packet["encodings"].append(dict(input_ids=ids + [999999], prompt_tokens=len(ids)))
    packet_path = tmp_path / "packet.json"
    packet_path.write_text(json.dumps(packet))
    monkeypatch.setattr(lineage.preflight, "PACKET_SHA", lineage.file_sha(packet_path))
    names = [f"model.layers.31.parameter{i}" for i in range(9)]
    paths = {}
    for phase, offset in (("parent", 10), ("child", 20)):
        paths[phase] = tmp_path / f"{phase}.pt"
        config = dict(model_files=files, dtype_profile=lineage.preflight.PROFILE,
                      encodings=["large training metadata must not be serialized"], trainids=[1, 2])
        if phase == "child":
            config["parent_sha256"] = lineage.PARENT_SHA
        saved = dict(config=config, trainable_state={
            name: dict(values=[offset + i + .25], dtype="float32") for i, name in enumerate(names)})
        paths[phase].write_text(json.dumps(saved))
        monkeypatch.setattr(lineage, phase.upper() + "_SHA", lineage.file_sha(paths[phase]))
    output = tmp_path / "output"
    argv = ["lineage", "--packet", str(packet_path), "--model", str(model_dir),
            "--parent", str(paths["parent"]), "--child", str(paths["child"]), "--output", str(output)]
    monkeypatch.setattr(sys, "argv", argv)

    @contextmanager
    def context(name):
        setattr(state, name, getattr(state, name) + 1)
        try:
            yield
        finally:
            setattr(state, name, getattr(state, name) - 1)

    def load(path, *, map_location, weights_only):
        assert map_location == "cpu" and weights_only is True
        state.loads.append(Path(path).name)
        saved = json.loads(Path(path).read_text())
        saved["trainable_state"] = {name: Tensor(**value) for name, value in saved["trainable_state"].items()}
        return saved

    torch = SimpleNamespace(
        __version__="fake-cpu", bfloat16="bfloat16", float32="float32", load=load,
        cuda=SimpleNamespace(is_available=lambda: True, is_bf16_supported=lambda: True,
                             get_device_name=lambda: "fake CPU runtime, not GPU evidence",
                             synchronize=lambda: None),
        manual_seed=state.seeds.append,
        no_grad=lambda: context("inference"), inference_mode=lambda: context("inference"),
        autocast=lambda **kwargs: context("autocast"),
        equal=lambda left, right: left.values == right.values and left.dtype == right.dtype,
        isfinite=lambda tensor: SimpleNamespace(all=lambda: all(math.isfinite(v) for v in tensor.values)))
    monkeypatch.setitem(sys.modules, "torch", torch)

    class Tokenizer:
        eos_token_id = 128009

        def apply_chat_template(self, messages, *, tokenize, add_generation_prompt):
            assert len(messages) == 1 and messages[0]["role"] == "user"
            assert tokenize is False and add_generation_prompt is True
            return messages[0]["content"]

        def encode(self, text, *, add_special_tokens):
            assert add_special_tokens is False
            row = int(text.split("-")[1])
            return [row] * lineage.PROMPT_TOKENS[row]

        def __call__(self, text, *, return_tensors, add_special_tokens):
            assert return_tensors == "pt" and add_special_tokens is False
            ids = self.encode(text, add_special_tokens=False)
            if state.bad_actual:
                ids[0] += 1
            return Inputs(input_ids=Tensor([ids], "int64"), attention_mask=Tensor([[1] * len(ids)], "int64"))

        def decode(self, ids, *, skip_special_tokens):
            assert skip_special_tokens is True
            state.decode_calls.append(ids)
            return "raw malformed output " + str(ids[0])

    class Model:
        def __init__(self):
            self.params = {name: Tensor([i + .25], "bfloat16")
                           for i, name in enumerate(names[:state.parameter_count])}
            self.generation_config = SimpleNamespace(num_beams=None)
            self.model = SimpleNamespace(layers=[SimpleNamespace(
                to=lambda *, dtype: [value.to(dtype=dtype) for value in self.params.values()],
                parameters=lambda: self.params.values())])
            self.eval_called = False
            self.no_grad_called = False

        def to(self, device):
            assert device == "cuda"
            return self

        def eval(self):
            self.eval_called = True
            return self

        def requires_grad_(self, enabled):
            assert enabled is False
            self.no_grad_called = True
            return self

        def named_parameters(self):
            return self.params.items()

        def _prepare_generation_config(self, config, **kwargs):
            assert config is None
            assert kwargs == dict(max_new_tokens=1024, do_sample=False, pad_token_id=128009)
            resolved = SimpleNamespace(num_beams=2 if state.beam else 1, do_sample=False,
                                       eos_token_id=None if state.no_eos else [128001, 128008, 128009],
                                       get_generation_mode=lambda: "greedy_search")
            return resolved, {}

        def generate(self, *, input_ids, attention_mask, **kwargs):
            assert self.eval_called and self.no_grad_called
            assert state.inference and state.autocast
            assert all(value.dtype == "float32" for value in self.params.values())
            self._prepare_generation_config(None, **kwargs)
            ids = input_ids[0].tolist()
            row = ids[0]
            assert ids == [row] * lineage.PROMPT_TOKENS[row]
            assert attention_mask.values == [[1] * len(ids)]
            weight = self.params[names[0]].values[0]
            state.calls.append((weight, row))
            if len(state.calls) == state.fail_call:
                raise RuntimeError("injected generation failure")
            suffix = [42] * 1024 if weight == 10.25 else [int(weight), 128009]
            if state.bad_generated_prefix:
                ids[0] = 999
            return Tensor([ids + suffix], "int64")

    def from_pretrained(path, **kwargs):
        assert path == model_dir
        assert kwargs == dict(local_files_only=True, torch_dtype="bfloat16", attn_implementation="sdpa")
        assert state.loads == ["parent.pt", "child.pt"]
        state.model_loads += 1
        state.model = Model()
        return state.model

    def tokenizer_from_pretrained(path, **kwargs):
        assert path == model_dir and kwargs == {"local_files_only": True}
        return Tokenizer()

    transformers = SimpleNamespace(
        __version__="fake-cpu", AutoTokenizer=SimpleNamespace(from_pretrained=tokenizer_from_pretrained),
        AutoModelForCausalLM=SimpleNamespace(from_pretrained=from_pretrained))
    monkeypatch.setitem(sys.modules, "transformers", transformers)
    real_restore = lineage.preflight.restore_exact

    def tracked_restore(selected, saved):
        state.restores.append(saved["trainable_state"][names[0]].values[0])
        real_restore(selected, saved)  # Real shared restore verification, fake tensor arithmetic.
        if state.bad_restore:
            selected[names[0]].values[0] += 1

    monkeypatch.setattr(lineage.preflight, "restore_exact", tracked_restore)

    def change_checkpoint(phase, change):
        value = json.loads(paths[phase].read_text())
        change(value)
        paths[phase].write_text(json.dumps(value))
        monkeypatch.setattr(lineage, phase.upper() + "_SHA", lineage.file_sha(paths[phase]))
        if phase == "parent":
            change_checkpoint("child", lambda child: child["config"].update(parent_sha256=lineage.PARENT_SHA))

    state.output, state.paths, state.packet_path = output, paths, packet_path
    state.change_checkpoint = change_checkpoint
    state.torch = torch
    return state


def test_full_cli_six_generations_restore_order_and_scorer_contract(runtime):
    lineage.main()
    receipt = json.loads((runtime.output / "receipt.json").read_text())
    assert receipt["complete"] and not receipt["gate_claim"]
    assert runtime.model_loads == 1
    assert runtime.calls == [(offset + .25, row) for offset in (0, 10, 20) for row in (47, 107)]
    assert runtime.restores == [10.25, 20.25]
    assert runtime.seeds == [lineage.SEED + row * 10 for _, row in lineage.plan()]
    assert [(r["phase"], r["row"]) for r in receipt["records"]] == lineage.plan()
    assert receipt["contract"]["ordered_plan"] == [dict(phase=p, row=r) for p, r in lineage.plan()]
    assert receipt["provenance"]["torch"] == "fake-cpu"
    assert len(receipt["provenance"]["source_sha256"]) == 3
    required = {"base_prompt_sha256", "raw_reply", "raw_reply_sha256", "actual_prompt_token_count",
                "actual_prompt_tokens_match_frozen", "actual_prompt_token_ids", "output_token_ids",
                "generation_seed", "resolved_decode"}
    for record in receipt["records"]:
        phase, row = record["phase"], record["row"]
        assert required <= record.keys()
        assert json.loads((runtime.output / f"row-{row}-{phase}.json").read_text()) == record
        assert record["base_prompt_sha256"] == lineage.paired.sha(f"prompt-{row}")
        assert record["actual_prompt_token_ids"] == [row] * lineage.PROMPT_TOKENS[row]
        assert record["actual_prompt_token_count"] == lineage.PROMPT_TOKENS[row]
        assert record["actual_prompt_tokens_match_frozen"] is True
        assert record["raw_reply"].startswith("raw malformed output")
        assert record["raw_reply_sha256"] == lineage.paired.sha(record["raw_reply"])
        assert record["output_token_count"] == len(record["output_token_ids"])
        assert record["full_sequence_token_ids"] == record["actual_prompt_token_ids"] + record["output_token_ids"]
        assert record["eos_ended"] == (phase != "parent")
        assert record["finish_reason"] == ("token_limit" if phase == "parent" else "eos")
        assert record["resolved_decode"]["effective_mode"] == "greedy_search"
        assert record["wall_seconds"] >= 0
        weights = record["weights_identity"]
        assert weights == receipt["phase_weights"][phase]
        assert len(weights["final_layer_sha256"]) == 9 and weights["actual_tensors_exact"]
        assert weights["restored_parameter_count"] == (0 if phase == "base" else 9)
        if phase != "base":
            assert "encodings" not in weights["checkpoint_config"]
            assert "trainids" not in weights["checkpoint_config"]
    assert len({r["weights_identity"]["final_layer_sha256"]["model.layers.31.parameter0"]
                for r in receipt["records"]}) == 3


@pytest.mark.parametrize("target", ["packet", "parent", "child"])
def test_hash_drift_fails_before_any_model_load(runtime, target):
    path = runtime.packet_path if target == "packet" else runtime.paths[target]
    path.write_bytes(path.read_bytes() + b" ")
    with pytest.raises(ValueError, match=f"{target} hash mismatch"):
        lineage.main()
    assert not runtime.loads and not runtime.calls and not runtime.model_loads
    assert not runtime.output.exists()


@pytest.mark.parametrize("phase", ["parent", "child"])
@pytest.mark.parametrize("field", ["model_files", "dtype_profile"])
def test_checkpoint_metadata_fails_before_generation(runtime, phase, field):
    runtime.change_checkpoint(phase, lambda saved: saved["config"].update({field: "wrong"}))
    with pytest.raises(ValueError, match="base model/dtype profile mismatch"):
        lineage.main()
    assert not runtime.calls and not runtime.model_loads


def test_child_lineage_mismatch_fails_before_base(runtime):
    runtime.change_checkpoint("child", lambda saved: saved["config"].update(parent_sha256="wrong"))
    with pytest.raises(ValueError, match="parent lineage mismatch"):
        lineage.main()
    assert not runtime.calls and not runtime.model_loads


def test_restricted_loader_failure_has_no_unsafe_retry(runtime):
    attempts = []

    def rejected(path, *, map_location, weights_only):
        attempts.append(weights_only)
        raise RuntimeError("restricted checkpoint loader rejected payload")

    runtime.torch.load = rejected
    with pytest.raises(RuntimeError, match="restricted checkpoint loader rejected"):
        lineage.main()
    assert attempts == [True]
    assert not runtime.calls and not runtime.model_loads
    assert not runtime.output.exists()


@pytest.mark.parametrize("phase", ["parent", "child"])
@pytest.mark.parametrize("defect", ["names", "shape", "dtype", "nonfinite"])
def test_all_checkpoint_tensors_checked_before_base_generation(runtime, phase, defect):
    def damage(saved):
        tensors = saved["trainable_state"]
        name = next(iter(tensors))
        if defect == "names":
            del tensors[name]
        elif defect == "shape":
            tensors[name]["values"] = [1, 2]
        elif defect == "dtype":
            tensors[name]["dtype"] = "bfloat16"
        else:
            tensors[name]["values"] = [float("nan")]
    runtime.change_checkpoint(phase, damage)
    with pytest.raises(ValueError, match="tensor.*mismatch"):
        lineage.main()
    assert not runtime.calls and not runtime.restores
    assert not runtime.output.exists()


def test_exactly_nine_model_tensors_required(runtime):
    runtime.parameter_count = 8
    with pytest.raises(ValueError, match="exactly 9"):
        lineage.main()
    assert not runtime.calls


def test_actual_tokenizer_path_must_match_preflight(runtime):
    runtime.bad_actual = True
    with pytest.raises(ValueError, match="generation input token IDs differ"):
        lineage.main()
    assert not runtime.calls and not runtime.model_loads


@pytest.mark.parametrize("flag,pattern", [("beam", "single-beam"), ("no_eos", "EOS")])
def test_effective_decoding_fails_closed(runtime, flag, pattern):
    setattr(runtime, flag, True)
    with pytest.raises(ValueError, match=pattern):
        lineage.main()
    assert not runtime.calls and not runtime.output.exists()


def test_cpu_or_no_bf16_is_rejected(runtime):
    runtime.torch.cuda.is_bf16_supported = lambda: False
    with pytest.raises(ValueError, match="CUDA bf16"):
        lineage.main()
    assert not runtime.loads and not runtime.model_loads


def test_partial_records_survive_generation_failure_and_rerun_is_rejected(runtime):
    runtime.fail_call = 4
    with pytest.raises(RuntimeError, match="injected generation"):
        lineage.main()
    assert len(list(runtime.output.glob("row-*.json"))) == 3
    assert not (runtime.output / "receipt.json").exists()
    original = {path.name: path.read_bytes() for path in runtime.output.iterdir()}
    with pytest.raises(ValueError, match="append-only"):
        lineage.main()
    assert original == {path.name: path.read_bytes() for path in runtime.output.iterdir()}


def test_actual_restoration_is_checked(runtime):
    runtime.bad_restore = True
    with pytest.raises(ValueError, match="actual final-layer weights differ"):
        lineage.main()
    assert len(runtime.calls) == 2
    assert not (runtime.output / "receipt.json").exists()


def test_generation_cannot_change_prompt_prefix(runtime):
    runtime.bad_generated_prefix = True
    with pytest.raises(ValueError, match="changed the frozen input prefix"):
        lineage.main()
    assert not list(runtime.output.glob("row-*.json"))


def test_exclusive_record_write_preserves_existing_bytes(tmp_path):
    path = tmp_path / "record.json"
    path.write_bytes(b"keep")
    with pytest.raises(FileExistsError):
        lineage.write_new(path, {"overwrite": True})
    assert path.read_bytes() == b"keep"


def test_three_file_stage_help_needs_no_model_or_grammar_runtime(tmp_path):
    root = Path(__file__).resolve().parents[1]
    for name in ("protected_lineage_generation.py", "protected_checkpoint_preflight.py",
                 "protected_checkpoint_paired_generation.py"):
        shutil.copyfile(root / "tools" / name, tmp_path / name)
    result = subprocess.run([sys.executable, "-B", "protected_lineage_generation.py", "--help"],
                            cwd=tmp_path, text=True, capture_output=True)
    assert result.returncode == 0, result.stderr
    for name in ("packet", "model", "parent", "child", "output"):
        assert "--" + name in result.stdout


def test_pbs_syntax_and_frozen_resource_contract():
    path = Path(__file__).resolve().parents[1] / "tools/protected_lineage_polaris.pbs"
    subprocess.run(["bash", "-n", str(path)], check=True)
    source = path.read_text()
    assert "#PBS -q debug" in source and "ngpus=1" in source
    assert "walltime=00:15:00" in source and "840s" in source
    assert "--kill-after=10s" in source
    assert "STAGE=/home/eric-spencer/tla-lineage-generation-20260912-v1" in source
    assert 'exec > "job.${PBS_JOBID%%.*}.log"' in source
    assert '--output "$STAGE/result.${PBS_JOBID%%.*}"' in source
    assert "--grammar" not in source and "--checkpoint" not in source
