#!/usr/bin/env python3
"""Six frozen greedy generations for the sequence-trained child; no scoring."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

try:  # Three-file isolated PBS stage.
    import protected_checkpoint_preflight as preflight
    import protected_checkpoint_paired_generation as paired
except ModuleNotFoundError:
    from tools import protected_checkpoint_preflight as preflight
    from tools import protected_checkpoint_paired_generation as paired

PHASES = ("base", "parent", "child")
ROWS = (47, 107)
PROMPT_TOKENS = {47: 401, 107: 457}
MAX_NEW_TOKENS = 1024
SEED = 20261011
PARENT_SHA = "b0399b51aed001051fe200751b3087fc008482ca9dfeb64eb12884f71eee3bb6"
CHILD_SHA = "7859aabdcc3bcc73b853c3527be88327e3c9f2cdb4b71a7005331525293d50ee"


def plan():
    return [(phase, row) for phase in PHASES for row in ROWS]


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_new(path, value):
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("packet", "model", "parent", "child", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("append-only output already exists")
    for path, expected, label in (
        (args.packet, preflight.PACKET_SHA, "packet"),
        (args.parent, PARENT_SHA, "parent"),
        (args.child, CHILD_SHA, "child"),
    ):
        if file_sha(path) != expected:
            raise ValueError(f"frozen {label} hash mismatch")

    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    selected_rows = preflight.protected_rows(json.loads(args.packet.read_text()))
    files = preflight.model_files(args.model)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    prompt_evidence = preflight.verify_prompt_tokens(tokenizer, selected_rows)
    for row in ROWS:
        if prompt_evidence[str(row)]["prompt_tokens"] != PROMPT_TOKENS[row]:
            raise ValueError("frozen prompt token count mismatch")
        # Also exercise the exact input construction before any model generation.
        source, encoding = selected_rows[row]
        paired.frozen_inputs(tokenizer, source["prompt"], encoding)

    states, configs = {}, {}
    for phase in ("parent", "child"):
        saved = torch.load(getattr(args, phase), map_location="cpu", weights_only=True)
        config = saved.get("config", {})
        if config.get("model_files") != files or config.get("dtype_profile") != preflight.PROFILE:
            raise ValueError(f"{phase} checkpoint base model/dtype profile mismatch")
        if phase == "child":
            parent_sha = (config.get("parent_sha256") or
                          config.get("parent_checkpoint_sha256") or
                          config.get("checkpoint_sha256"))
            if parent_sha != PARENT_SHA:
                raise ValueError("child checkpoint parent lineage mismatch")
        states[phase] = {"trainable_state": saved.get("trainable_state")}
        configs[phase] = {key: config[key] for key in (
            "dtype_profile", "model_files", "parent_sha256", "parent_checkpoint_sha256",
            "kind", "schema") if key in config}
        del saved  # Optimizer state is never used or retained.

    model = transformers.AutoModelForCausalLM.from_pretrained(
        args.model, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa").to("cuda").eval().requires_grad_(False)
    layer = model.model.layers[-1]
    layer.to(dtype=torch.float32)
    layer_ids = {id(parameter) for parameter in layer.parameters()}
    selected = {name: parameter for name, parameter in model.named_parameters()
                if id(parameter) in layer_ids}
    if len(selected) != 9 or len(layer_ids) != 9:
        raise ValueError("expected exactly 9 final-layer tensors")
    # Capture the unmodified base BEFORE any restore; no checkpoint is written.
    states["base"] = {"trainable_state": {
        name: parameter.detach().cpu().clone() for name, parameter in selected.items()}}
    for phase in PHASES:
        state = states[phase]["trainable_state"]
        if not isinstance(state, dict) or set(state) != set(selected):
            raise ValueError(f"{phase} checkpoint trainable tensor names mismatch")
        for name, parameter in selected.items():
            value = state[name]
            if (value.dtype != torch.float32 or value.dtype != parameter.dtype
                    or value.shape != parameter.shape or not torch.isfinite(value).all()):
                raise ValueError(f"{phase} checkpoint tensor mismatch: {name}")

    kwargs = dict(max_new_tokens=MAX_NEW_TOKENS, do_sample=False,
                  pad_token_id=tokenizer.eos_token_id)
    paired.validate_greedy_configuration(model, kwargs)
    effective, _ = model._prepare_generation_config(None, **kwargs)
    eos_ids = effective.eos_token_id
    eos_ids = [eos_ids] if isinstance(eos_ids, int) else eos_ids
    if not eos_ids or any(not isinstance(token, int) for token in eos_ids):
        raise ValueError("effective EOS token IDs unavailable")

    provenance = dict(
        producer="direct_lineage_generation", interpreter=sys.executable,
        torch=torch.__version__, transformers=transformers.__version__,
        cuda_device=torch.cuda.get_device_name(), dtype_profile=preflight.PROFILE,
        paths={name: str(getattr(args, name).resolve())
               for name in ("packet", "model", "parent", "child")},
        source_sha256={Path(path).name: file_sha(path)
                       for path in (__file__, preflight.__file__, paired.__file__)})
    contract = dict(phases=list(PHASES), rows=list(ROWS),
                    ordered_plan=[dict(phase=phase, row=row) for phase, row in plan()],
                    generations_per_phase_row=1, max_new_tokens=MAX_NEW_TOKENS,
                    seed=SEED, seed_rule="SEED + row * 10", sampling_mode="greedy",
                    grammar_enforced=False, reference_conditioning=False, training=False,
                    eos_token_ids=eos_ids, input_transform="none; frozen user chat template")
    args.output.mkdir(parents=True, exist_ok=False)
    records, phase_weights = [], {}
    started = time.monotonic()
    with torch.inference_mode():
        for phase in PHASES:
            if phase != "base":
                preflight.restore_exact(selected, states[phase])
            state = states[phase]["trainable_state"]
            if not all(torch.equal(parameter.detach().cpu(), state[name])
                       for name, parameter in selected.items()):
                raise ValueError(f"{phase} actual final-layer weights differ")
            identity = dict(
                phase=phase, model_files=files, dtype_profile=preflight.PROFILE,
                checkpoint_sha256={"base": None, "parent": PARENT_SHA, "child": CHILD_SHA}[phase],
                checkpoint_config=configs.get(phase), final_layer_tensor_count=9,
                restored_parameter_count=0 if phase == "base" else 9,
                restored_tensors_exact=phase != "base", actual_tensors_exact=True,
                final_layer_sha256={name: paired.sha(value.contiguous().numpy().tobytes())
                                    for name, value in state.items()})
            phase_weights[phase] = identity
            write_new(args.output / f"weights-{phase}.json", identity)
            for row in ROWS:
                source, encoding = selected_rows[row]
                inputs = paired.frozen_inputs(tokenizer, source["prompt"], encoding).to("cuda")
                input_ids = inputs["input_ids"][0].tolist()
                if (len(input_ids) != PROMPT_TOKENS[row]
                        or input_ids != encoding["input_ids"][:encoding["prompt_tokens"]]):
                    raise ValueError("actual device prompt differs from frozen packet")
                seed = SEED + row * 10
                torch.manual_seed(seed)
                resolved = paired.validate_greedy_configuration(model, kwargs)
                torch.cuda.synchronize()
                generation_started = time.monotonic()
                with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
                    generated = model.generate(**inputs, **kwargs)
                torch.cuda.synchronize()
                seconds = time.monotonic() - generation_started
                full_ids = generated[0].tolist()
                if full_ids[:len(input_ids)] != input_ids:
                    raise ValueError("generated sequence changed the frozen input prefix")
                output_ids = full_ids[len(input_ids):]
                if not output_ids or len(output_ids) > MAX_NEW_TOKENS:
                    raise ValueError("generated response outside frozen token budget")
                text = tokenizer.decode(output_ids, skip_special_tokens=True)
                ended = output_ids[-1] in eos_ids
                record = dict(
                    phase=phase, row=row, generation_seed=seed, resolved_decode=resolved,
                    base_prompt_sha256=paired.sha(source["prompt"]), raw_reply=text,
                    raw_reply_sha256=paired.sha(text), actual_prompt_token_count=len(input_ids),
                    actual_prompt_tokens_match_frozen=True, actual_prompt_token_ids=input_ids,
                    output_token_ids=output_ids, full_sequence_token_ids=full_ids,
                    output_token_count=len(output_ids), eos_ended=ended,
                    finish_reason="eos" if ended else "token_limit" if len(output_ids) == MAX_NEW_TOKENS else "other_stop",
                    wall_seconds=seconds, weights_identity=identity,
                    sampling_mode="greedy", independent_sample=False,
                    grammar_enforced=False, producer="direct_lineage_generation")
                write_new(args.output / f"row-{row}-{phase}.json", record)
                records.append(record)
                print(json.dumps(dict(phase=phase, row=row, output_tokens=len(output_ids),
                                      eos_ended=ended)), flush=True)
    if [(record["phase"], record["row"]) for record in records] != plan():
        raise ValueError("incomplete or reordered lineage plan")
    receipt = dict(
        kind="protected_lineage_generation_v1", complete=True, contract=contract,
        packet_sha256=preflight.PACKET_SHA, parent_checkpoint_sha256=PARENT_SHA,
        child_checkpoint_sha256=CHILD_SHA, model_files=files,
        protected_prompt_tokens=prompt_evidence, phase_weights=phase_weights,
        provenance=provenance, records=records, wall_seconds=time.monotonic() - started,
        producer="direct_lineage_generation", gate_claim=False, model_improvement_claim=False)
    write_new(args.output / "receipt.json", receipt)


if __name__ == "__main__":
    main()
