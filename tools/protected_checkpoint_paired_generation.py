#!/usr/bin/env python3
"""Direct frozen 2x2x2 generation from the restored protected checkpoint.

This is an evidence generator, not a SANY scorer or acceptance gate.  It keeps
the existing-decoder and XGrammar-enforced arms in one direct model process so
both arms use the same frozen tokenizer, base model, and restored tensors.
"""
import argparse
import hashlib
import json
from pathlib import Path

try:  # Script execution from a staged directory.
    import protected_checkpoint_preflight as preflight
except ModuleNotFoundError:  # Repository-package import used by focused tests.
    from tools import protected_checkpoint_preflight as preflight

ROWS = (47, 107)
ARMS = ("existing_decoder", "grammar_enforced")
GENERATIONS_PER_ROW = 2
MAX_NEW_TOKENS = 1024
SEED = 20261011


def sha(value):
    if isinstance(value, str):
        value = value.encode()
    return hashlib.sha256(value).hexdigest()


def plan():
    return [(row, arm, generation) for row in ROWS for arm in ARMS
            for generation in range(GENERATIONS_PER_ROW)]


def generation_metadata(row, arm, generation):
    # The frozen temperature-zero contract deliberately yields deterministic
    # repeats.  Seeds remain provenance fields, not independent-sample claims.
    return dict(row=row, arm=arm, generation=generation,
                generation_role="deterministic_replicate",
                sampling_mode="greedy", independent_sample=False,
                generation_seed=SEED + row * 10 + generation)


def build_processor(xgrammar, tokenizer, model, grammar):
    info = xgrammar.TokenizerInfo.from_huggingface(tokenizer, vocab_size=model.config.vocab_size)
    compiled = xgrammar.GrammarCompiler(info).compile_grammar(grammar)
    return xgrammar.contrib.hf.LogitsProcessor(compiled)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--grammar", type=Path, required=True)
    parser.add_argument("--xgrammar-site", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("append-only output already exists")
    if preflight.file_sha(args.packet) != preflight.PACKET_SHA:
        raise ValueError("frozen packet hash mismatch")

    # Dependency and grammar validation deliberately happen before Torch/CUDA.
    xgrammar, xgrammar_version = preflight.load_xgrammar(args.xgrammar_site, args.grammar)
    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")

    packet = json.loads(args.packet.read_text())
    selected_rows = preflight.protected_rows(packet)
    files = preflight.model_files(args.model)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    prompt_evidence = preflight.verify_prompt_tokens(tokenizer, selected_rows)
    saved = torch.load(args.checkpoint, map_location="cpu", weights_only=False)
    if saved.get("config", {}).get("model_files") != files or saved["config"].get("dtype_profile") != preflight.PROFILE:
        raise ValueError("checkpoint base model/dtype profile mismatch")
    model = transformers.AutoModelForCausalLM.from_pretrained(
        args.model, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa").to("cuda").eval().requires_grad_(False)
    last_layer = model.model.layers[-1]
    last_layer.to(dtype=torch.float32)
    trainable_ids = {id(parameter) for parameter in last_layer.parameters()}
    selected = {name: parameter for name, parameter in model.named_parameters()
                if id(parameter) in trainable_ids}
    preflight.restore_exact(selected, saved)
    grammar = args.grammar.read_text()

    args.output.mkdir(parents=True)
    records = []
    with torch.inference_mode():
        for row, arm, generation in plan():
            prompt = selected_rows[row][0]["prompt"]
            rendered = tokenizer.apply_chat_template(
                [{"role": "user", "content": prompt}], tokenize=False, add_generation_prompt=True)
            inputs = tokenizer(rendered, return_tensors="pt").to("cuda")
            metadata = generation_metadata(row, arm, generation)
            torch.manual_seed(metadata["generation_seed"])
            kwargs = dict(max_new_tokens=MAX_NEW_TOKENS, do_sample=False,
                          pad_token_id=tokenizer.eos_token_id)
            if arm == "grammar_enforced":
                # A new processor per candidate prevents cross-candidate
                # matcher state from contaminating the paired measurement.
                kwargs["logits_processor"] = [build_processor(xgrammar, tokenizer, model, grammar)]
            with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
                generated = model.generate(**inputs, **kwargs)
            new_ids = generated[0][inputs.input_ids.shape[1]:]
            text = tokenizer.decode(new_ids, skip_special_tokens=True)
            record = dict(**metadata, base_prompt_sha256=sha(prompt), raw_reply=text,
                          raw_reply_sha256=sha(text), output_token_count=len(new_ids),
                          grammar_enforced=(arm == "grammar_enforced"))
            records.append(record)
            (args.output / f"row-{row}-{arm}-{generation}.json").write_text(
                json.dumps(record, indent=2) + "\n")
    receipt = dict(kind="protected_checkpoint_paired_generation_v1", complete=True,
                   contract=dict(rows=list(ROWS), arms=list(ARMS),
                                 generations_per_row=GENERATIONS_PER_ROW,
                                 max_new_tokens=MAX_NEW_TOKENS, seed=SEED,
                                 sampling_mode="greedy deterministic repeats",
                                 independent_samples=False),
                   packet_sha256=preflight.PACKET_SHA,
                   checkpoint_sha256=preflight.file_sha(args.checkpoint),
                   model_files=files, restored_parameter_count=len(selected),
                   restored_tensors_exact=True, protected_prompt_tokens=prompt_evidence,
                   grammar_sha256=sha(grammar), grammar_compiled=True,
                   xgrammar_version=xgrammar_version, xgrammar_site=str(args.xgrammar_site),
                   records=records, producer="direct_checkpoint_generation",
                   gate_claim=False)
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(dict(kind=receipt["kind"], records=len(records),
                          restored_tensors_exact=True, grammar_compiled=True,
                          gate_claim=False), sort_keys=True))


if __name__ == "__main__":
    main()
