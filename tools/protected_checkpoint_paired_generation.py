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


def build_processor(xgrammar, tokenizer, vocab_size, grammar, *, selector="dense", audit_steps=4):
    info = xgrammar.TokenizerInfo.from_huggingface(tokenizer, vocab_size=vocab_size)
    compiled = xgrammar.GrammarCompiler(info).compile_grammar(grammar)
    if selector == "greedy":
        try:
            from protected_greedy_grammar_selector import GreedyGrammarSelector
        except ModuleNotFoundError:
            from tools.protected_greedy_grammar_selector import GreedyGrammarSelector
        return GreedyGrammarSelector(xgrammar, compiled, audit_steps=audit_steps)
    if selector != "dense":
        raise ValueError("unknown grammar selector")
    return xgrammar.contrib.hf.LogitsProcessor(compiled)


def frozen_inputs(tokenizer, prompt, encoding):
    """Validate the very tensors used by generate, not a parallel encoding path."""
    rendered = tokenizer.apply_chat_template(
        [{"role": "user", "content": prompt}], tokenize=False, add_generation_prompt=True)
    inputs = tokenizer(rendered, return_tensors="pt", add_special_tokens=False)
    actual = inputs["input_ids"][0].tolist()
    expected = encoding["input_ids"][:encoding["prompt_tokens"]]
    if actual != expected:
        raise ValueError("generation input token IDs differ from frozen packet")
    return inputs


def smoke_grammar_mask_kernel(torch, processor, tokenizer, vocab_size):
    """Exercise XGrammar's real CUDA mask kernel before loading the 8B model."""
    token_id = tokenizer.eos_token_id if tokenizer.eos_token_id is not None else 0
    input_ids = torch.tensor([[token_id]], device="cuda", dtype=torch.long)
    scores = torch.zeros((1, vocab_size), device="cuda", dtype=torch.float32)
    processor(input_ids, scores)


def smoke_ranked_selector_cuda(torch, xgrammar):
    """Close the local CUDA-test gap before loading weights; no model answers."""
    try:
        from protected_greedy_grammar_selector import GreedyGrammarSelector
    except ModuleNotFoundError:
        from tools.protected_greedy_grammar_selector import GreedyGrammarSelector
    info = xgrammar.TokenizerInfo(['ax', 'a', 'b', 'ab', 'x', '<eos>'], stop_token_ids=[5])
    compiled = xgrammar.GrammarCompiler(info).compile_grammar('root ::= "ab"')
    selector = GreedyGrammarSelector(xgrammar, compiled, audit_steps=3)
    inputs = torch.tensor([[4, 4]], device='cuda', dtype=torch.long)
    scores = torch.tensor([[10., 9., 8., 7., 6., 11.]], device='cuda')
    for expected in (1, 2, 5):
        actual = int(selector(inputs, scores).argmax())
        if actual != expected:
            raise ValueError('ranked CUDA control differs from expected dense selection')
        inputs = torch.cat([inputs, torch.tensor([[actual]], device='cuda')], dim=1)
    selector.validate_generated([1, 2, 5])
    if not selector.matcher.is_terminated() or selector.audit_count != 3:
        raise ValueError('ranked CUDA termination/audit control failed')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--grammar", type=Path, required=True)
    parser.add_argument("--xgrammar-site", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--grammar-selector", choices=("dense", "greedy"), default="dense")
    parser.add_argument("--greedy-audit-steps", type=int, default=4)
    args = parser.parse_args()
    if args.greedy_audit_steps < 0:
        raise ValueError("negative audit step count")
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
    vocab_size = tokenizer.vocab_size
    smoke_processor = build_processor(xgrammar, tokenizer, vocab_size, args.grammar.read_text())
    smoke_grammar_mask_kernel(torch, smoke_processor, tokenizer, vocab_size)
    if args.grammar_selector == "greedy":
        smoke_ranked_selector_cuda(torch, xgrammar)
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
            packet_row, encoding = selected_rows[row]
            prompt = packet_row["prompt"]
            inputs = frozen_inputs(tokenizer, prompt, encoding).to("cuda")
            metadata = generation_metadata(row, arm, generation)
            torch.manual_seed(metadata["generation_seed"])
            kwargs = dict(max_new_tokens=MAX_NEW_TOKENS, do_sample=False,
                          pad_token_id=tokenizer.eos_token_id)
            processor = None
            if arm == "grammar_enforced":
                # A new processor per candidate prevents cross-candidate
                # matcher state from contaminating the paired measurement.
                processor = build_processor(xgrammar, tokenizer, model.config.vocab_size, grammar,
                                            selector=args.grammar_selector, audit_steps=args.greedy_audit_steps)
                if args.grammar_selector == "greedy":
                    if model.generation_config.num_beams != 1:
                        raise ValueError("ranked grammar selector requires the frozen single-beam greedy contract")
                kwargs["logits_processor"] = [processor]
            with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
                generated = model.generate(**inputs, **kwargs)
            new_ids = generated[0][inputs.input_ids.shape[1]:]
            selector_evidence = None
            if processor is not None and args.grammar_selector == "greedy":
                processor.validate_generated(new_ids.tolist())
                selector_evidence = dict(method="ranked_greedy_same_grammar", full_mask_audits=processor.audit_count,
                                         candidates_checked=processor.candidates_checked,
                                         actual_generated_ids_match=True)
            text = tokenizer.decode(new_ids, skip_special_tokens=True)
            record = dict(**metadata, base_prompt_sha256=sha(prompt), raw_reply=text,
                          actual_prompt_token_count=inputs.input_ids.shape[1],
                          actual_prompt_tokens_match_frozen=True,
                          raw_reply_sha256=sha(text), output_token_count=len(new_ids),
                          grammar_enforced=(arm == "grammar_enforced"),
                          selector_evidence=selector_evidence)
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
                   grammar_selector=args.grammar_selector,
                   ranked_cuda_control_passed=args.grammar_selector == "greedy",
                   xgrammar_version=xgrammar_version, xgrammar_site=str(args.xgrammar_site),
                   records=records, producer="direct_checkpoint_generation",
                   gate_claim=False)
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(dict(kind=receipt["kind"], records=len(records),
                          restored_tensors_exact=True, grammar_compiled=True,
                          gate_claim=False), sort_keys=True))


if __name__ == "__main__":
    main()
