"""Verifier-constrained protected decode for the continuation LoRA child.

This decoder restores the exact parent final layer, injects the exact
continuation adapter, preserves the accepted prefix, and regenerates only a
bounded suffix under the audited grammar/rollback selector.  It is inference
only: protected rows are never used for training or reference conditioning,
and every result remains subject to independent pinned-SANY scoring.
"""

import argparse
import hashlib
import importlib.metadata
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import protected_layout_aware_repair as repair

from tools import proof_cuda_train as helpers
from tools import protected_checkpoint_preflight as preflight


def load_continuation_module():
    path = ROOT / "tools" / "proof_fullmodule_continuation_sft_train.py"
    spec = importlib.util.spec_from_file_location("continuation_sft_train", path)
    if spec is None or spec.loader is None:
        raise ImportError(f"continuation trainer unavailable: {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


continuation = load_continuation_module()


PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
PARENT_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f244dcf8511"
CHECKPOINT_SHA = "e8a1395685c5c5c4d9311361fcea1e354d3decb4cf46b94cffab8831e936e69a"
ROWS = (47, 107)


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def write_new(path, value):
    with Path(path).open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")


def exact_inputs(args):
    expected = ((args.packet, PACKET_SHA, "packet"),
                (args.parent_checkpoint, PARENT_SHA, "parent checkpoint"),
                (args.checkpoint, CHECKPOINT_SHA, "adapter checkpoint"))
    for path, wanted, label in expected:
        if file_sha(path) != wanted:
            raise ValueError(f"frozen {label} hash mismatch")
    if args.output.exists():
        raise ValueError("append-only output already exists")


def preflight_only(args, tokenizer, xgrammar, compiled, vocab_size):
    packet = json.loads(args.packet.read_text())
    selected = preflight.protected_rows(packet)
    prompt_evidence = preflight.verify_prompt_tokens(tokenizer, selected)
    references = repair.protected_references(args, tokenizer, xgrammar, compiled)
    controls = dict(
        ranked=repair.synthetic_ranked_control(xgrammar),
        rollback=repair.synthetic_bounded_backtrack_control(xgrammar),
        failure_trace=repair.synthetic_failure_trace_control(),
        comment_free=repair.synthetic_comment_free_control(
            {row: selected[row][0]["response"] for row in ROWS}),
        lexical=repair.synthetic_lexical_control(),
    )
    result = dict(
        schema=1,
        kind="fullmodule_continuation_grammar_decode_cpu_preflight_v1",
        complete=True,
        packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA,
        adapter_checkpoint_sha256=CHECKPOINT_SHA,
        corpus_sha256=repair.CORPUS_SHA,
        grammar_sha256=repair.GRAMMAR_SHA,
        rows=list(ROWS),
        protected_prompt_tokens=prompt_evidence,
        protected_references=references,
        xgrammar_version=importlib.metadata.version("xgrammar"),
        vocabulary_size=vocab_size,
        synthetic_controls=controls,
        model_weights_loaded=False,
        cuda_touched=False,
        training=False,
        reference_conditioning=False,
        gate_claim=False,
        model_improvement_claim=False,
        proof_claim=False,
    )
    write_new(args.output, result)
    print(json.dumps(result, sort_keys=True))


def run(args):
    exact_inputs(args)
    # The shared repair helper is pinned to the old checkpoint by default;
    # replace only that identity for this append-only adapter stage.
    repair.CHILD_SHA = CHECKPOINT_SHA
    tokenizer = repair.load_tokenizer(args)
    xgrammar, compiled, vocab_size = repair.compile_grammar(args, tokenizer)
    if args.preflight_only:
        preflight_only(args, tokenizer, xgrammar, compiled, vocab_size)
        return

    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    packet = json.loads(args.packet.read_text())
    selected = preflight.protected_rows(packet)
    prompt_evidence = preflight.verify_prompt_tokens(tokenizer, selected)
    model_files = helpers.model_files(args.model)
    net = helpers.load_policy(args.model)
    parent = torch.load(args.parent_checkpoint, map_location="cpu", weights_only=False)
    helpers.restore_policy(net, parent, model_files)
    del parent
    adapter_selected = continuation.inject_adapters(net)
    saved = torch.load(args.checkpoint, map_location="cpu", weights_only=False)
    if saved.get("config", {}).get("parent_sha256") != PARENT_SHA or not saved.get("config", {}).get("adapter_only"):
        raise ValueError("adapter checkpoint provenance mismatch")
    continuation.restore_adapters(adapter_selected, saved.get("adapter_state", {}))
    del saved
    args.output.mkdir(parents=False, exist_ok=False)
    records = []
    for row in ROWS:
        source, encoding = selected[row]
        prompt_inputs, _ = repair.frozen_inputs(tokenizer, source, encoding)
        with torch.inference_mode(), torch.autocast(device_type="cuda", dtype=torch.bfloat16):
            baseline = net.generate(**prompt_inputs.to("cuda"), max_new_tokens=args.max_new_tokens,
                                    do_sample=False, pad_token_id=tokenizer.eos_token_id)
        repaired = repair.run_repair(
            net, tokenizer, xgrammar, compiled, prompt_inputs.to("cuda"), baseline[0].tolist(),
            repair_max_new_tokens=args.repair_max_new_tokens,
            selector_audit_steps=args.selector_audit_steps,
            pad_id=tokenizer.eos_token_id, backtrack_windows=args.backtrack_windows)
        baseline_reply = tokenizer.decode(
            baseline[0].tolist()[prompt_inputs["input_ids"].shape[1]:], skip_special_tokens=True)
        repaired_reply = tokenizer.decode(repaired["output"], skip_special_tokens=True)
        record = dict(
            row=row,
            prompt_tokens=int(prompt_inputs["input_ids"].shape[1]),
            prompt_tokens_match_frozen=True,
            baseline_reply=baseline_reply,
            baseline_reply_sha256=hashlib.sha256(baseline_reply.encode()).hexdigest(),
            repaired_reply=repaired_reply,
            repaired_reply_sha256=hashlib.sha256(repaired_reply.encode()).hexdigest(),
            baseline_response_tokens=repaired["baseline_response_tokens"],
            accepted_prefix_tokens=len(repaired["prefix"]),
            first_rejected_response_token=repaired["rejected_at"],
            repaired_response_tokens=len(repaired["output"]),
            repair_tokens=len(repaired["repaired"]),
            grammar_ended=repaired["grammar_ended"],
            backtrack_attempts=repaired["backtrack_attempts"],
            backtrack_windows=list(args.backtrack_windows),
            protected_reference_conditioning=False,
            training=False,
            supplied_reference_credit=False,
            gate_claim=False,
            model_improvement_claim=False,
        )
        write_new(args.output / f"row-{row}.json", record)
        records.append(record)
        print(json.dumps(dict(event="row", row=row,
                              accepted_prefix_tokens=record["accepted_prefix_tokens"],
                              repair_tokens=record["repair_tokens"],
                              grammar_ended=record["grammar_ended"])), flush=True)
    write_new(args.output / "receipt.json", dict(
        schema=1, kind="fullmodule_continuation_grammar_decode_v1", complete=True,
        packet_sha256=PACKET_SHA, parent_checkpoint_sha256=PARENT_SHA,
        adapter_checkpoint_sha256=CHECKPOINT_SHA, model_files=model_files,
        protected_prompt_tokens=prompt_evidence, rows=list(ROWS), records=records,
        grammar_sha256=repair.GRAMMAR_SHA, corpus_sha256=repair.CORPUS_SHA,
        xgrammar_version=importlib.metadata.version("xgrammar"),
        restored_parent_exact=True, restored_adapter_exact=True,
        prefix_preserving=True, reference_conditioning=False, training=False,
        gate_claim=False, model_improvement_claim=False, proof_claim=False,
        tlc_claim=False, nonvacuity_claim=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--grammar", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--parent-checkpoint", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--xgrammar-site", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--preflight-only", action="store_true")
    parser.add_argument("--max-new-tokens", type=int, default=2048)
    parser.add_argument("--repair-max-new-tokens", type=int, default=512)
    parser.add_argument("--selector-audit-steps", type=int, default=4)
    parser.add_argument("--backtrack-windows", type=int, nargs="+", default=[64, 128, 256, 512])
    run(parser.parse_args())
