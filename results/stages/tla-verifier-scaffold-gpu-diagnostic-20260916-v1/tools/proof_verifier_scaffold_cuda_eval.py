#!/usr/bin/env python3
"""Bounded GPU generation for the answer-free verifier scaffold.

This diagnostic loads the exact frozen Llama3.1-8B parent and generates one
short proof action for the four development prompts in an answer-free packet.
It performs no training, optimizer step, repair, reward calculation, or target
conditioning.  The generated rows are raw inference evidence only; local
independent SANY scoring must happen after retrieval.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


PROFILE = "frozen bf16 base with float32 final transformer layer; bf16 autocast"
BUDGET = {
    "max_new_tokens": 256,
    "generation_seconds_per_row": 90,
    "rows": 4,
    "parameter_updates": 0,
    "do_sample": False,
    "num_beams": 1,
    "walltime": "00:15:00",
}
FORBIDDEN_FIELDS = {
    "reference_fragment", "response", "answer", "candidate", "candidates",
    "proof_body", "proof_module", "by_facts", "successful_candidate",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def validate_packet(data: dict) -> list[dict]:
    if (data.get("packet_kind") != "answer_free_verifier_conditioned_retrieval"
            or data.get("split") != "development" or data.get("denominator") != 4
            or data.get("reference_fragment_used") is not False
            or data.get("reference_fragment_exported") is not False
            or data.get("proof_bodies_exported") is not False
            or data.get("successful_candidates_exported") is not False
            or data.get("model_executed") is not False
            or data.get("training_executed") is not False
            or data.get("parameter_updates") != 0
            or data.get("proof_or_quality_claim") is not False):
        raise ValueError("only the frozen four-row answer-free development packet is accepted")
    rows = data.get("rows", [])
    if len(rows) != 4 or len({row.get("id") for row in rows}) != 4:
        raise ValueError("exact four development rows required")
    for row in rows:
        if FORBIDDEN_FIELDS & set(row):
            raise ValueError("answer-bearing packet field")
        if (row.get("split") != "development" or not row.get("prompt")
                or row.get("prompt_sha256") != sha(row["prompt"].encode())):
            raise ValueError("prompt provenance mismatch")
        if not isinstance(row.get("retrieval_hits"), list):
            raise ValueError("retrieval hit list required")
    return rows


def trim_output(ids: list[int], eos_ids: set[int]) -> list[int]:
    for index, token in enumerate(ids):
        if token in eos_ids:
            return ids[:index + 1]
    return ids


def encode_prompt(tokenizer, row: dict) -> dict:
    rendered = tokenizer.apply_chat_template(
        [dict(role="user", content=row["prompt"])],
        tokenize=False, add_generation_prompt=True)
    ids = tokenizer(rendered, add_special_tokens=False, truncation=False)["input_ids"]
    if not ids or any(type(token) is not int or token < 0 for token in ids):
        raise ValueError("invalid prompt token IDs")
    return {
        "id": row["id"],
        "prompt_sha256": row["prompt_sha256"],
        "rendered_prompt": rendered,
        "rendered_prompt_sha256": sha(rendered.encode()),
        "input_token_ids": ids,
        "input_token_ids_sha256": digest(ids),
        "input_tokens": len(ids),
        "status": "context_overflow" if len(ids) + BUDGET["max_new_tokens"] > 8192 else "ready",
    }


def model_files(model_path: Path) -> dict[str, str]:
    from tools.proof_cuda_train import model_files as get_model_files
    return get_model_files(model_path)


def worker(packet_path: Path, model_path: Path, checkpoint_path: Path, output: Path,
           packet_sha256: str | None = None) -> dict:
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, restore_policy

    packet_bytes = packet_path.read_bytes()
    if packet_sha256 and sha(packet_bytes) != packet_sha256:
        raise ValueError("packet changed after stage freeze")
    rows = validate_packet(json.loads(packet_bytes))
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 support required; no CPU fallback")
    torch.set_num_threads(4)
    torch.manual_seed(20260916)
    torch.backends.cuda.matmul.allow_tf32 = False
    torch.cuda.reset_peak_memory_stats()
    files = model_files(model_path)
    net = load_policy(model_path, device="cuda")
    tokenizer = transformers.AutoTokenizer.from_pretrained(model_path, local_files_only=True)
    saved = torch.load(checkpoint_path, map_location="cpu", weights_only=False)
    selected = restore_policy(net, saved, files)
    if not all(torch.equal(parameter.detach().cpu(), saved["trainable_state"][name])
               for name, parameter in selected.items()):
        raise ValueError("exact parent tensor restore failed")
    del saved
    config = {
        "schema_version": 1,
        "packet_sha256": sha(packet_bytes),
        "checkpoint_sha256": sha(checkpoint_path.read_bytes()),
        "model_files": files,
        "model_files_sha256": digest(files),
        "profile": PROFILE,
        "budget": BUDGET,
        "restore_exact": True,
        "parameter_updates": 0,
        "training_executed": False,
        "reference_fragment_used": False,
        "proof_or_quality_claim": False,
        "torch_version": torch.__version__,
        "transformers_version": transformers.__version__,
    }
    dump(output / "config.json", config)
    tokenizer.padding_side = "left"
    pad_id = tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if not isinstance(pad_id, int):
        raise ValueError("scalar pad token required")
    eos = net.generation_config.eos_token_id
    eos_ids = set(eos if isinstance(eos, list) else [eos])
    generated = []
    started = time.monotonic()
    with (output / "generations.jsonl").open("x") as stream:
        for row in rows:
            encoded = encode_prompt(tokenizer, row)
            if encoded["status"] == "ready":
                input_ids = torch.tensor([encoded["input_token_ids"]], device="cuda")
                attention = torch.ones_like(input_ids)
                with torch.inference_mode(), torch.autocast("cuda", dtype=torch.bfloat16):
                    outputs = net.generate(
                        input_ids=input_ids, attention_mask=attention, do_sample=False,
                        num_beams=1, num_return_sequences=1,
                        max_new_tokens=BUDGET["max_new_tokens"],
                        max_time=BUDGET["generation_seconds_per_row"], pad_token_id=pad_id)
                torch.cuda.synchronize()
                new_ids = trim_output(outputs[0][input_ids.shape[1]:].tolist(), eos_ids)
                raw_reply = tokenizer.decode(new_ids, skip_special_tokens=True,
                                             clean_up_tokenization_spaces=False)
                encoded.update(
                    status="generated", token_ids=new_ids,
                    token_ids_sha256=digest(new_ids), output_tokens=len(new_ids),
                    hit_token_limit=len(new_ids) == BUDGET["max_new_tokens"],
                    raw_reply=raw_reply, raw_reply_sha256=sha(raw_reply.encode()))
            generated.append(encoded)
            stream.write(json.dumps(encoded) + "\n")
            stream.flush()
    runtime = {
        "gpu": torch.cuda.get_device_name(),
        "cuda_peak_allocated_bytes": torch.cuda.max_memory_allocated(),
        "cuda_peak_reserved_bytes": torch.cuda.max_memory_reserved(),
        "parameter_updates": 0,
        "elapsed_seconds": time.monotonic() - started,
    }
    dump(output / "runtime.json", runtime)
    summary = {
        "requested_rows": len(rows),
        "generated_rows": sum(row["status"] == "generated" for row in generated),
        "context_overflow_rows": sum(row["status"] == "context_overflow" for row in generated),
        "parameter_updates": 0,
        "training_executed": False,
        "reference_fragment_used": False,
        "proof_or_quality_claim": False,
        "independent_sany_scoring": "not performed in worker",
    }
    dump(output / "summary.json", {**summary, **runtime})
    return summary


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--packet-sha256")
    args = parser.parse_args(argv)
    os.environ.update(HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1", TOKENIZERS_PARALLELISM="false")
    args.output.mkdir(parents=True, exist_ok=False)
    print(json.dumps(worker(args.packet, args.model, args.checkpoint, args.output, args.packet_sha256)), flush=True)


if __name__ == "__main__":
    main()
