#!/usr/bin/env python3
"""Exact-parent conditional ranking over the frozen official action lattice.

This worker is inference-only.  It does not read reference proofs, invoke
TLAPS, train, repair, consume verifier feedback, or compute a reward.
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

BUDGET = {
    "rows": 119,
    "max_candidates_per_row": 4,
    "score_seconds": 720,
    "parameter_updates": 0,
    "training_executed": False,
    "reference_fragment_used": False,
    "tlaps_executed": False,
    "resources": "one Polaris GPU, 64 CPUs, 00:15:00",
}
PROFILE = "frozen bf16 base with float32 final transformer layer; bf16 autocast"
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def reject_keys(value, path="packet"):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def validate_packet(packet: dict) -> list[dict]:
    reject_keys(packet)
    expected = {
        "packet_kind": "answer_free_official_symbolic_candidate_ranking",
        "split": "official_test", "denominator": 119,
        "protected_evaluation": True,
        "reference_fragment_used": False,
        "reference_fragment_exported": False,
        "proof_bodies_exported": False,
        "successful_candidates_exported": False,
        "generated_feedback": False,
        "training_executed": False,
        "parameter_updates": 0,
        "tlaps_executed": False,
        "proof_or_quality_claim": False,
    }
    if any(packet.get(key) != value for key, value in expected.items()):
        raise ValueError("official packet contract mismatch")
    rows = packet.get("rows", [])
    if len(rows) != 119 or len({row.get("id") for row in rows}) != 119:
        raise ValueError("exact official denominator required")
    required = {"id", "split", "theorem_name", "prompt", "prompt_sha256",
                 "candidate_proposals", "candidate_proposals_sha256"}
    for row in rows:
        if set(row) != required or row["split"] != "official_test":
            raise ValueError("unexpected official packet fields")
        candidates = row["candidate_proposals"]
        if not 1 <= len(candidates) <= 4 or len(set(candidates)) != len(candidates):
            raise ValueError("official candidate shortlist outside bound")
        if (not row["prompt"] or sha(row["prompt"].encode()) != row["prompt_sha256"] or
                digest(candidates) != row["candidate_proposals_sha256"]):
            raise ValueError("official packet hash mismatch")
        if any(candidate != "OBVIOUS" and not candidate.startswith("BY ")
               for candidate in candidates):
            raise ValueError("non-TLAPS candidate")
    return rows


def encode_candidate(tokenizer, prompt_text, candidate, max_tokens=8192):
    messages = [dict(role="user", content=prompt_text)]
    prompt = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
    full = tokenizer.apply_chat_template(
        messages + [dict(role="assistant", content=candidate)],
        tokenize=False, add_generation_prompt=False)
    prefix = tokenizer(prompt, add_special_tokens=False, truncation=False)["input_ids"]
    ids = tokenizer(full, add_special_tokens=False, truncation=False)["input_ids"]
    if not prefix or ids[:len(prefix)] != prefix:
        raise ValueError("chat template changed prompt boundary")
    response = ids[len(prefix):]
    eos = tokenizer.eos_token_id
    if not response or not isinstance(eos, int) or eos not in response:
        raise ValueError("candidate has no terminal EOS")
    ids = ids[:len(prefix) + response.index(eos) + 1]
    if len(ids) > max_tokens:
        raise OverflowError("context exceeds frozen 8192-token budget")
    return dict(input_ids=ids, labels=[-100] * len(prefix) + ids[len(prefix):],
                prompt_tokens=len(prefix), response_tokens=len(ids) - len(prefix),
                rendered_prompt=prompt)


def response_logps(logits, labels):
    import torch
    labels = torch.as_tensor(labels, device=logits.device)
    mask = labels[1:] != -100
    if logits.ndim != 2 or labels.ndim != 1 or logits.shape[0] != len(labels) or not mask.any():
        raise ValueError("invalid response alignment")
    selected = logits[:-1][mask].float().log_softmax(-1)
    values = selected.gather(1, labels[1:][mask, None]).squeeze(1)
    if not torch.isfinite(values).all():
        raise ValueError("nonfinite candidate score")
    return dict(sum_logp=float(values.sum()), mean_logp=float(values.mean()),
                response_tokens=int(mask.sum()), token_logps=values.tolist())


def worker(packet_path: Path, model_path: Path, checkpoint_path: Path, output: Path,
           packet_sha256: str | None = None):
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, model_files, restore_policy

    packet_bytes = packet_path.read_bytes()
    if packet_sha256 and sha(packet_bytes) != packet_sha256:
        raise ValueError("packet changed after freeze")
    rows = validate_packet(json.loads(packet_bytes))
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 support required")
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
        raise ValueError("exact parent restore failed")
    del saved
    dump(output / "config.json", {
        "schema_version": 1,
        "packet_sha256": sha(packet_bytes),
        "checkpoint_sha256": sha(checkpoint_path.read_bytes()),
        "model_files": files,
        "profile": PROFILE,
        "budget": BUDGET,
        "restore_exact": True,
        "parameter_updates": 0,
        "training_executed": False,
        "reference_fragment_used": False,
        "tlaps_executed": False,
        "proof_or_quality_claim": False,
        "torch_version": torch.__version__,
        "transformers_version": transformers.__version__,
    })
    started = time.monotonic()
    scored = {}
    with (output / "scores.jsonl").open("x") as stream:
        for row in rows:
            task_scores = []
            task_status = "ready"
            for index, candidate in enumerate(row["candidate_proposals"]):
                if time.monotonic() - started >= BUDGET["score_seconds"]:
                    task_status = "time_budget"
                    break
                try:
                    encoding = encode_candidate(tokenizer, row["prompt"], candidate)
                except OverflowError:
                    task_status = "context_overflow"
                    break
                with torch.inference_mode(), torch.autocast("cuda", dtype=torch.bfloat16):
                    ids = torch.tensor([encoding["input_ids"]], device="cuda")
                    logits = net(input_ids=ids, use_cache=False).logits[0]
                    score = response_logps(logits, encoding["labels"])
                record = dict(task=row["id"], candidate_index=index,
                              candidate=candidate, **score)
                task_scores.append(record)
                stream.write(json.dumps(record) + "\n")
                stream.flush()
            if task_status == "ready" and len(task_scores) == len(row["candidate_proposals"]):
                scored[row["id"]] = sorted(
                    task_scores, key=lambda item: (-item["mean_logp"], item["candidate_index"]))
            elif task_status != "ready":
                stream.write(json.dumps(dict(task=row["id"], status=task_status)) + "\n")
                stream.flush()
    elapsed = time.monotonic() - started
    dump(output / "rankings.json", scored)
    runtime = {
        "gpu": torch.cuda.get_device_name(),
        "cuda_peak_allocated_bytes": torch.cuda.max_memory_allocated(),
        "cuda_peak_reserved_bytes": torch.cuda.max_memory_reserved(),
        "parameter_updates": 0,
        "elapsed_seconds": elapsed,
    }
    dump(output / "runtime.json", runtime)
    summary = {
        "requested_tasks": 119,
        "fully_scored_tasks": len(scored),
        "scored_candidates": sum(len(value) for value in scored.values()),
        "parameter_updates": 0,
        "training_executed": False,
        "reference_fragment_used": False,
        "tlaps_executed": False,
        "proof_or_quality_claim": False,
        "method": "exact-parent conditional mean response logp over answer-free official symbolic proposals",
        **runtime,
    }
    dump(output / "summary.json", summary)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--packet-sha256")
    args = parser.parse_args()
    os.environ.update(HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1",
                      TOKENIZERS_PARALLELISM="false")
    args.output.mkdir(parents=True, exist_ok=False)
    print(json.dumps(worker(args.packet, args.model, args.checkpoint, args.output,
                            args.packet_sha256)), flush=True)


if __name__ == "__main__":
    main()
