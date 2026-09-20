#!/usr/bin/env python3
"""Independently score the complete frozen TRAIN teacher-anchor denominator.

This audit loads the immutable parent and contrastive child separately and
scores all 17 x 8 frozen candidates.  It performs no training, verifier
rewarding, DEVELOPMENT evaluation, proof checking, or gate accounting.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

PACKET_SHA256 = "d6437a577cdee66efdeacb9b818463853a8d4aacfaf987561532693bccc147a0"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
CHILD_SHA256 = "672ada258500f3b5aba704ef7150cc3662155ef272b0a3e87e63312ff323e4ca"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def restore_trainable(trainable: dict, saved: dict) -> None:
    import torch
    state = saved["trainable_state"]
    if set(state) != set(trainable):
        raise ValueError("checkpoint trainable parameter coverage mismatch")
    for name, parameter in trainable.items():
        if state[name].shape != parameter.shape or state[name].dtype != parameter.dtype:
            raise ValueError(f"checkpoint shape/dtype mismatch: {name}")
    with torch.no_grad():
        for name, parameter in trainable.items():
            parameter.copy_(state[name].to(parameter.device))


def validate_packet(packet: object) -> list[dict]:
    from tools.proof_teacher_anchor_contrastive import validate_packet as validate
    return validate(packet)


def rank(values: list[float]) -> list[int]:
    return sorted(range(len(values)), key=lambda i: (-values[i], i))


def score_policy(net, encoded, device: str) -> list[float]:
    from tools.proof_candidate_rank import response_logps
    import torch
    values = []
    with torch.inference_mode():
        for encoding in encoded:
            ids = torch.tensor([encoding["input_ids"]], device=device)
            logits = net(input_ids=ids, use_cache=False).logits[0]
            values.append(float(response_logps(logits, encoding["labels"])["mean_logp"]))
    return values


def worker(args) -> dict:
    from tools.proof_candidate_rank import encode_candidate
    import torch
    import transformers

    packet_raw = args.packet.read_bytes()
    if sha(packet_raw) != args.expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    if sha(args.parent.read_bytes()) != args.expected_parent_sha256:
        raise ValueError("parent hash mismatch")
    if sha(args.child.read_bytes()) != args.expected_child_sha256:
        raise ValueError("child hash mismatch")
    packet = validate_packet(json.loads(packet_raw))
    if args.output.exists():
        raise ValueError("output already exists")
    args.output.mkdir(parents=True)
    (args.output / "packet.json").write_bytes(packet_raw)

    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model_path, local_files_only=True)
    encoded = [[encode_candidate(tokenizer, row["prompt"], candidate, args.max_tokens)
                for candidate in row["candidates"]] for row in packet]
    dump(args.output / "encodings.json", encoded)
    net = transformers.AutoModelForCausalLM.from_pretrained(
        args.model_path, local_files_only=True, torch_dtype=torch.float32).to(args.device).eval()
    net.requires_grad_(False)
    net.model.layers[-1].requires_grad_(True)
    trainable = {name: parameter for name, parameter in net.named_parameters()
                 if parameter.requires_grad}
    model_files = {path.name: sha(path.read_bytes()) for path in args.model_path.iterdir()
                   if path.is_file() and path.suffix in {".json", ".safetensors"}}
    parent_saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    child_saved = torch.load(args.child, map_location="cpu", weights_only=False)
    if parent_saved["config"]["model_files"] != model_files or child_saved["config"]["model_files"] != model_files:
        raise ValueError("base model identity mismatch")

    started = time.monotonic()
    rows = []
    with (args.output / "rows.jsonl").open("x") as stream:
        for row, candidates in zip(packet, encoded):
            restore_trainable(trainable, parent_saved)
            parent_scores = score_policy(net, candidates, args.device)
            restore_trainable(trainable, child_saved)
            child_scores = score_policy(net, candidates, args.device)
            parent_order = rank(parent_scores)
            child_order = rank(child_scores)
            result = {
                "task": row["id"],
                "candidate_count": len(candidates),
                "teacher_candidate_index": 0,
                "parent_mean_logps": parent_scores,
                "child_mean_logps": child_scores,
                "parent_order": parent_order,
                "child_order": child_order,
                "parent_teacher_rank": parent_order.index(0) + 1,
                "child_teacher_rank": child_order.index(0) + 1,
                "parent_teacher_margin": parent_scores[0] - max(parent_scores[1:]),
                "child_teacher_margin": child_scores[0] - max(child_scores[1:]),
                "child_margin_delta": (child_scores[0] - max(child_scores[1:])) -
                                      (parent_scores[0] - max(parent_scores[1:])),
            }
            rows.append(result)
            stream.write(json.dumps(result) + "\n")
            stream.flush()

    def mean(key):
        return sum(row[key] for row in rows) / len(rows)

    summary = {
        "schema": 1,
        "packet_sha256": sha(packet_raw),
        "parent_sha256": sha(args.parent.read_bytes()),
        "child_sha256": sha(args.child.read_bytes()),
        "train_tasks": len(rows),
        "candidate_denominator": sum(row["candidate_count"] for row in rows),
        "parent_teacher_top1": sum(row["parent_teacher_rank"] == 1 for row in rows),
        "child_teacher_top1": sum(row["child_teacher_rank"] == 1 for row in rows),
        "parent_mean_teacher_margin": mean("parent_teacher_margin"),
        "child_mean_teacher_margin": mean("child_teacher_margin"),
        "mean_margin_delta": mean("child_margin_delta"),
        "parent_mean_teacher_rank": mean("parent_teacher_rank"),
        "child_mean_teacher_rank": mean("child_teacher_rank"),
        "development_rows_scored": 0,
        "verifier_rewards_used": False,
        "optimizer_updates": 0,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
        "elapsed_seconds": time.monotonic() - started,
        "scope": "independent fixed-denominator TRAIN ranking diagnostic only",
    }
    dump(args.output / "summary.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--model-path", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--child", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--device", choices=("cpu", "cuda"), default="cuda")
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    parser.add_argument("--expected-parent-sha256", default=PARENT_SHA256)
    parser.add_argument("--expected-child-sha256", default=CHILD_SHA256)
    args = parser.parse_args()
    if not 128 <= args.max_tokens <= 8192:
        parser.error("invalid max-token budget")
    worker(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
