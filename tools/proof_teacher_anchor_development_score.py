#!/usr/bin/env python3
"""Score an unseen, target-free DEVELOPMENT candidate packet parent vs child.

The packet contains symbolic candidates and prompts only.  No DEVELOPMENT
reference fragment is serialized or forwarded.  This is a ranking diagnostic;
it does not assign verifier rewards or make a proof/gate claim.
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

PACKET_SHA256 = "d43ca8ab8beb31dfd1b36b3feeff00346175115b951aba9545334ecf71ae6537"
MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
CHILD_SHA256 = "672ada258500f3b5aba704ef7150cc3662155ef272b0a3e87e63312ff323e4ca"
DEV_IDS = {"crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof", "crdt-sum-zero-proof"}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def validate_packet(packet: object) -> list[dict]:
    if not isinstance(packet, list) or len(packet) != 4:
        raise ValueError("exact four DEVELOPMENT rows required")
    ids = {row.get("id") for row in packet if isinstance(row, dict)}
    if ids != DEV_IDS:
        raise ValueError("unexpected DEVELOPMENT population")
    for row in packet:
        if not isinstance(row.get("prompt"), str) or "<PROOF_HOLE>" not in row["prompt"]:
            raise ValueError("development prompt must expose proof hole")
        candidates = row.get("candidates")
        if not isinstance(candidates, list) or len(candidates) != 29:
            raise ValueError("fixed 29-candidate DEVELOPMENT denominator required")
        if any(not isinstance(candidate, str) or not candidate.strip() for candidate in candidates):
            raise ValueError("nonempty symbolic candidates required")
        context = row.get("context", {})
        if context.get("reference_fragment_used") is not False:
            raise ValueError("DEVELOPMENT packet reference-use attestation failed")
        if any(key in row for key in ("reference_fragment", "response", "answer", "proof_body",
                                      "reward", "feedback", "repair")):
            raise ValueError("DEVELOPMENT target or verifier signal leaked into packet")
    serialized = json.dumps(packet, ensure_ascii=False)
    if '"reference_fragment"' in serialized:
        raise ValueError("reference field leaked into serialized DEVELOPMENT packet")
    return packet


def rank(values: list[float]) -> list[int]:
    return sorted(range(len(values)), key=lambda i: (-values[i], i))


def worker(args) -> dict:
    from tools.proof_candidate_rank import encode_candidate
    from tools.proof_teacher_anchor_contrastive_score import restore_trainable, score_policy
    import torch
    import transformers

    packet_raw = args.packet.read_bytes()
    if sha(packet_raw) != args.expected_packet_sha256:
        raise ValueError("DEVELOPMENT packet hash mismatch")
    if sha(args.manifest.read_bytes()) != args.expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    if sha(args.parent.read_bytes()) != args.expected_parent_sha256:
        raise ValueError("parent hash mismatch")
    if sha(args.child.read_bytes()) != args.expected_child_sha256:
        raise ValueError("child hash mismatch")
    packet = validate_packet(json.loads(packet_raw))
    if args.output.exists():
        raise ValueError("output already exists")
    args.output.mkdir(parents=True)
    (args.output / "development_packet.json").write_bytes(packet_raw)
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
            parent_order, child_order = rank(parent_scores), rank(child_scores)
            result = {
                "task": row["id"],
                "candidate_count": 29,
                "parent_mean_logps": parent_scores,
                "child_mean_logps": child_scores,
                "parent_order": parent_order,
                "child_order": child_order,
                "parent_top1": parent_order[0],
                "child_top1": child_order[0],
                "top1_changed": parent_order[0] != child_order[0],
                "parent_top4": parent_order[:4],
                "child_top4": child_order[:4],
            }
            rows.append(result)
            stream.write(json.dumps(result) + "\n")
            stream.flush()
    summary = {
        "schema": 1,
        "packet_sha256": sha(packet_raw),
        "manifest_sha256": sha(args.manifest.read_bytes()),
        "parent_sha256": sha(args.parent.read_bytes()),
        "child_sha256": sha(args.child.read_bytes()),
        "development_tasks": len(rows),
        "candidate_denominator": sum(row["candidate_count"] for row in rows),
        "top1_changed": sum(row["top1_changed"] for row in rows),
        "development_reference_bytes_forwarded": False,
        "verifier_rewards_used": False,
        "optimizer_updates": 0,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
        "elapsed_seconds": time.monotonic() - started,
        "scope": "target-free DEVELOPMENT ranking diagnostic only; strict TLAPS scoring is separate",
    }
    dump(args.output / "summary.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--model-path", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--child", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--device", choices=("cpu", "cuda"), default="cuda")
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    parser.add_argument("--expected-manifest-sha256", default=MANIFEST_SHA256)
    parser.add_argument("--expected-parent-sha256", default=PARENT_SHA256)
    parser.add_argument("--expected-child-sha256", default=CHILD_SHA256)
    args = parser.parse_args()
    if not 128 <= args.max_tokens <= 8192:
        parser.error("invalid max-token budget")
    worker(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
