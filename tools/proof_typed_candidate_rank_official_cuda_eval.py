#!/usr/bin/env python3
"""Score the answer-free official-119 packet with a trained agenda head."""
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

from tools import proof_typed_candidate_rank_official as official
from tools.proof_cuda_train import file_sha, load_policy, model_files, restore_policy
from tools.proof_typed_candidate_rank_cuda_train import CandidateHead, candidate_features, prompt_hidden


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def evaluate(args) -> dict:
    import torch
    import transformers

    packet = official.load_packet(args.packet, official.sha(args.packet.read_bytes()))
    if file_sha(args.parent) != args.parent_sha256:
        raise ValueError("parent checkpoint binding changed")
    if file_sha(args.head) != args.head_sha256:
        raise ValueError("candidate head binding changed")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 is required")
    net = load_policy(args.model, device="cuda")
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    restore_policy(net, saved, model_files(args.model))
    net.eval().requires_grad_(False)
    head_saved = torch.load(args.head, map_location="cpu", weights_only=False)
    head = CandidateHead(torch, int(head_saved["hidden_size"]), int(head_saved["feature_size"])).to("cuda")
    head.load_state_dict(head_saved["state_dict"])
    hidden_size = int(head_saved["hidden_size"])
    rankings = {}
    prompt_tokens = {}
    started = time.monotonic()
    with torch.inference_mode():
        for row in packet["rows"]:
            hidden, tokens = prompt_hidden(net, tokenizer, row["prompt"], torch)
            prompt_tokens[row["id"]] = tokens
            features = candidate_features(row, torch, "cuda")
            scores = [float(value.detach().cpu()) for value in head.score(hidden, features)]
            order = sorted(range(len(scores)), key=lambda index: (scores[index], -index), reverse=True)
            rankings[row["id"]] = [{
                "candidate_index": index, "candidate": row["candidate_proposals"][index],
                "mean_logp": scores[index], "agenda_score": scores[index],
            } for index in order]
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    # The existing official scorer binds its config to the immutable 119-task
    # packet, while this evaluator consumes the derived typed packet. Keep
    # both hashes explicit so a transfer cannot silently score a different
    # population.
    config = {
        "packet_sha256": official.OFFICIAL_PACKET_SHA256,
        "typed_packet_sha256": official.sha(args.packet.read_bytes()),
        "source_manifest_sha256": official.SOURCE_MANIFEST_SHA256,
        "checkpoint_sha256": args.parent_sha256, "head_sha256": args.head_sha256,
        "model_files": model_files(args.model), "algorithm": "prompt-plus-candidate typed-agenda ranker",
    }
    (args.output / "config.json").write_text(json.dumps(config, indent=2) + "\n")
    summary = {
        "kind": "answer_free_typed_candidate_rank_official_eval",
        "packet_sha256": config["packet_sha256"],
        "typed_packet_sha256": config["typed_packet_sha256"], "denominator": 119,
        "ranked_tasks": len(rankings), "candidate_count": sum(map(len, rankings.values())),
        "hidden_size": hidden_size, "prompt_tokens": prompt_tokens,
        "reference_fragment_used": False, "verifier_feedback_used": False,
        "repair_used": False, "reward_used": False, "training_executed": False,
        "parameter_updates": 0, "tlaps_executed": False,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--head", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--parent-sha256", required=True)
    parser.add_argument("--head-sha256", required=True)
    args = parser.parse_args()
    print(json.dumps(evaluate(args), indent=2), flush=True)


if __name__ == "__main__":
    main()
