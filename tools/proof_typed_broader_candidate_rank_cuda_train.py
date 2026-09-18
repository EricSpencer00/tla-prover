#!/usr/bin/env python3
"""Train a typed-agenda rank head on the admitted broader32 TRAIN packet."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_typed_broader_candidate_rank as packet_tools
from tools.proof_cuda_train import file_sha, load_policy, model_files, restore_policy
from tools.proof_typed_candidate_rank_cuda_train import CandidateHead, candidate_features, prompt_hidden

PROFILE = "frozen bf16 base with float32 candidate agenda rank head over broader32 TRAIN"


def select(head, hidden, row, torch, feature_cache):
    scores = [float(value.detach().cpu())
              for value in head.score(hidden, feature_cache[row["id"]])]
    index = max(range(len(scores)), key=lambda i: (scores[i], -i))
    return {
        "id": row["id"], "valid": True, "candidate_index": index,
        "candidate": row["candidate_proposals"][index],
        "agenda_slots": row["candidate_agenda_slots"][index],
        "agenda_score": scores[index], "scores": scores,
    }


def worker(args) -> dict:
    import torch
    import transformers

    packet = packet_tools.load_packet(args.packet, args.expected_packet_sha256)
    if file_sha(args.parent) != packet_tools.PARENT_SHA256:
        raise ValueError("exact approved parent checkpoint required")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 is required")
    if not 1 <= args.updates <= 64 or not 0 < args.lr <= 0.1:
        raise ValueError("bounded broader candidate-rank budget required")
    if args.output.exists():
        raise ValueError("output must be new")
    torch.manual_seed(args.seed)
    net = load_policy(args.model, device="cuda")
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    restore_policy(net, saved, model_files(args.model))
    net.eval().requires_grad_(False)

    all_rows = packet["train_rows"] + packet["development_rows"]
    hidden, prompt_tokens = {}, {}
    for row in all_rows:
        hidden[row["id"]], prompt_tokens[row["id"]] = prompt_hidden(net, tokenizer, row["prompt"], torch)
    feature_cache = {row["id"]: candidate_features(row, torch, "cuda") for row in all_rows}
    hidden_size = int(next(iter(hidden.values())).shape[0])
    feature_size = len(packet_tools.agenda.SLOTS) + 4
    head = CandidateHead(torch, hidden_size, feature_size).to("cuda")
    initial_state = copy.deepcopy(head.state_dict())
    optimizer = torch.optim.AdamW(head.parameters(), lr=args.lr, weight_decay=0.01)
    losses = []
    started = time.monotonic()
    for _ in range(args.updates):
        losses_now = []
        for row in packet["train_rows"]:
            logits = head.score(hidden[row["id"]], feature_cache[row["id"]])
            target = torch.tensor([row["teacher_candidate_index"]], dtype=torch.long, device="cuda")
            losses_now.append(torch.nn.functional.cross_entropy(logits.unsqueeze(0), target))
        loss = sum(losses_now) / len(losses_now)
        if not torch.isfinite(loss):
            raise ValueError("nonfinite broader candidate-rank loss")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(list(head.parameters()), 1.0, error_if_nonfinite=True)
        optimizer.step()
        losses.append(float(loss.detach().cpu()))

    trained_state = copy.deepcopy(head.state_dict())
    dev_rows = packet["development_rows"]
    head.load_state_dict(initial_state)
    with torch.inference_mode():
        parent = [select(head, hidden[row["id"]], row, torch, feature_cache) for row in dev_rows]
    base = [{
        "id": row["id"], "valid": True, "candidate_index": 0,
        "candidate": row["candidate_proposals"][0],
        "agenda_slots": row["candidate_agenda_slots"][0], "agenda_score": 0.0, "scores": [],
    } for row in dev_rows]
    head.load_state_dict(trained_state)
    with torch.inference_mode():
        child = [select(head, hidden[row["id"]], row, torch, feature_cache) for row in dev_rows]

    args.output.mkdir(parents=True, exist_ok=False)
    head_path = args.output / "candidate_head.pt"
    torch.save({"state_dict": trained_state, "slots": list(packet_tools.agenda.SLOTS),
                "hidden_size": hidden_size, "feature_size": feature_size,
                "updates": args.updates}, head_path)
    for name, values in (("base_generations.json", base), ("parent_generations.json", parent),
                         ("child_generations.json", child)):
        (args.output / name).write_text(json.dumps(values, indent=2) + "\n")
    (args.output / "steps.jsonl").write_text(
        "".join(json.dumps({"update": index + 1, "loss": value}) + "\n"
                for index, value in enumerate(losses)))
    summary = {
        "algorithm": "prompt-plus-candidate typed-agenda ranker broader32",
        "packet_sha256": packet_tools.sha(args.packet.read_bytes()),
        "parent_sha256": file_sha(args.parent), "source_manifest_sha256": packet["source_manifest_sha256"],
        "train_rows": 32, "development_rows": 4,
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in dev_rows),
        "requested_updates": args.updates, "updates": len(losses),
        "hidden_size": hidden_size, "feature_size": feature_size,
        "head_sha256": packet_tools.sha(head_path.read_bytes()),
        "base_generations": 4, "parent_generations": 4, "child_generations": 4,
        "prompt_tokens": prompt_tokens,
        "development_targets_exported": False, "candidate_index_labels_used": False,
        "train_teacher_agenda_labels_used": True, "verifier_feedback_used": False,
        "repair_used": False, "reward_used": False, "strict_verifier_runs": 0,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
        "loss_first_last": [losses[0], losses[-1]],
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "config.json").write_text(json.dumps({
        "seed": args.seed, "lr": args.lr, "updates": args.updates,
        "model_files": model_files(args.model), "parent_sha256": file_sha(args.parent),
        "packet_sha256": packet_tools.sha(args.packet.read_bytes()), "max_prompt_tokens": 8192,
        "dtype_profile": PROFILE,
    }, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--updates", type=int, default=32)
    parser.add_argument("--lr", type=float, default=0.01)
    parser.add_argument("--seed", type=int, default=20260918)
    args = parser.parse_args()
    print(json.dumps(worker(args), indent=2), flush=True)


if __name__ == "__main__":
    main()
