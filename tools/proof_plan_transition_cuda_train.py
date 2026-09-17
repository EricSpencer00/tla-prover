#!/usr/bin/env python3
"""Fit a multi-slot ordered proof-plan head on one bounded Polaris GPU."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_plan_transition as plan
from tools.proof_cuda_train import file_sha, load_policy, model_files, restore_policy


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def prompt_hidden(net, tokenizer, prompt: str, torch):
    rendered = tokenizer.apply_chat_template(
        [dict(role="user", content=prompt)], tokenize=False, add_generation_prompt=True)
    batch = tokenizer(rendered, return_tensors="pt", add_special_tokens=False)
    batch = {key: value.to("cuda") for key, value in batch.items()}
    with torch.inference_mode(), torch.autocast(device_type="cuda", dtype=torch.bfloat16):
        hidden = net(**batch, use_cache=False, output_hidden_states=True).hidden_states[-1][0, -1].float()
    return hidden.detach().clone(), int(batch["input_ids"].shape[1])


def split_logits(logits, torch):
    out, start = {}, 0
    for slot in plan.SLOTS:
        width = len(plan.VOCAB[slot])
        out[slot] = logits[..., start:start + width]
        start += width
    return out


def choose(row: dict, logits, torch) -> dict:
    pieces = split_logits(logits, torch)
    predicted = {slot: plan.VOCAB[slot][int(torch.argmax(pieces[slot]).item())]
                 for slot in plan.SLOTS}
    selected = plan.select_candidate(row, predicted)
    selected.update({"id": row["id"], "valid": True,
                     "plan_probabilities": {
                         slot: torch.softmax(pieces[slot].float(), dim=0).detach().cpu().tolist()
                         for slot in plan.SLOTS}})
    return selected


def worker(args) -> dict:
    import torch
    import transformers

    packet = plan.load_packet(args.packet, args.expected_packet_sha256)
    if file_sha(args.parent) != plan.PARENT_SHA256:
        raise ValueError("exact approved parent checkpoint required")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("Polaris CUDA bf16 is required")
    if not 1 <= args.updates <= 64 or not 0 < args.lr <= 0.1:
        raise ValueError("bounded ordered-plan budget required")
    if args.output.exists():
        raise ValueError("output must be new")
    torch.manual_seed(args.seed)
    net = load_policy(args.model, device="cuda")
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    restore_policy(net, saved, model_files(args.model))
    net.eval().requires_grad_(False)
    all_rows = packet["train_rows"] + packet["development_rows"]
    representations, prompt_tokens = {}, {}
    for row in all_rows:
        representations[row["id"]], prompt_tokens[row["id"]] = prompt_hidden(net, tokenizer, row["prompt"], torch)
    hidden_size = int(next(iter(representations.values())).shape[0])
    output_size = sum(len(plan.VOCAB[slot]) for slot in plan.SLOTS)
    head = torch.nn.Linear(hidden_size, output_size, device="cuda", dtype=torch.float32)
    initial_state = {key: value.detach().cpu().clone() for key, value in head.state_dict().items()}
    optimizer = torch.optim.AdamW(head.parameters(), lr=args.lr, weight_decay=0.01)
    train_matrix = torch.stack([representations[row["id"]] for row in packet["train_rows"]])
    targets = {slot: torch.tensor([plan.VOCAB[slot].index(row["plan"][slot]) for row in packet["train_rows"]], device="cuda")
               for slot in plan.SLOTS}
    losses = []
    started = time.monotonic()
    for update in range(args.updates):
        pieces = split_logits(head(train_matrix).float(), torch)
        loss = sum(torch.nn.functional.cross_entropy(pieces[slot], targets[slot]) for slot in plan.SLOTS)
        if not torch.isfinite(loss):
            raise ValueError("nonfinite ordered-plan loss")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(head.parameters(), 1.0, error_if_nonfinite=True)
        optimizer.step()
        losses.append(float(loss.detach().cpu()))
    trained_state = {key: value.detach().cpu().clone() for key, value in head.state_dict().items()}
    dev_rows = packet["development_rows"]
    with torch.inference_mode():
        base = []
        parent = []
        head.load_state_dict(initial_state)
        for row in dev_rows:
            base.append({"id": row["id"], "valid": True, "candidate_index": 0,
                         "candidate": row["candidate_proposals"][0], "strategy": "renderer_first",
                         "plan": None, "plan_probabilities": []})
            parent.append(choose(row, head(representations[row["id"]]), torch))
        head.load_state_dict(trained_state)
    with torch.inference_mode():
        child = [choose(row, head(representations[row["id"]]), torch) for row in dev_rows]
    args.output.mkdir(parents=True, exist_ok=False)
    head_path = args.output / "plan_head.pt"
    torch.save({"state_dict": trained_state, "slots": list(plan.SLOTS), "vocab": plan.VOCAB,
                "hidden_size": hidden_size, "updates": args.updates}, head_path)
    for name, values in (("base_generations.json", base), ("parent_generations.json", parent),
                         ("child_generations.json", child)):
        (args.output / name).write_text(json.dumps(values, indent=2) + "\n")
    (args.output / "steps.jsonl").write_text("".join(json.dumps({"update": i + 1, "loss": value}) + "\n"
                                                    for i, value in enumerate(losses)))
    summary = {
        "algorithm": "multi-slot ordered proof-plan transition classifier; fresh float32 AdamW head; no RL",
        "packet_sha256": sha(args.packet.read_bytes()), "parent_sha256": file_sha(args.parent),
        "manifest_sha256": packet["manifest_sha256"], "slots": list(plan.SLOTS), "vocab": plan.VOCAB,
        "train_rows": 17, "development_rows": 4, "requested_updates": args.updates,
        "updates": len(losses), "hidden_size": hidden_size, "checkpoint_sha256": sha(head_path.read_bytes()),
        "base_generations": 4, "parent_generations": 4, "child_generations": 4,
        "prompt_tokens": prompt_tokens, "development_targets_exported": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "strict_verifier_runs": 0, "quality_claim": False, "proof_claim": False,
        "gate_claim": False, "loss_first_last": [losses[0], losses[-1]],
        "elapsed_seconds": time.monotonic() - started,
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "config.json").write_text(json.dumps({
        "seed": args.seed, "lr": args.lr, "updates": args.updates,
        "model_files": model_files(args.model), "parent_sha256": file_sha(args.parent),
        "packet_sha256": sha(args.packet.read_bytes()), "max_prompt_tokens": 8192,
    }, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--updates", type=int, default=16)
    parser.add_argument("--lr", type=float, default=0.02)
    parser.add_argument("--seed", type=int, default=20260917)
    args = parser.parse_args()
    print(json.dumps(worker(args), indent=2), flush=True)


if __name__ == "__main__":
    main()
