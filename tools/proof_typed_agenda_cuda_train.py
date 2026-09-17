#!/usr/bin/env python3
"""Train a frozen-encoder multi-label typed proof-agenda head."""
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

from tools import proof_typed_agenda as agenda
from tools.proof_cuda_train import file_sha, load_policy, model_files, restore_policy

PROFILE = "frozen bf16 base with float32 final transformer layer; bf16 autocast"


def prompt_hidden(net, tokenizer, prompt: str, torch):
    rendered = tokenizer.apply_chat_template(
        [dict(role="user", content=prompt)], tokenize=False, add_generation_prompt=True)
    batch = tokenizer(rendered, return_tensors="pt", add_special_tokens=False)
    batch = {key: value.to("cuda") for key, value in batch.items()}
    with torch.inference_mode(), torch.autocast(device_type="cuda", dtype=torch.bfloat16):
        hidden = net(**batch, use_cache=False, output_hidden_states=True).hidden_states[-1][0, -1].float()
    return hidden.detach().clone(), int(batch["input_ids"].shape[1])


class AgendaHead:
    """Torch-free-at-import wrapper for a multi-label slot head."""

    def __init__(self, torch, hidden_size: int, slot_count: int):
        self.torch = torch
        self.module = torch.nn.Sequential(
            torch.nn.LayerNorm(hidden_size),
            torch.nn.Linear(hidden_size, slot_count),
        )

    def parameters(self):
        return self.module.parameters()

    def state_dict(self):
        return self.module.state_dict()

    def load_state_dict(self, state):
        return self.module.load_state_dict(state)

    def to(self, device):
        self.module.to(device=device, dtype=self.torch.float32)
        return self

    def logits(self, hidden):
        return self.module(hidden)

    def target(self, row, device):
        torch = self.torch
        target = torch.zeros(len(agenda.SLOTS), dtype=torch.float32, device=device)
        target[torch.tensor(row["agenda_slot_ids"], dtype=torch.long, device=device)] = 1.0
        return target


def candidate_score(logits, slot_ids, torch):
    target = torch.zeros_like(logits)
    target[torch.tensor(slot_ids, dtype=torch.long, device=logits.device)] = 1.0
    return float((-torch.nn.functional.binary_cross_entropy_with_logits(
        logits, target, reduction="mean")).detach().cpu())


def score_row(head, hidden, row, torch):
    logits = head.logits(hidden.unsqueeze(0))[0]
    scores = [candidate_score(logits, ids, torch) for ids in row["candidate_agenda_slot_ids"]]
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

    packet = agenda.load_packet(args.packet, args.expected_packet_sha256)
    if file_sha(args.parent) != agenda.PARENT_SHA256:
        raise ValueError("exact approved parent checkpoint required")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("Polaris CUDA bf16 is required")
    if not 1 <= args.updates <= 64 or not 0 < args.lr <= 0.1:
        raise ValueError("bounded agenda budget required")
    if args.output.exists():
        raise ValueError("output must be new")
    torch.manual_seed(args.seed)
    net = load_policy(args.model, device="cuda")
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    restore_policy(net, saved, model_files(args.model))
    net.eval().requires_grad_(False)

    all_rows = packet["train_rows"] + packet["development_rows"]
    hidden = {}
    prompt_tokens = {}
    for row in all_rows:
        hidden[row["id"]], prompt_tokens[row["id"]] = prompt_hidden(net, tokenizer, row["prompt"], torch)
    hidden_size = int(next(iter(hidden.values())).shape[0])
    head = AgendaHead(torch, hidden_size, len(agenda.SLOTS)).to("cuda")
    initial_state = copy.deepcopy(head.state_dict())
    optimizer = torch.optim.AdamW(head.parameters(), lr=args.lr, weight_decay=0.01)
    losses = []
    started = time.monotonic()
    for update in range(args.updates):
        losses_now = []
        for row in packet["train_rows"]:
            logits = head.logits(hidden[row["id"]].unsqueeze(0))[0]
            losses_now.append(torch.nn.functional.binary_cross_entropy_with_logits(
                logits, head.target(row, logits.device)))
        loss = sum(losses_now) / len(losses_now)
        if not torch.isfinite(loss):
            raise ValueError("nonfinite agenda loss")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(list(head.parameters()), 1.0, error_if_nonfinite=True)
        optimizer.step()
        losses.append(float(loss.detach().cpu()))

    trained_state = copy.deepcopy(head.state_dict())
    dev_rows = packet["development_rows"]
    head.load_state_dict(initial_state)
    with torch.inference_mode():
        parent = [score_row(head, hidden[row["id"]], row, torch) for row in dev_rows]
    base = [{
        "id": row["id"], "valid": True, "candidate_index": 0,
        "candidate": row["candidate_proposals"][0],
        "agenda_slots": row["candidate_agenda_slots"][0], "agenda_score": 0.0, "scores": [],
    } for row in dev_rows]
    head.load_state_dict(trained_state)
    with torch.inference_mode():
        child = [score_row(head, hidden[row["id"]], row, torch) for row in dev_rows]

    args.output.mkdir(parents=True, exist_ok=False)
    head_path = args.output / "agenda_head.pt"
    torch.save({"state_dict": trained_state, "slots": list(agenda.SLOTS),
                "hidden_size": hidden_size, "updates": args.updates}, head_path)
    for name, values in (("base_generations.json", base), ("parent_generations.json", parent),
                         ("child_generations.json", child)):
        (args.output / name).write_text(json.dumps(values, indent=2) + "\n")
    (args.output / "steps.jsonl").write_text(
        "".join(json.dumps({"update": index + 1, "loss": value}) + "\n"
                for index, value in enumerate(losses)))
    summary = {
        "algorithm": "multi-label typed proof-agenda head with deterministic renderer",
        "packet_sha256": agenda.sha(args.packet.read_bytes()), "parent_sha256": file_sha(args.parent),
        "manifest_sha256": packet["manifest_sha256"], "slots": list(agenda.SLOTS),
        "train_rows": 17, "development_rows": 4,
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in dev_rows),
        "requested_updates": args.updates, "updates": len(losses), "hidden_size": hidden_size,
        "head_sha256": agenda.sha(head_path.read_bytes()), "base_generations": 4,
        "parent_generations": 4, "child_generations": 4, "prompt_tokens": prompt_tokens,
        "development_targets_exported": False, "candidate_index_labels_used": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "strict_verifier_runs": 0, "quality_claim": False, "proof_claim": False,
        "gate_claim": False, "loss_first_last": [losses[0], losses[-1]],
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "config.json").write_text(json.dumps({
        "seed": args.seed, "lr": args.lr, "updates": args.updates,
        "model_files": model_files(args.model), "parent_sha256": file_sha(args.parent),
        "packet_sha256": agenda.sha(args.packet.read_bytes()), "max_prompt_tokens": 8192,
        "dtype_profile": PROFILE,
    }, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--updates", type=int, default=32)
    parser.add_argument("--lr", type=float, default=0.01)
    parser.add_argument("--seed", type=int, default=20260917)
    args = parser.parse_args()
    print(json.dumps(worker(args), indent=2), flush=True)


if __name__ == "__main__":
    main()
