#!/usr/bin/env python3
"""Train a small autoregressive abstract proof-state transition decoder.

The Llama checkpoint is only a frozen prompt encoder. The trainable module is
an fp32 GRU over abstract event IDs, and its output is consumed by the frozen
symbolic renderer. Verifier results and DEVELOPMENT answers never enter this
worker; decoder loss is diagnostic, not acceptance.
"""
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

from tools import proof_state_transition as transition
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


class TransitionDecoder:
    """Thin wrapper kept torch-free at import time for CPU packet tests."""

    def __init__(self, torch, hidden_size: int, event_count: int, embedding_size=64, state_size=128):
        self.torch = torch
        self.module = torch.nn.Module()
        self.module.embedding = torch.nn.Embedding(event_count + 1, embedding_size)
        self.module.init = torch.nn.Linear(hidden_size, state_size)
        self.module.gru = torch.nn.GRU(embedding_size, state_size, batch_first=True)
        self.module.output = torch.nn.Linear(state_size, event_count)

    def parameters(self):
        return self.module.parameters()

    def state_dict(self):
        return self.module.state_dict()

    def load_state_dict(self, state):
        return self.module.load_state_dict(state)

    def to(self, device):
        self.module.to(device=device, dtype=self.torch.float32)
        return self

    def logits(self, hidden, inputs):
        torch = self.torch
        state = torch.tanh(self.module.init(hidden)).unsqueeze(0)
        embedded = self.module.embedding(inputs)
        output, _ = self.module.gru(embedded, state)
        return self.module.output(output)

    def trace_loss(self, hidden, ids, bos_id):
        torch = self.torch
        inputs = torch.tensor([[bos_id] + ids[:-1]], dtype=torch.long, device=hidden.device)
        targets = torch.tensor([ids], dtype=torch.long, device=hidden.device)
        logits = self.logits(hidden.unsqueeze(0), inputs)
        return torch.nn.functional.cross_entropy(logits.reshape(-1, logits.shape[-1]), targets.reshape(-1))

    def trace_log_probs(self, hidden, ids, bos_id):
        torch = self.torch
        inputs = torch.tensor([[bos_id] + ids[:-1]], dtype=torch.long, device=hidden.device)
        logits = self.logits(hidden.unsqueeze(0), inputs)[0]
        target = torch.tensor(ids, dtype=torch.long, device=hidden.device)
        return torch.log_softmax(logits.float(), dim=-1).gather(1, target.unsqueeze(1)).squeeze(1)


def score_rows(decoder, hidden, row, torch, bos_id):
    scores = []
    for ids in row["candidate_transition_ids"]:
        logs = decoder.trace_log_probs(hidden, ids, bos_id)
        scores.append(float(logs.mean().detach().cpu()))
    return transition.select_candidate(row, scores) | {"scores": scores}


def worker(args) -> dict:
    import torch
    import transformers

    packet = transition.load_packet(args.packet, args.expected_packet_sha256)
    if file_sha(args.parent) != transition.PARENT_SHA256:
        raise ValueError("exact approved parent checkpoint required")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("Polaris CUDA bf16 is required")
    if not 1 <= args.updates <= 64 or not 0 < args.lr <= 0.1:
        raise ValueError("bounded transition budget required")
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
    decoder = TransitionDecoder(torch, hidden_size, len(transition.EVENTS)).to("cuda")
    initial_state = copy.deepcopy(decoder.state_dict())
    optimizer = torch.optim.AdamW(decoder.parameters(), lr=args.lr, weight_decay=0.01)
    bos_id = len(transition.EVENTS)
    losses = []
    started = time.monotonic()
    for update in range(args.updates):
        loss = sum(decoder.trace_loss(hidden[row["id"]], row["transition_ids"], bos_id)
                   for row in packet["train_rows"]) / len(packet["train_rows"])
        if not torch.isfinite(loss):
            raise ValueError("nonfinite transition loss")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(list(decoder.parameters()), 1.0, error_if_nonfinite=True)
        optimizer.step()
        losses.append(float(loss.detach().cpu()))

    trained_state = copy.deepcopy(decoder.state_dict())
    dev_rows = packet["development_rows"]
    decoder.load_state_dict(initial_state)
    with torch.inference_mode():
        parent = [score_rows(decoder, hidden[row["id"]], row, torch, bos_id) for row in dev_rows]
    decoder.load_state_dict(initial_state)
    with torch.inference_mode():
        base = [{"id": row["id"], "valid": True, "candidate_index": 0,
                 "candidate": row["candidate_proposals"][0], "scores": [],
                 "transition_events": row["candidate_transition_events"][0]}
                for row in dev_rows]
    decoder.load_state_dict(trained_state)
    with torch.inference_mode():
        child = [score_rows(decoder, hidden[row["id"]], row, torch, bos_id) for row in dev_rows]

    args.output.mkdir(parents=True, exist_ok=False)
    decoder_path = args.output / "transition_decoder.pt"
    torch.save({"state_dict": trained_state, "events": list(transition.EVENTS),
                "hidden_size": hidden_size, "updates": args.updates}, decoder_path)
    for name, values in (("base_generations.json", base), ("parent_generations.json", parent),
                         ("child_generations.json", child)):
        (args.output / name).write_text(json.dumps(values, indent=2) + "\n")
    (args.output / "steps.jsonl").write_text(
        "".join(json.dumps({"update": index + 1, "loss": value}) + "\n"
                for index, value in enumerate(losses)))
    summary = {
        "algorithm": "autoregressive abstract proof-state transition decoder with frozen renderer",
        "packet_sha256": transition.sha(args.packet.read_bytes()),
        "parent_sha256": file_sha(args.parent), "manifest_sha256": packet["manifest_sha256"],
        "events": list(transition.EVENTS), "train_rows": 17, "development_rows": 4,
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in dev_rows),
        "requested_updates": args.updates, "updates": len(losses),
        "hidden_size": hidden_size, "decoder_sha256": transition.sha(decoder_path.read_bytes()),
        "base_generations": 4, "parent_generations": 4, "child_generations": 4,
        "prompt_tokens": prompt_tokens, "development_targets_exported": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "strict_verifier_runs": 0, "quality_claim": False, "proof_claim": False,
        "gate_claim": False, "loss_first_last": [losses[0], losses[-1]],
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    (args.output / "config.json").write_text(json.dumps({
        "seed": args.seed, "lr": args.lr, "updates": args.updates,
        "model_files": model_files(args.model), "parent_sha256": file_sha(args.parent),
        "packet_sha256": transition.sha(args.packet.read_bytes()), "max_prompt_tokens": 8192,
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
