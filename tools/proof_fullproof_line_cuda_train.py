#!/usr/bin/env python3
"""Train and pair-evaluate structured full-proof line-event generation.

Only the final transformer layer is updated from the exact non-protected TRAIN
packet.  DEVELOPMENT prompts are target-free.  The model emits a JSON line
event sequence which is decoded without repair; independent SANY/TLAPS scoring
is intentionally outside this worker.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullproof_line_packet as line_packet
from tools.proof_candidate_rank import encode_candidate
from tools.proof_cuda_train import PROFILE, file_sha, load_policy, model_files, restore_policy, schedule, select_final_layer

PACKET_SHA256 = "7ec5b64bebe1df1e9fa9c93ec33e66e819a33fbeb0b5aede7fecfeca27b91d79"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
ALGORITHM = "structured line-event response-only causal cross-entropy SFT; fresh float32 AdamW; no RL"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def load_packet(path: Path, expected_sha: str = PACKET_SHA256) -> dict:
    raw = path.read_bytes()
    if sha(raw) != expected_sha:
        raise ValueError("exact structured line-event packet SHA required")
    packet = json.loads(raw)
    if packet.get("packet_kind") != "frozen17_structured_fullproof_line_events":
        raise ValueError("unexpected line-event packet kind")
    if packet.get("manifest_sha256") != line_packet.MANIFEST_SHA256:
        raise ValueError("manifest binding changed")
    if packet.get("development_targets_exported") is not False:
        raise ValueError("development targets must remain unexported")
    train, dev = packet.get("train_rows", []), packet.get("development_rows", [])
    if len(train) != 17 or {row.get("id") for row in train} != line_packet.TRAIN_IDS:
        raise ValueError("exact17 TRAIN rows required")
    if len(dev) != 4 or {row.get("id") for row in dev} != line_packet.DEV_IDS:
        raise ValueError("exact4 DEVELOPMENT rows required")
    for row in train:
        if set(row) != {"id", "split", "module_name", "theorem_name", "source_family",
                         "prompt", "prompt_sha256", "target_events", "target_events_sha256",
                         "target_lines", "assembled_sha256"}:
            raise ValueError("unexpected TRAIN fields")
        if sha(row["prompt"].encode()) != row["prompt_sha256"]:
            raise ValueError("TRAIN prompt binding changed")
        if line_packet.digest(row["target_events"]) != row["target_events_sha256"]:
            raise ValueError("TRAIN event target binding changed")
        if line_packet.decode_fragment(row["target_events"]) == "":
            raise ValueError("empty TRAIN event target")
    for row in dev:
        line_packet.reject(row)
        if "target_events" in row or "reference_fragment" in row:
            raise ValueError("DEVELOPMENT target leaked")
    return packet


def preflight(packet_path: Path, parent_path: Path, expected_packet_sha: str,
              expected_parent_sha: str) -> dict:
    packet = load_packet(packet_path, expected_packet_sha)
    parent_raw = parent_path.read_bytes()
    if sha(parent_raw) != expected_parent_sha:
        raise ValueError("exact approved parent checkpoint SHA required")
    return {
        "packet_sha256": sha(packet_path.read_bytes()), "parent_sha256": sha(parent_raw),
        "manifest_sha256": packet["manifest_sha256"], "train_rows": len(packet["train_rows"]),
        "development_rows": len(packet["development_rows"]),
        "development_targets_exported": False, "model_loaded": False,
        "cuda_touched": False, "optimizer_updates": 0, "quality_claim": False,
        "proof_claim": False, "gate_claim": False,
    }


def target_text(row: dict) -> str:
    return json.dumps(row["target_events"], separators=(",", ":"), ensure_ascii=False)


def decode_reply(reply: str) -> dict:
    result = {"raw_reply": reply, "valid": False, "status": "malformed_line_events"}
    try:
        events = json.loads(reply)
        fragment = line_packet.decode_fragment(events)
        result.update(valid=True, status="decoded", events=events, fragment=fragment)
    except (json.JSONDecodeError, TypeError, ValueError) as exc:
        result["reason"] = str(exc)
    return result


def development_prompt(row: dict) -> str:
    prompt = row.get("prompt", row.get("prefix"))
    if not isinstance(prompt, str) or not prompt:
        raise ValueError("target-free DEVELOPMENT prefix is required")
    return prompt


def generate(net, tokenizer, prompt: str, max_new_tokens: int) -> dict:
    import torch
    rendered = tokenizer.apply_chat_template(
        [dict(role="user", content=prompt)], tokenize=False, add_generation_prompt=True)
    inputs = tokenizer(rendered, return_tensors="pt", add_special_tokens=False).to("cuda")
    started = time.monotonic()
    with torch.inference_mode(), torch.autocast(device_type="cuda", dtype=torch.bfloat16):
        output = net.generate(**inputs, max_new_tokens=max_new_tokens, do_sample=False,
                              pad_token_id=tokenizer.eos_token_id)
    ids = output[0, inputs.input_ids.shape[1]:].tolist()
    reply = tokenizer.decode(ids, skip_special_tokens=True)
    row = {"rendered_prompt": rendered, "token_ids": ids, "raw_reply": reply,
           "output_tokens": len(ids), "hit_token_limit": len(ids) >= max_new_tokens,
           "generation_seconds": time.monotonic() - started}
    row.update(decode_reply(reply))
    return row


def train(args) -> dict:
    import torch
    import transformers
    os.environ.update(HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1",
                      TOKENIZERS_PARALLELISM="false", HF_HOME="/grand/EVITA/eric-spencer/hf-cache")
    packet = load_packet(args.packet, args.expected_packet_sha256)
    if file_sha(args.parent) != args.expected_parent_sha256:
        raise ValueError("parent changed after preflight")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("Polaris CUDA bf16 is required; no CPU fallback")
    if not 1 <= args.updates <= 16 or not 1 <= args.seconds <= 600:
        raise ValueError("bounded update/time budget required")
    if not 1 <= args.max_tokens <= 8192 or not 1 <= args.max_new_tokens <= 1024 or args.lr <= 0:
        raise ValueError("invalid sequence or learning-rate budget")
    if args.output.exists():
        raise ValueError("output must be new")
    args.output.mkdir(parents=True)
    (args.output / "packet.json").write_bytes(args.packet.read_bytes())
    random.seed(args.seed)
    torch.manual_seed(args.seed)
    torch.cuda.manual_seed_all(args.seed)
    torch.backends.cuda.matmul.allow_tf32 = False
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    encoded = []
    for row in packet["train_rows"]:
        encoded.append(encode_candidate(tokenizer, row["prompt"], target_text(row), args.max_tokens))
    expected_files = model_files(args.model)
    net = load_policy(args.model, device="cuda")
    select_final_layer(net, train=False)
    base = [dict(id=row["id"], **generate(net, tokenizer, development_prompt(row), args.max_new_tokens))
            for row in packet["development_rows"]]
    saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    restore_policy(net, saved, expected_files)
    parent = [dict(id=row["id"], **generate(net, tokenizer, development_prompt(row), args.max_new_tokens))
              for row in packet["development_rows"]]
    selected = select_final_layer(net, train=True)
    optimizer = torch.optim.AdamW(selected.values(), lr=args.lr, weight_decay=0, foreach=False)
    initial = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    started = time.monotonic()
    steps = []
    deadline = started + args.seconds
    for step, index in enumerate(schedule(len(encoded), args.updates, args.seed), 1):
        if time.monotonic() >= deadline:
            break
        item = encoded[index]
        ids = torch.tensor([item["input_ids"]], device="cuda")
        labels = torch.tensor([item["labels"]], device="cuda")
        optimizer.zero_grad(set_to_none=True)
        with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
            loss = net(input_ids=ids, labels=labels, use_cache=False).loss
        if not torch.isfinite(loss):
            raise RuntimeError("nonfinite loss")
        loss.backward()
        norm = torch.nn.utils.clip_grad_norm_(selected.values(), 1.0, error_if_nonfinite=True)
        optimizer.step()
        if any(not torch.isfinite(parameter).all() for parameter in selected.values()):
            raise RuntimeError("nonfinite parameter")
        steps.append({"step": step, "id": packet["train_rows"][index]["id"],
                      "loss": float(loss), "gradient_norm": float(norm),
                      "response_tokens": item["response_tokens"],
                      "elapsed_s": time.monotonic() - started})
    checkpoint = args.output / "policy_optimizer.pt"
    torch.save({"trainable_state": {name: p.detach().cpu().clone() for name, p in selected.items()},
                "optimizer": optimizer.state_dict(), "config": {"model_files": expected_files,
                "dtype_profile": PROFILE}}, checkpoint)
    child = [dict(id=row["id"], **generate(net, tokenizer, development_prompt(row), args.max_new_tokens))
             for row in packet["development_rows"]]
    delta = sum(float((selected[name].detach().cpu() - initial[name]).double().square().sum())
                for name in initial) ** 0.5
    summary = {
        "algorithm": ALGORITHM, "packet_kind": packet["packet_kind"],
        "packet_sha256": file_sha(args.packet), "parent_sha256": file_sha(args.parent),
        "model_files": expected_files, "model_path": str(args.model), "dtype_profile": PROFILE,
        "train_rows": 17, "development_rows": 4, "requested_updates": args.updates,
        "updates": len(steps), "attempted_train_tasks": len({x["id"] for x in steps}),
        "parameter_delta_l2": delta, "seconds": time.monotonic() - started,
        "checkpoint_sha256": file_sha(checkpoint), "base_generations": 4,
        "parent_generations": 4, "child_generations": 4,
        "development_targets_exported": False, "verifier_feedback_used": False,
        "repair_used": False, "reward_used": False, "strict_verifier_runs": 0,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
    }
    dump(args.output / "config.json", dict(summary=summary, seed=args.seed, lr=args.lr,
         max_tokens=args.max_tokens, max_new_tokens=args.max_new_tokens,
         train_ids=[row["id"] for row in packet["train_rows"]]))
    (args.output / "steps.jsonl").write_text("\n".join(json.dumps(x) for x in steps) +
                                             ("\n" if steps else ""))
    dump(args.output / "base_generations.json", base)
    dump(args.output / "parent_generations.json", parent)
    dump(args.output / "child_generations.json", child)
    dump(args.output / "summary.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="mode", required=True)
    pre = sub.add_parser("preflight")
    pre.add_argument("--packet", type=Path, required=True)
    pre.add_argument("--parent", type=Path, required=True)
    pre.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    pre.add_argument("--expected-parent-sha256", default=PARENT_SHA256)
    train_parser = sub.add_parser("train")
    train_parser.add_argument("--packet", type=Path, required=True)
    train_parser.add_argument("--parent", type=Path, required=True)
    train_parser.add_argument("--model", type=Path, required=True)
    train_parser.add_argument("--output", type=Path, required=True)
    train_parser.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    train_parser.add_argument("--expected-parent-sha256", default=PARENT_SHA256)
    train_parser.add_argument("--updates", type=int, default=16)
    train_parser.add_argument("--seconds", type=int, default=540)
    train_parser.add_argument("--max-tokens", type=int, default=8192)
    train_parser.add_argument("--max-new-tokens", type=int, default=512)
    train_parser.add_argument("--lr", type=float, default=1e-5)
    train_parser.add_argument("--seed", type=int, default=20260917)
    args = parser.parse_args()
    if args.mode == "preflight":
        print(json.dumps(preflight(args.packet, args.parent, args.expected_packet_sha256,
                                   args.expected_parent_sha256), indent=2))
        return 0
    print(json.dumps(train(args), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
