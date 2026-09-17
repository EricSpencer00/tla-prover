#!/usr/bin/env python3
"""Train and pair-evaluate a typed proof-fragment PIR worker on Polaris.

This worker is deliberately narrower than the protected gate.  It trains only
the final transformer layer with response-only causal SFT on the admitted
17-row PIR packet.  The four development prompts are target-free.  Parent and
child generations are recorded on exactly the same prompts; decoding is a
strict JSON/type check with no repair, verifier feedback, reward, or candidate
selection.  Strict TLAPS scoring belongs to the independent scorer.
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
sys.path.insert(0, str(ROOT))

from tools import proof_fragment_pir as pir
from tools.proof_fragment_delimited_pir import PACKET_KIND as DELIMITED_PACKET_KIND, decode_stream
from tools.proof_candidate_rank import encode_candidate
from tools.proof_cuda_train import (
    PROFILE,
    file_sha,
    load_policy,
    model_files,
    restore_policy,
    schedule,
    select_final_layer,
)

PACKET_SHA256 = "095d2d0a070961150d76575e5768f3ce615ee01b283a844c69d24f8a4661f5f5"
DELIMITED_PACKET_SHA256 = "30e594b4e82de3f8d455e2a87597e175d79bcb6cd31d67e55de84b384e53baaf"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
MANIFEST_SHA256 = pir.MANIFEST_SHA256
TRAIN_IDS = pir.TRAIN_IDS
DEV_IDS = pir.DEV_IDS
ALGORITHM = "typed-token response-only causal cross-entropy SFT; fresh float32 AdamW; no RL"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")


def load_packet(packet_path: Path, expected_sha: str = PACKET_SHA256) -> dict:
    raw = packet_path.read_bytes()
    if sha(raw) != expected_sha:
        raise ValueError("exact admitted PIR packet SHA required")
    packet = json.loads(raw)
    packet_kind = packet.get("packet_kind")
    if packet_kind not in {"frozen17_typed_proof_fragment_pir", DELIMITED_PACKET_KIND}:
        raise ValueError("unexpected PIR packet kind")
    if packet.get("manifest_sha256") != MANIFEST_SHA256:
        raise ValueError("PIR manifest binding changed")
    train = packet.get("train_rows", [])
    dev = packet.get("development_rows", [])
    if len(train) != 17 or {row.get("id") for row in train} != TRAIN_IDS:
        raise ValueError("exact 17-row PIR TRAIN population required")
    if len(dev) != 4 or {row.get("id") for row in dev} != DEV_IDS:
        raise ValueError("exact four-row PIR DEVELOPMENT population required")
    if packet.get("development_targets_exported") is not False:
        raise ValueError("development targets must remain unexported")
    if packet.get("verifier_feedback_used") or packet.get("repair_used") or packet.get("reward_used"):
        raise ValueError("PIR packet cannot contain verifier feedback, repair, or reward")
    for row in train:
        if packet_kind == DELIMITED_PACKET_KIND:
            required = {"id", "split", "source_family", "source_sha256", "assembled_sha256",
                        "prompt", "target_stream", "target_sha256", "target_records"}
            if set(row) != required or not row["prompt"] or sha(row["target_stream"].encode()) != row["target_sha256"]:
                raise ValueError("unexpected or changed delimited TRAIN row")
            if not decode_stream(row["target_stream"]):
                raise ValueError("empty delimited target")
        else:
            required = {"id", "split", "source_family", "source_sha256", "assembled_sha256",
                        "prompt", "prompt_sha256", "pir_target", "pir_target_sha256", "target_tokens"}
            if set(row) != required:
                raise ValueError("unexpected TRAIN packet fields")
            if row["split"] != "train" or sha(row["prompt"].encode()) != row["prompt_sha256"]:
                raise ValueError("TRAIN prompt binding changed")
            if pir.decode_tokens(row["pir_target"]) == "":
                raise ValueError("empty PIR target")
            target = pir.target_text(pir.decode_tokens(row["pir_target"]))
            if sha(target.encode()) != row["pir_target_sha256"]:
                raise ValueError("TRAIN typed target binding changed")
    for row in dev:
        if row.get("split") != "development":
            raise ValueError("development split binding changed")
        pir.reject_answer_fields(row)
        if "prompt_sha256" in row and sha(row["prompt"].encode()) != row["prompt_sha256"]:
            raise ValueError("DEVELOPMENT prompt binding changed")
    return packet


def preflight(packet_path: Path, parent_path: Path, expected_packet_sha: str, expected_parent_sha: str) -> dict:
    packet = load_packet(packet_path, expected_packet_sha)
    parent_raw = parent_path.read_bytes()
    if sha(parent_raw) != expected_parent_sha:
        raise ValueError("exact approved parent checkpoint SHA required")
    return {
        "packet_sha256": sha(packet_path.read_bytes()),
        "parent_sha256": sha(parent_raw),
        "manifest_sha256": packet["manifest_sha256"],
        "train_rows": len(packet["train_rows"]),
        "development_rows": len(packet["development_rows"]),
        "development_targets_exported": packet["development_targets_exported"],
        "verifier_feedback_used": packet["verifier_feedback_used"],
        "repair_used": packet["repair_used"],
        "reward_used": packet["reward_used"],
        "model_loaded": False,
        "cuda_touched": False,
        "optimizer_updates": 0,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
    }


def decode_pir_reply(reply: str, packet_kind: str = "frozen17_typed_proof_fragment_pir") -> dict:
    """Decode a complete packet-specific stream; never repair output."""
    result = {"raw_reply": reply, "valid": False,
              "status": "malformed_delimited" if packet_kind == DELIMITED_PACKET_KIND else "malformed_json"}
    try:
        if packet_kind == DELIMITED_PACKET_KIND:
            fragment = decode_stream(reply)
            result.update(valid=True, status="decoded", fragment=fragment)
        else:
            tokens = json.loads(reply)
            if not tokens:
                raise ValueError("empty typed token stream")
            fragment = pir.decode_tokens(tokens)
            result.update(valid=True, status="decoded", typed_tokens=tokens, fragment=fragment)
    except (json.JSONDecodeError, TypeError, ValueError) as exc:
        result["reason"] = str(exc)
    return result


def _encode(tokenizer, prompt: str, target: str, max_tokens: int) -> dict:
    encoded = encode_candidate(tokenizer, prompt, target, max_tokens)
    if encoded["response_tokens"] < 3:
        raise ValueError("PIR response must contain multiple tokens plus EOS")
    return encoded


def _generate(net, tokenizer, prompt: str, max_new_tokens: int, device: str, packet_kind: str) -> dict:
    import torch

    rendered = tokenizer.apply_chat_template(
        [dict(role="user", content=prompt)], tokenize=False, add_generation_prompt=True
    )
    inputs = tokenizer(rendered, return_tensors="pt", add_special_tokens=False).to(device)
    started = time.monotonic()
    with torch.inference_mode(), torch.autocast(device_type=device, dtype=torch.bfloat16):
        output = net.generate(
            **inputs, max_new_tokens=max_new_tokens, do_sample=False,
            pad_token_id=tokenizer.eos_token_id,
        )
    ids = output[0, inputs.input_ids.shape[1]:].tolist()
    reply = tokenizer.decode(ids, skip_special_tokens=True)
    row = dict(rendered_prompt=rendered, token_ids=ids, raw_reply=reply,
               output_tokens=len(ids), hit_token_limit=len(ids) >= max_new_tokens,
               generation_seconds=time.monotonic() - started)
    row.update(decode_pir_reply(reply, packet_kind))
    return row


def train(args) -> dict:
    import torch
    import transformers

    os.environ.update(
        HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1", TOKENIZERS_PARALLELISM="false",
        HF_HOME="/grand/EVITA/eric-spencer/hf-cache",
    )
    packet = load_packet(args.packet, args.expected_packet_sha256)
    if file_sha(args.parent) != args.expected_parent_sha256:
        raise ValueError("parent changed after preflight")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("Polaris CUDA bf16 is required; no CPU fallback")
    if not 1 <= args.updates <= 100 or not 1 <= args.seconds <= 600:
        raise ValueError("bounded update/time budget required")
    if not 1 <= args.max_tokens <= 8192 or not math.isfinite(args.lr) or args.lr <= 0:
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
    packet_kind = packet["packet_kind"]
    encoded = []
    for row in packet["train_rows"]:
        target = (row["target_stream"] if packet_kind == DELIMITED_PACKET_KIND
                  else pir.target_text(pir.decode_tokens(row["pir_target"])))
        encoded.append(_encode(tokenizer, row["prompt"], target, args.max_tokens))

    expected_files = model_files(args.model)
    net = load_policy(args.model)
    selected = select_final_layer(net, train=False)
    base_generations = []
    for row in packet["development_rows"]:
        base_generations.append(dict(id=row["id"], **_generate(net, tokenizer, row["prompt"], args.max_new_tokens, "cuda", packet_kind)))
    parent_saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    restore_policy(net, parent_saved, expected_files)
    parent_selected = select_final_layer(net, train=False)
    if any(p.requires_grad for p in parent_selected.values()):
        raise ValueError("parent inference layer unexpectedly trainable")

    started = time.monotonic()
    parent_generations = []
    for row in packet["development_rows"]:
        parent_generations.append(dict(id=row["id"], **_generate(net, tokenizer, row["prompt"], args.max_new_tokens, "cuda", packet_kind)))

    selected = select_final_layer(net, train=True)
    optimizer = torch.optim.AdamW(selected.values(), lr=args.lr, weight_decay=0, foreach=False)
    initial = {name: p.detach().cpu().clone() for name, p in selected.items()}
    indices = schedule(len(encoded), args.updates, args.seed)
    steps = []
    deadline = time.monotonic() + args.seconds
    for step, index in enumerate(indices, 1):
        if time.monotonic() >= deadline:
            break
        e = encoded[index]
        ids = torch.tensor([e["input_ids"]], device="cuda")
        labels = torch.tensor([e["labels"]], device="cuda")
        optimizer.zero_grad(set_to_none=True)
        with torch.autocast(device_type="cuda", dtype=torch.bfloat16):
            loss = net(input_ids=ids, labels=labels, use_cache=False).loss
        if not torch.isfinite(loss):
            raise RuntimeError("nonfinite loss")
        loss.backward()
        norm = torch.nn.utils.clip_grad_norm_(selected.values(), 1.0, error_if_nonfinite=True)
        optimizer.step()
        if any(not torch.isfinite(p).all() for p in selected.values()):
            raise RuntimeError("nonfinite parameter")
        steps.append(dict(step=step, id=packet["train_rows"][index]["id"], loss=float(loss),
                          gradient_norm=float(norm), response_tokens=e["response_tokens"],
                          elapsed_s=time.monotonic() - started))

    checkpoint = args.output / "policy_optimizer.pt"
    torch.save(dict(trainable_state={n: p.detach().cpu().clone() for n, p in selected.items()},
                    optimizer=optimizer.state_dict(), config=dict(model_files=expected_files,
                    dtype_profile=PROFILE), metrics=steps), checkpoint)
    child_generations = []
    for row in packet["development_rows"]:
        child_generations.append(dict(id=row["id"], **_generate(net, tokenizer, row["prompt"], args.max_new_tokens, "cuda", packet_kind)))

    delta = sum(float((selected[n].detach().cpu() - initial[n]).double().square().sum()) for n in initial) ** 0.5
    summary = dict(
        algorithm=("delimited-token " + ALGORITHM if packet_kind == DELIMITED_PACKET_KIND else ALGORITHM),
        packet_kind=packet_kind, packet_sha256=file_sha(args.packet), parent_sha256=file_sha(args.parent),
        model_files=expected_files, model_path=str(args.model), dtype_profile=PROFILE,
        train_rows=17, development_rows=4, requested_updates=args.updates, updates=len(steps),
        attempted_train_tasks=len({x["id"] for x in steps}), parameter_delta_l2=delta,
        seconds=time.monotonic() - started, checkpoint_sha256=file_sha(checkpoint),
        base_generations=4, parent_generations=4, child_generations=4,
        development_targets_exported=False, verifier_feedback_used=False, repair_used=False,
        reward_used=False, strict_verifier_runs=0, quality_claim=False, proof_claim=False, gate_claim=False,
    )
    dump(args.output / "config.json", dict(summary=summary, seed=args.seed, lr=args.lr,
         max_tokens=args.max_tokens, max_new_tokens=args.max_new_tokens, train_ids=[r["id"] for r in packet["train_rows"]]))
    (args.output / "steps.jsonl").write_text("\n".join(json.dumps(x) for x in steps) + ("\n" if steps else ""))
    dump(args.output / "base_generations.json", base_generations)
    dump(args.output / "parent_generations.json", parent_generations)
    dump(args.output / "child_generations.json", child_generations)
    dump(args.output / "summary.json", summary)
    return summary


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="mode", required=True)
    q = sub.add_parser("preflight")
    q.add_argument("--packet", type=Path, required=True)
    q.add_argument("--parent", type=Path, required=True)
    q.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    q.add_argument("--expected-parent-sha256", default=PARENT_SHA256)
    t = sub.add_parser("train")
    t.add_argument("--packet", type=Path, required=True)
    t.add_argument("--parent", type=Path, required=True)
    t.add_argument("--model", type=Path, required=True)
    t.add_argument("--output", type=Path, required=True)
    t.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    t.add_argument("--expected-parent-sha256", default=PARENT_SHA256)
    t.add_argument("--updates", type=int, default=16)
    t.add_argument("--seconds", type=int, default=540)
    t.add_argument("--max-tokens", type=int, default=8192)
    t.add_argument("--max-new-tokens", type=int, default=256)
    t.add_argument("--lr", type=float, default=1e-5)
    t.add_argument("--seed", type=int, default=20260917)
    args = p.parse_args()
    if args.mode == "preflight":
        print(json.dumps(preflight(args.packet, args.parent, args.expected_packet_sha256,
                                   args.expected_parent_sha256), indent=2))
        return 0
    print(json.dumps(train(args), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
