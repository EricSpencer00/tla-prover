#!/usr/bin/env python3
"""Fit a prompt-only semantic proof-action signature head on Polaris.

The frozen Llama parent is used only as a prompt representation.  The trainable
component is a small multi-label head whose target is the sanitized signature
of a strict-SANY-certified answer-free proposal.  It never sees a candidate
response, proof fragment, protected row, verifier feedback, or official label.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

_ADMISSION_PATH = Path(__file__).with_name("proof_action_signature_admission.py")
_ADMISSION_SPEC = importlib.util.spec_from_file_location(
    "action_signature_admission_stage", _ADMISSION_PATH)
if _ADMISSION_SPEC is None or _ADMISSION_SPEC.loader is None:
    raise ImportError(f"cannot load staged admission module: {_ADMISSION_PATH}")
_ADMISSION = importlib.util.module_from_spec(_ADMISSION_SPEC)
_ADMISSION_SPEC.loader.exec_module(_ADMISSION)
HOLDOUT_IDS = _ADMISSION.HOLDOUT_IDS
LABELS_SHA256 = _ADMISSION.LABELS_SHA256
OFFICIAL_SHA256 = _ADMISSION.OFFICIAL_SHA256
PACKET_SHA256 = _ADMISSION.PACKET_SHA256
SLOTS = _ADMISSION.SLOTS
TRAIN_IDS = _ADMISSION.TRAIN_IDS
action_signature = _ADMISSION.action_signature
load_packets = _ADMISSION.load_packets
sha = _ADMISSION.sha
target_signatures = _ADMISSION.target_signatures

PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def prompt_encoding(tokenizer, prompt_text: str):
    messages = [{"role": "user", "content": prompt_text}]
    rendered = tokenizer.apply_chat_template(messages, tokenize=False,
                                              add_generation_prompt=True)
    encoded = tokenizer(rendered, add_special_tokens=False, truncation=False)
    ids = encoded["input_ids"]
    if not ids or len(ids) > 8192:
        raise ValueError("prompt encoding outside fixed context contract")
    return {"input_ids": ids, "prompt_sha256": sha(rendered.encode())}


def prompt_hidden(net, encoding, torch):
    ids = torch.tensor([encoding["input_ids"]], device="cuda")
    with torch.inference_mode(), torch.autocast(device_type="cuda", dtype=torch.bfloat16):
        output = net(input_ids=ids, use_cache=False, output_hidden_states=True)
        hidden = output.hidden_states[-1][0, -1].float()
    # Leave inference mode before cloning: the head is trainable and PyTorch
    # must be able to save this frozen input for its backward pass.
    return hidden.detach().clone()


def rank_rows(rows, representations, head, torch):
    rankings = {}
    probabilities = {}
    for row in rows:
        logits = head(representations[row["id"]]).float()
        probs = torch.sigmoid(logits).detach().cpu().tolist()
        if not all(math.isfinite(value) for value in probs):
            raise ValueError("nonfinite signature probabilities")
        values = []
        for index, candidate in enumerate(row["candidate_proposals"]):
            signature = action_signature(candidate)
            distance = sum(abs(float(prob) - bit)
                           for prob, bit in zip(probs, signature))
            values.append({"candidate_index": index, "candidate": candidate,
                           "signature": signature, "signature_distance": distance})
        rankings[row["id"]] = sorted(values,
                                      key=lambda item: (item["signature_distance"],
                                                        item["candidate_index"]))
        probabilities[row["id"]] = dict(zip(SLOTS, probs))
    return rankings, probabilities


def worker(args) -> None:
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, model_files, restore_policy

    train_bytes = args.train_packet.read_bytes()
    official_bytes = args.official_packet.read_bytes()
    labels_bytes = args.labels.read_bytes()
    if sha(train_bytes) != PACKET_SHA256 or sha(official_bytes) != OFFICIAL_SHA256:
        raise ValueError("packet hash mismatch")
    if sha(labels_bytes) != LABELS_SHA256:
        raise ValueError("label hash mismatch")
    packet, official, labels = load_packets(args.train_packet, args.official_packet,
                                             args.labels)
    targets = target_signatures(packet, labels)
    fit_rows = [row for row in packet["rows"] if row["id"] not in HOLDOUT_IDS
                and targets[row["id"]] is not None]
    holdout_rows = [row for row in packet["rows"] if row["id"] in HOLDOUT_IDS]
    if len(fit_rows) != 4 or len(holdout_rows) != 4:
        raise ValueError("frozen signature fit/holdout contract mismatch")
    torch.set_num_threads(4)
    torch.manual_seed(20260917)
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 support required")
    torch.cuda.reset_peak_memory_stats()
    net = load_policy(args.model, device="cuda")
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    selected = restore_policy(net, saved, model_files(args.model))
    if not all(torch.equal(parameter.detach().cpu(), saved["trainable_state"][name])
               for name, parameter in selected.items()):
        raise ValueError("exact parent restore failed")
    del saved
    net.eval().requires_grad_(False)
    representations = {}
    for row in packet["rows"] + official["rows"]:
        if row["id"] in representations:
            raise ValueError("duplicate row id across packets")
        representations[row["id"]] = prompt_hidden(
            net, prompt_encoding(tokenizer, row["prompt"]), torch)
    hidden_size = int(next(iter(representations.values())).shape[0])
    head = torch.nn.Linear(hidden_size, len(SLOTS), bias=True,
                           device="cuda", dtype=torch.float32)
    optimizer = torch.optim.AdamW(head.parameters(), lr=args.lr, weight_decay=0.01)
    fit_targets = torch.tensor([targets[row["id"]] for row in fit_rows],
                               device="cuda", dtype=torch.float32)
    started = time.monotonic()
    losses = []
    for _ in range(args.updates):
        matrix = torch.stack([representations[row["id"]] for row in fit_rows])
        logits = head(matrix)
        loss = torch.nn.functional.binary_cross_entropy_with_logits(logits, fit_targets)
        if not torch.isfinite(loss):
            raise ValueError("nonfinite signature loss")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(head.parameters(), 1.0, error_if_nonfinite=True)
        optimizer.step()
        losses.append(float(loss.detach().cpu()))
    holdout, holdout_probs = rank_rows(holdout_rows, representations, head, torch)
    official_rankings, official_probs = rank_rows(official["rows"], representations, head, torch)
    by_id = {row["id"]: row for row in packet["rows"]}
    holdout_rank1 = 0
    holdout_solvable = 0
    for task_id, ranking in holdout.items():
        positives = {i for i in range(4) if labels.get((task_id, i), 0)}
        if any(item["candidate_index"] in positives for item in ranking):
            holdout_solvable += 1
        if ranking and ranking[0]["candidate_index"] in positives:
            holdout_rank1 += 1
    output = args.output
    output.mkdir(parents=True, exist_ok=False)
    head_path = output / "signature_head.pt"
    torch.save({"state_dict": {key: value.detach().cpu() for key, value in head.state_dict().items()},
                "hidden_size": hidden_size, "slots": list(SLOTS),
                "updates": args.updates}, head_path)
    dump(output / "holdout-rankings.json", holdout)
    dump(output / "holdout-probabilities.json", holdout_probs)
    dump(output / "rankings.json", official_rankings)
    dump(output / "probabilities.json", official_probs)
    dump(output / "config.json", {
        "train_packet_sha256": PACKET_SHA256, "labels_sha256": LABELS_SHA256,
        "packet_sha256": OFFICIAL_SHA256, "checkpoint_sha256": sha(args.parent.read_bytes()),
        "selection_method": "frozen-parent prompt-terminal hidden state to multi-label semantic action signature",
        "slots": list(SLOTS), "fit_tasks": len(fit_rows), "holdout_tasks": len(holdout_rows),
        "parameter_updates": args.updates, "hidden_size": hidden_size,
        "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "candidate_response_hidden_state_used": False,
    })
    dump(output / "runtime.json", {
        "gpu": torch.cuda.get_device_name(), "torch_version": torch.__version__,
        "transformers_version": transformers.__version__, "parameter_updates": args.updates,
        "cuda_peak_allocated_bytes": torch.cuda.max_memory_allocated(),
        "cuda_peak_reserved_bytes": torch.cuda.max_memory_reserved(),
        "elapsed_seconds": time.monotonic() - started,
    })
    dump(output / "summary.json", {
        "fit_tasks": len(fit_rows), "holdout_tasks": len(holdout_rows),
        "parameter_updates": args.updates, "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "official_tasks_ranked": len(official_rankings),
        "official_candidates_ranked": sum(len(rows) for rows in official_rankings.values()),
        "representation": "prompt-terminal hidden state -> multi-label semantic action signature",
        "slots": list(SLOTS), "reference_fragment_used": False,
        "protected_verifier_feedback_used": False, "candidate_response_hidden_state_used": False,
        "tlaps_executed": False, "proof_or_quality_claim": False, "gate_claim": False,
        "loss_first_last": [losses[0], losses[-1]], "head_sha256": sha(head_path.read_bytes()),
        "elapsed_seconds": time.monotonic() - started,
    })
    print(json.dumps({"updates": args.updates, "fit_tasks": len(fit_rows),
                      "holdout_rank1_certified": holdout_rank1,
                      "official_tasks_ranked": len(official_rankings)}, indent=2), flush=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train-packet", required=True, type=Path)
    parser.add_argument("--official-packet", required=True, type=Path)
    parser.add_argument("--labels", required=True, type=Path)
    parser.add_argument("--model", required=True, type=Path)
    parser.add_argument("--parent", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--updates", type=int, default=16)
    parser.add_argument("--lr", type=float, default=0.02)
    args = parser.parse_args()
    if not 1 <= args.updates <= 16 or not 0 < args.lr <= 0.1:
        parser.error("bounded update/lr contract required")
    worker(args)


if __name__ == "__main__":
    main()
