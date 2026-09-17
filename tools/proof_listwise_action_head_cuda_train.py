#!/usr/bin/env python3
"""Train and evaluate a task-normalized listwise action head on Polaris.

The Llama parent is restored exactly and kept frozen.  Only a float32 linear
head over pooled response hidden states is trained with task-normalized
listwise cross-entropy on strict labels from the non-protected 17-row action
packet.  Four non-protected tasks are held out.
The official119 packet is prediction-only; this worker never runs TLAPS and
never reads protected verifier results.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}
TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}
HOLDOUT_IDS = {
    "highest-done-step", "highest-correctness", "simple-preservation",
    "simple-short-full",
}
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
OFFICIAL_SHA256 = "f40539a20e449ad63b8244e85eff33c8022402df11a84e8228b71ccbfeae11b5"
TRAIN_SHA256 = "c9784d4da893464f23bc27610c5f7aed64c44bf5406a7ec33f27637ad0d7394f"
TRAIN_LABELS_SHA256 = "bba10249105e1999656dd329a642c079f623f64fd9a4ee49f574c390d34a7854"
BUDGET = {
    "train_tasks": 13,
    "holdout_tasks": 4,
    "max_updates": 16,
    "score_seconds": 720,
    "parameter_updates": 16,
    "resources": "one Polaris GPU, 64 CPUs, 00:15:00",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def reject_keys(value, path="document"):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def validate_packet(packet: dict, kind: str, expected_rows: int):
    reject_keys(packet)
    expected_kind = (
        "answer_free_multistep_symbolic_action_coverage"
        if kind == "train" else "answer_free_official_symbolic_candidate_ranking"
    )
    if packet.get("packet_kind") != expected_kind or packet.get("denominator") != expected_rows:
        raise ValueError(f"unexpected {kind} packet contract")
    if len(packet.get("rows", [])) != expected_rows:
        raise ValueError(f"{kind} denominator mismatch")
    if kind == "train" and {row["id"] for row in packet["rows"]} != TRAIN_IDS:
        raise ValueError("frozen training membership mismatch")
    for row in packet["rows"]:
        if not row.get("prompt") or not row.get("candidate_proposals"):
            raise ValueError("prompt/candidate missing")
        if len(set(row["candidate_proposals"])) != len(row["candidate_proposals"]):
            raise ValueError("duplicate candidate")
    return packet["rows"]


def load_labels(path: Path, train_rows: dict[str, dict]):
    labels: dict[str, dict[int, int]] = {task_id: {} for task_id in TRAIN_IDS}
    for line in path.read_text().splitlines():
        record = json.loads(line)
        if set(record) != {"task", "candidate_index", "candidate", "certified"}:
            raise ValueError("labels must be sanitized task/candidate/certified records")
        task_id, index = record["task"], record["candidate_index"]
        if task_id not in TRAIN_IDS or not isinstance(index, int):
            raise ValueError("label outside training set")
        row = train_rows[task_id]
        if not 0 <= index < len(row["candidate_proposals"]):
            raise ValueError("label index outside packet")
        if record["candidate"] != row["candidate_proposals"][index]:
            raise ValueError("label candidate mismatch")
        labels[task_id][index] = int(bool(record["certified"]))
    if sum(len(value) for value in labels.values()) < 17:
        raise ValueError("insufficient labels")
    return labels


def encode_candidate(tokenizer, prompt_text: str, candidate: str, max_tokens: int = 8192):
    messages = [dict(role="user", content=prompt_text)]
    prompt = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
    full = tokenizer.apply_chat_template(
        messages + [dict(role="assistant", content=candidate)],
        tokenize=False, add_generation_prompt=False)
    prefix = tokenizer(prompt, add_special_tokens=False, truncation=False)["input_ids"]
    ids = tokenizer(full, add_special_tokens=False, truncation=False)["input_ids"]
    if not prefix or ids[:len(prefix)] != prefix:
        raise ValueError("chat template changed prompt boundary")
    response = ids[len(prefix):]
    if not response or not isinstance(tokenizer.eos_token_id, int) or tokenizer.eos_token_id not in response:
        raise ValueError("candidate missing terminal EOS")
    ids = ids[:len(prefix) + response.index(tokenizer.eos_token_id) + 1]
    if len(ids) > max_tokens:
        raise ValueError("candidate exceeds context budget")
    return {"input_ids": ids, "labels": [-100] * len(prefix) + ids[len(prefix):]}


def listwise_loss(scores, labels, torch):
    positives = [i for i, label in enumerate(labels) if label]
    if not positives:
        raise ValueError("task has no certified action")
    # Normalize within each complete candidate set so tasks with wider
    # proposal lists do not contribute more pairwise terms than narrow tasks.
    return -torch.log_softmax(scores, dim=0)[positives].mean()


def pool_response(net, encoding, device, torch):
    ids = torch.tensor([encoding["input_ids"]], device=device)
    labels = torch.tensor(encoding["labels"], device=device)
    with torch.inference_mode(), torch.autocast(device_type="cuda", dtype=torch.bfloat16):
        output = net(input_ids=ids, use_cache=False, output_hidden_states=True)
        hidden = output.hidden_states[-1][0].float()
    mask = labels != -100
    if not bool(mask.any()):
        raise ValueError("empty response representation")
    return hidden[mask].mean(dim=0).detach()


def score_rankings(rows, representations, head, torch):
    ranked = {}
    for row in rows:
        values = []
        for index, candidate in enumerate(row["candidate_proposals"]):
            value = head(representations[(row["id"], index)]).squeeze()
            score = float(value.detach().cpu())
            if not math.isfinite(score):
                raise ValueError("nonfinite head score")
            values.append({"candidate_index": index, "candidate": candidate,
                           "mean_logp": score, "action_head_score": score})
        ranked[row["id"]] = sorted(values, key=lambda item: (-item["action_head_score"], item["candidate_index"]))
    return ranked


def worker(args):
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, model_files, restore_policy

    train_bytes = args.train_packet.read_bytes()
    official_bytes = args.official_packet.read_bytes()
    labels_bytes = args.labels.read_bytes()
    if sha(train_bytes) != TRAIN_SHA256 or sha(official_bytes) != OFFICIAL_SHA256:
        raise ValueError("packet hash mismatch")
    if sha(labels_bytes) != TRAIN_LABELS_SHA256:
        raise ValueError("label hash mismatch")
    train_rows = validate_packet(json.loads(train_bytes), "train", 17)
    official_rows = validate_packet(json.loads(official_bytes), "official", 119)
    train_by_id = {row["id"]: row for row in train_rows}
    labels = load_labels(args.labels, train_by_id)
    train_rows_for_fit = [row for row in train_rows if row["id"] not in HOLDOUT_IDS]
    if len(train_rows_for_fit) != 13:
        raise ValueError("exact 13-task fit set required")
    torch.set_num_threads(4)
    torch.manual_seed(20260917)
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 support required")
    torch.cuda.reset_peak_memory_stats()
    files = model_files(args.model)
    net = load_policy(args.model, device="cuda")
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    saved = torch.load(args.parent, map_location="cpu", weights_only=False)
    selected = restore_policy(net, saved, files)
    if not all(torch.equal(parameter.detach().cpu(), saved["trainable_state"][name])
               for name, parameter in selected.items()):
        raise ValueError("exact parent restore failed")
    del saved
    net.eval().requires_grad_(False)
    encoded = {}
    representations = {}
    all_rows = train_rows + official_rows
    for row in all_rows:
        for index, candidate in enumerate(row["candidate_proposals"]):
            encoding = encode_candidate(tokenizer, row["prompt"], candidate)
            encoded[(row["id"], index)] = encoding
            representations[(row["id"], index)] = pool_response(net, encoding, "cuda", torch)
    hidden_size = int(next(iter(representations.values())).shape[0])
    head = torch.nn.Linear(hidden_size, 1, bias=True, device="cuda", dtype=torch.float32)
    optimizer = torch.optim.AdamW(head.parameters(), lr=args.lr, weight_decay=0.01)
    fit_rows = {row["id"]: row for row in train_rows_for_fit}
    started = time.monotonic()
    updates = 0
    losses = []
    for _ in range(args.updates):
        total = []
        for row in train_rows_for_fit:
            candidates = row["candidate_proposals"]
            scores = torch.cat([head(representations[(row["id"], index)]) for index in range(len(candidates))])
            task_labels = [labels[row["id"]].get(index, 0) for index in range(len(candidates))]
            if any(task_labels) and not all(task_labels):
                total.append(listwise_loss(scores, task_labels, torch))
        if not total:
            raise ValueError("fit set has no pairwise labels")
        loss = torch.stack(total).mean()
        if not torch.isfinite(loss):
            raise ValueError("nonfinite action-head loss")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        torch.nn.utils.clip_grad_norm_(head.parameters(), 1.0, error_if_nonfinite=True)
        optimizer.step()
        updates += 1
        losses.append(float(loss.detach().cpu()))
    holdout_rows = [row for row in train_rows if row["id"] in HOLDOUT_IDS]
    holdout = score_rankings(holdout_rows, representations, head, torch)
    holdout_rank1 = sum(labels[task_id].get(rows[0]["candidate_index"]) == 1
                        for task_id, rows in holdout.items())
    holdout_solvable = sum(any(labels[task_id].get(item["candidate_index"]) == 1 for item in rows)
                           for task_id, rows in holdout.items())
    official = score_rankings(official_rows, representations, head, torch)
    output = args.output
    output.mkdir(parents=True, exist_ok=False)
    head_path = output / "action_head.pt"
    torch.save({"state_dict": {key: value.detach().cpu() for key, value in head.state_dict().items()},
                "hidden_size": hidden_size, "updates": updates}, head_path)
    dump(output / "holdout-rankings.json", holdout)
    dump(output / "rankings.json", official)
    dump(output / "config.json", {
        "train_packet_sha256": TRAIN_SHA256, "labels_sha256": TRAIN_LABELS_SHA256,
        "packet_sha256": OFFICIAL_SHA256, "checkpoint_sha256": sha(args.parent.read_bytes()),
        "selection_method": "frozen-parent pooled hidden-state linear listwise action head",
        "learning_signal": "task-normalized listwise cross-entropy over complete candidate sets",
        "training_tasks": 13, "holdout_tasks": 4, "parameter_updates": updates,
        "hidden_size": hidden_size, "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "protected_verifier_feedback_used": False, "reference_fragment_used": False,
    })
    dump(output / "runtime.json", {
        "gpu": torch.cuda.get_device_name(), "torch_version": torch.__version__,
        "transformers_version": transformers.__version__, "parameter_updates": updates,
        "cuda_peak_allocated_bytes": torch.cuda.max_memory_allocated(),
        "cuda_peak_reserved_bytes": torch.cuda.max_memory_reserved(),
        "elapsed_seconds": time.monotonic() - started,
    })
    dump(output / "summary.json", {
        "training_tasks": 13, "holdout_tasks": 4, "parameter_updates": updates,
        "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "official_tasks_ranked": len(official),
        "official_candidates_ranked": sum(len(rows) for rows in official.values()),
        "representation": "frozen-parent pooled hidden-state linear listwise action head",
        "learning_signal": "task-normalized listwise cross-entropy over complete candidate sets",
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "tlaps_executed": False, "proof_or_quality_claim": False, "gate_claim": False,
        "loss_first_last": [losses[0], losses[-1]], "head_sha256": sha(head_path.read_bytes()),
        "elapsed_seconds": time.monotonic() - started,
    })
    print(json.dumps({"updates": updates, "holdout_rank1_certified": holdout_rank1,
                      "official_tasks_ranked": len(official)}, indent=2), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-packet", type=Path, required=True)
    parser.add_argument("--official-packet", type=Path, required=True)
    parser.add_argument("--labels", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--updates", type=int, default=16)
    parser.add_argument("--lr", type=float, default=0.02)
    args = parser.parse_args()
    if not 1 <= args.updates <= BUDGET["max_updates"] or not 0 < args.lr <= 0.1:
        parser.error("bounded action-head budget required")
    os.environ.update(HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1", TOKENIZERS_PARALLELISM="false")
    worker(args)


if __name__ == "__main__":
    main()
