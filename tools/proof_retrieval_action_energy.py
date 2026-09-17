#!/usr/bin/env python3
"""Fit an answer-free retrieval-conditioned symbolic proof-action energy.

This is a CPU diagnostic for a renderer-owned prover interface.  A safe index
contains only abstract shapes of previously proved obligations; it never
contains proof bodies, fact names, modules, or successful candidates.  The
model ranks a frozen finite set of symbolic actions.  The renderer and strict
TLAPS own all proof semantics, so this experiment has no free-generation,
repair, reward, reference, or protected-row path.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import time
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools.proof_task_context_energy import (
    HOLDOUT_IDS,
    PACKET_IDS,
    candidate_features,
    goal_text,
    task_features,
)
from tools.proof_verifier_scaffold import obligation_shape, query

SOURCE_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PACKET_SHA256 = "c9784d4da893464f23bc27610c5f7aed64c44bf5406a7ec33f27637ad0d7394f"
INDEX_PATH = Path("results/runs/proof-verifier-scaffold-20260916-v3/index.jsonl")
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}
SAFE_AUDIT_FLAGS = {
    "generated_feedback", "reference_fragment_exported", "reference_fragment_used",
    "successful_candidates_exported", "proof_bodies_exported", "tlaps_executed",
    "training_executed", "parameter_updates", "proof_or_quality_claim",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def reject_forbidden(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS or (
                    key in SAFE_AUDIT_FLAGS and child not in (False, 0)):
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_forbidden(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_forbidden(child, f"{path}[{index}]")


def load_safe_tasks(source_manifest: Path, packet_path: Path):
    source_bytes = source_manifest.read_bytes()
    packet_bytes = packet_path.read_bytes()
    if sha(source_bytes) != SOURCE_SHA256:
        raise ValueError("source manifest hash mismatch")
    if sha(packet_bytes) != PACKET_SHA256:
        raise ValueError("training packet hash mismatch")
    packet = json.loads(packet_bytes)
    reject_forbidden(packet)
    if packet.get("packet_kind") != "answer_free_multistep_symbolic_action_coverage":
        raise ValueError("unexpected packet kind")
    rows = packet.get("rows", [])
    if packet.get("denominator") != 17 or len(rows) != 17:
        raise ValueError("fixed 17-row denominator required")
    if {row.get("id") for row in rows} != PACKET_IDS:
        raise ValueError("training membership mismatch")
    source = json.loads(source_bytes)
    # Project immutable scaffold fields only.  The archival manifest contains
    # answer-bearing fields for other workflows; none are accessed here.
    tasks = {}
    for raw in source.get("tasks", []):
        if raw.get("id") in PACKET_IDS:
            tasks[raw["id"]] = {
                key: raw[key] for key in
                ("id", "split", "prefix", "suffix", "theorem_name", "dependencies")
            }
    if set(tasks) != PACKET_IDS:
        raise ValueError("source task projection mismatch")
    by_id = {}
    for row in rows:
        if row.get("id") in by_id or row.get("split") != "train":
            raise ValueError("duplicate or non-train packet row")
        if not row.get("prompt") or not row.get("candidate_proposals"):
            raise ValueError("missing prompt or candidate proposals")
        if row.get("prompt_sha256") != sha(row["prompt"].encode()):
            raise ValueError("prompt hash mismatch")
        by_id[row["id"]] = row
    return tasks, by_id, packet_bytes


def retrieval_features(index: list[dict], task: dict) -> tuple[str, ...]:
    goal = goal_text(task)
    hits = query(index, goal, k=8)
    features = []
    shape = obligation_shape(goal)["features"]
    for key in ("length", "quantifiers", "conjunctions", "disjunctions",
                "implications", "membership", "temporal", "primed", "unchanged"):
        value = shape[key]
        bucket = value if key == "length" else min(int(value), 4)
        features.append(f"query:{key}:{bucket}")
    features.append(f"retrieval:count:{min(len(hits), 8)}")
    for rank, hit in enumerate(hits[:4], 1):
        score_bucket = min(20, int(float(hit["score"]) * 20.0))
        features.extend((f"retrieval:{rank}:score:{score_bucket}",
                         f"retrieval:{rank}:backend:{hit['backend']}",
                         f"retrieval:{rank}:kind:{hit['theorem_kind']}",
                         f"retrieval:{rank}:source:{hit['source_kind']}",
                         f"retrieval:{rank}:length:{hit['features']['length']}",
                         f"retrieval:{rank}:temporal:{min(int(hit['features']['temporal']), 4)}",
                         f"retrieval:{rank}:quantifiers:{min(int(hit['features']['quantifiers']), 4)}"))
    return tuple(sorted(features))


def joint_features(task: dict, candidate: str, retrieved: tuple[str, ...]) -> tuple[str, ...]:
    task_tokens = tuple(task_features(task))
    action_tokens = tuple(candidate_features(candidate))
    # Pairing retrieval evidence with candidate syntax is the new signal; the
    # old task-only energy is retained only as a deliberately explicit control.
    base = list(task_tokens) + list(action_tokens) + list(retrieved)
    base.extend("joint:" + a + "|" + b for a in task_tokens for b in action_tokens)
    base.extend("retrieved_action:" + a + "|" + b for a in retrieved for b in action_tokens)
    return tuple(base)


def fit_logistic(examples: list[tuple[tuple[str, ...], int]], *, epochs=2400,
                 learning_rate=0.08, l2=0.15):
    vocabulary = sorted({token for tokens, _ in examples for token in tokens})
    weights = {token: 0.0 for token in vocabulary}
    bias = 0.0
    for _ in range(epochs):
        gradients = {token: l2 * weight for token, weight in weights.items()}
        bias_gradient = l2 * bias
        for tokens, target in examples:
            value = max(-30.0, min(30.0, bias + sum(weights[token] for token in tokens)))
            probability = 1.0 / (1.0 + math.exp(-value))
            delta = probability - target
            bias_gradient += delta
            for token in tokens:
                gradients[token] += delta
        scale = learning_rate / max(1, len(examples))
        bias -= scale * bias_gradient
        for token in weights:
            weights[token] -= scale * gradients[token]
    return weights, bias


def energy(weights, bias, tokens):
    return bias + sum(weights.get(token, 0.0) for token in tokens)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--index", type=Path, default=INDEX_PATH)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if not 1 <= args.timeout <= 15 or not 60 <= args.seconds <= 900:
        parser.error("bounded strict-TLAPS budget required")
    tasks, rows, packet_bytes = load_safe_tasks(args.source_manifest, args.packet)
    index_bytes = args.index.read_bytes()
    index = []
    for line in index_bytes.splitlines():
        if line.strip():
            item = json.loads(line)
            reject_forbidden(item, "safe_index")
            index.append(item)
    if len(index) < 100:
        raise ValueError("safe retrieval index unexpectedly small")
    retrieved = {task_id: retrieval_features(index, tasks[task_id]) for task_id in rows}
    labels = {}
    checks = []
    started = time.monotonic()
    for task_id in sorted(rows):
        task, row = tasks[task_id], rows[task_id]
        for candidate_index, candidate in enumerate(row["candidate_proposals"]):
            if time.monotonic() + args.timeout > started + args.seconds:
                raise TimeoutError("strict TLAPS budget exhausted")
            result = certify_fragment(
                task["prefix"], candidate, task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                work_root=args.output / "checks" / task_id / str(candidate_index),
                timeout=args.timeout,
            )
            certified = bool(result["certified"])
            labels[(task_id, candidate_index)] = int(certified)
            checks.append({
                "task": task_id, "candidate_index": candidate_index,
                "candidate": candidate, "certified": certified,
                "status": result["status"], "proved": result["proved"],
                "total": result["total"], "seconds": result["seconds"],
                "sha256": result["sha256"],
            })
    fit_ids = sorted(PACKET_IDS - HOLDOUT_IDS)
    examples = []
    for task_id in fit_ids:
        row = rows[task_id]
        for index_number, candidate in enumerate(row["candidate_proposals"]):
            examples.append((joint_features(tasks[task_id], candidate, retrieved[task_id]),
                             labels[(task_id, index_number)]))
    weights, bias = fit_logistic(examples)
    rankings = {}
    for task_id in sorted(rows):
        row = rows[task_id]
        ranked = []
        for index_number, candidate in enumerate(row["candidate_proposals"]):
            tokens = joint_features(tasks[task_id], candidate, retrieved[task_id])
            ranked.append({
                "candidate_index": index_number, "candidate": candidate,
                "energy": energy(weights, bias, tokens),
                "certified": bool(labels[(task_id, index_number)]),
            })
        rankings[task_id] = sorted(
            ranked, key=lambda value: (-value["energy"], value["candidate_index"]))
    holdout = {task_id: ranking for task_id, ranking in rankings.items()
               if task_id in HOLDOUT_IDS}
    holdout_rank1 = sum(int(values and values[0]["certified"])
                        for values in holdout.values())
    holdout_solvable = sum(int(any(value["certified"] for value in values))
                           for values in holdout.values())
    # The strict checker creates its owned work-root before the final ledgers;
    # tolerate that expected directory so a completed diagnostic can seal it.
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "strict-labels.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in checks))
    dump(args.output / "rankings.json", rankings)
    dump(args.output / "holdout-rankings.json", holdout)
    dump(args.output / "retrieval-features.json", retrieved)
    dump(args.output / "model.json", {
        "feature": "safe verifier-obligation retrieval x symbolic-action energy",
        "source_manifest_sha256": sha(args.source_manifest.read_bytes()),
        "packet_sha256": sha(packet_bytes), "index_sha256": sha(index_bytes),
        "index_entries": len(index), "training_tasks": fit_ids,
        "holdout_tasks": sorted(HOLDOUT_IDS), "training_examples": len(examples),
        "bias": bias, "weights": weights,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "official_packet_used": False,
        "quality_claim": False, "gate_claim": False,
    })
    dump(args.output / "summary.json", {
        "kind": "proof_retrieval_action_energy_v1",
        "strict_label_records": len(checks),
        "train_positive_labels": sum(labels.values()),
        "fit_tasks": len(fit_ids), "holdout_tasks": len(HOLDOUT_IDS),
        "holdout_rank1": holdout_rank1, "holdout_solvable": holdout_solvable,
        "denominator_fixed": True, "checker": "fresh strict uncached TLAPS",
        "safe_index_entries": len(index), "training_executed": False,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "quality_claim": False, "gate_claim": False,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    })
    print(json.dumps({
        "holdout_rank1": holdout_rank1, "holdout_solvable": holdout_solvable,
        "strict_label_records": len(checks), "safe_index_entries": len(index),
        "output": str(args.output),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
