#!/usr/bin/env python3
"""Fit a compositional utility model over answer-free proof-action transitions.

This is a CPU-only research diagnostic.  It expands the frozen four-action
interface with bounded visible-statement proposals, independently labels the
expanded actions with strict TLAPS, then fits an additive transition model on
the 17 non-protected training tasks.  The model scores an action from its
solver-to-fact/definition transitions and atom order; it does not consume a
reference fragment, protected verifier feedback, reward, repair or official
test outcome.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals

TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}
HOLDOUT_IDS = {
    "crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof",
    "crdt-sum-zero-proof",
}
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def reject_keys(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing key: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def atom_sequence(candidate: str) -> tuple[str, ...]:
    """Return the ordered transition atoms without normalizing candidate IDs."""
    if candidate == "OBVIOUS":
        return ("solver:obvious",)
    if candidate.startswith("BY SMT DEF "):
        solver = "solver:smt"
        body = candidate[len("BY SMT DEF "):]
    elif candidate.startswith("BY DEF "):
        solver = "solver:def"
        body = candidate[len("BY DEF "):]
    elif candidate.startswith("BY SMT, "):
        solver = "solver:smt_facts"
        body = candidate[len("BY SMT, "):]
    elif candidate.startswith("BY "):
        solver = "solver:other"
        body = candidate[len("BY "):]
    else:
        raise ValueError("unsupported action syntax")
    atoms = tuple(item.strip() for item in body.split(",") if item.strip())
    transitions = [solver, f"transition:{solver}->atoms", f"length:{min(len(atoms), 16)}"]
    previous = None
    for position, atom in enumerate(atoms):
        transitions.append(f"atom:{atom}")
        transitions.append(f"position:{position}:{atom}")
        if previous is not None:
            transitions.append(f"edge:{previous}->{atom}")
        previous = atom
    return tuple(transitions)


def fit_logistic(examples: list[tuple[tuple[str, ...], int]],
                 epochs: int = 3000, learning_rate: float = 0.08,
                 l2: float = 0.1) -> tuple[dict[str, float], float]:
    vocabulary = sorted({token for tokens, _ in examples for token in tokens})
    weights = {token: 0.0 for token in vocabulary}
    bias = 0.0
    for _ in range(epochs):
        gradients = {token: l2 * value for token, value in weights.items()}
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


def utility(weights: dict[str, float], bias: float, candidate: str) -> float:
    return bias + sum(weights.get(token, 0.0) for token in atom_sequence(candidate))


def task_candidates(task: dict) -> list[str]:
    dependencies = tuple(Path(path) for path in task.get("dependencies", []))
    expected = task.get("dependency_sha256", {})
    for dependency in dependencies:
        if expected and sha(dependency.read_bytes()) != expected.get(str(dependency)):
            raise ValueError(f"dependency hash mismatch: {task['id']}:{dependency}")
    dependency_texts = [path.read_text() for path in dependencies]
    library_paths = libraries(task["prefix"], dependency_texts, TLA_LIBRARY.split(":"))
    candidates_found, _ = proposals(
        task["prefix"], task["theorem_name"], task.get("target_goal", f"THEOREM {task['theorem_name']}"),
        dependency_texts, [path.read_text() for path in library_paths])
    candidates_found = list(dict.fromkeys(candidates_found))
    if not 1 <= len(candidates_found) <= 32:
        raise ValueError(f"bounded proposal width violated: {task['id']}")
    if any(not candidate.startswith("BY ") or "AXIOM" in candidate or "OMITTED" in candidate
           for candidate in candidates_found):
        raise ValueError(f"unsafe proposal: {task['id']}")
    return candidates_found


def prepare_tasks(manifest: dict) -> dict[str, dict]:
    tasks = {task["id"]: task for task in manifest.get("tasks", [])}
    if set(tasks) != TRAIN_IDS | HOLDOUT_IDS or any(
            tasks[task_id].get("split") not in {"train", "development"}
            for task_id in tasks):
        raise ValueError("exact 17/4 task split required")
    if {tasks[task_id].get("split") for task_id in TRAIN_IDS} != {"train"}:
        raise ValueError("training split mismatch")
    if {tasks[task_id].get("split") for task_id in HOLDOUT_IDS} != {"development"}:
        raise ValueError("holdout split mismatch")
    return tasks


def rank(task: dict, candidates: list[str], weights: dict[str, float], bias: float) -> list[dict]:
    rows = [{"candidate_index": index, "candidate": candidate,
             "transition_utility": utility(weights, bias, candidate)}
            for index, candidate in enumerate(candidates)]
    return sorted(rows, key=lambda row: (-row["transition_utility"], row["candidate_index"]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 10 or not 30 <= args.seconds <= 900:
        parser.error("bounded timeout/seconds required")
    if args.output.exists():
        raise FileExistsError(args.output)
    manifest_bytes = args.manifest.read_bytes()
    if sha(manifest_bytes) != args.expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(manifest_bytes)
    # Check only structural metadata; do not traverse or export reference fields.
    tasks = prepare_tasks(manifest)
    args.output.mkdir(parents=True)
    candidates_by_task = {task_id: task_candidates(task) for task_id, task in tasks.items()}
    (args.output / "candidates.json").write_text(json.dumps({
        task_id: candidates_by_task[task_id] for task_id in sorted(candidates_by_task)
    }, indent=2) + "\n")
    labels_path = args.output / "strict-labels.jsonl"
    started = time.monotonic()
    examples: list[tuple[tuple[str, ...], int]] = []
    holdout_records: list[dict] = []
    train_records: list[dict] = []
    with labels_path.open("x") as stream:
        for task_id in sorted(tasks):
            task = tasks[task_id]
            for candidate_index, candidate in enumerate(candidates_by_task[task_id]):
                if time.monotonic() + args.timeout > started + args.seconds:
                    raise TimeoutError("strict labeling budget exhausted before complete 21-task coverage")
                result = certify_fragment(
                    task["prefix"], candidate, task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                    work_root=args.output / "checks" / task_id / str(candidate_index),
                    timeout=args.timeout)
                record = {
                    "task": task_id, "candidate_index": candidate_index,
                    "candidate": candidate, "certified": bool(result["certified"]),
                    "status": result["status"], "proved": result["proved"],
                    "total": result["total"], "seconds": result["seconds"],
                    "sha256": result["sha256"],
                }
                stream.write(json.dumps(record) + "\n")
                stream.flush()
                if task_id in TRAIN_IDS:
                    train_records.append(record)
                else:
                    holdout_records.append(record)
                if task_id in TRAIN_IDS:
                    examples.append((atom_sequence(candidate), int(record["certified"])))
    weights, bias = fit_logistic(examples)
    train_task_rows = {task_id: rank(tasks[task_id], candidates_by_task[task_id], weights, bias)
                       for task_id in sorted(TRAIN_IDS)}
    holdout_rankings = {task_id: rank(tasks[task_id], candidates_by_task[task_id], weights, bias)
                        for task_id in sorted(HOLDOUT_IDS)}
    label_map = {(row["task"], row["candidate_index"]): row["certified"]
                 for row in train_records + holdout_records}
    holdout_rank1 = sum(label_map[(task_id, rows[0]["candidate_index"])] for task_id, rows in holdout_rankings.items())
    holdout_solvable = sum(any(label_map[(task_id, row["candidate_index"])] for row in rows)
                           for task_id, rows in holdout_rankings.items())
    (args.output / "model.json").write_text(json.dumps({
        "feature": "ordered solver/atom transition utility",
        "weights": weights, "bias": bias,
        "training_tasks": sorted(TRAIN_IDS), "holdout_tasks": sorted(HOLDOUT_IDS),
        "training_examples": len(examples), "manifest_sha256": sha(manifest_bytes),
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
    }, indent=2) + "\n")
    (args.output / "holdout-rankings.json").write_text(json.dumps(holdout_rankings, indent=2) + "\n")
    (args.output / "summary.json").write_text(json.dumps({
        "train_tasks": len(TRAIN_IDS), "holdout_tasks": len(HOLDOUT_IDS),
        "expanded_candidate_min": min(map(len, candidates_by_task.values())),
        "expanded_candidate_max": max(map(len, candidates_by_task.values())),
        "strict_label_records": len(train_records) + len(holdout_records),
        "train_positive_labels": sum(row["certified"] for row in train_records),
        "holdout_positive_labels": sum(row["certified"] for row in holdout_records),
        "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
        "official_packet_used": False,
        "parameter_updates": 0,
        "quality_claim": False, "gate_claim": False,
        "manifest_sha256": sha(manifest_bytes),
        "elapsed_seconds": time.monotonic() - started,
    }, indent=2) + "\n")
    print(json.dumps({
        "complete": True, "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "strict_label_records": len(train_records) + len(holdout_records),
        "expanded_candidate_max": max(map(len, candidates_by_task.values())),
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
    }, indent=2))


if __name__ == "__main__":
    main()
