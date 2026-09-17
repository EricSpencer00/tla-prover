#!/usr/bin/env python3
"""Fit an answer-free within-task pairwise action ranker.

The ranker learns only from strict-TLAPS labels in the frozen non-protected
packet.  It forms positive-vs-negative pairs within each training task and
uses task-context interactions, rather than absolute certification labels or
candidate indices.  A fixed four-task non-protected holdout is scored only
after fitting; the protected official packet is prediction-only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import re


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
FEATURE_NAMES = (
    "bias", "candidate_obvious", "candidate_smt", "candidate_def",
    "candidate_smt_def", "candidate_def_count", "candidate_identifier_count",
    "candidate_chars", "candidate_visible_overlap", "candidate_set_extensionality",
    "prompt_visible_name_count", "prompt_has_init", "prompt_has_next",
    "prompt_has_typeok", "prompt_chars", "candidate_overlap_ratio",
    "smt_def_x_prompt_next", "def_x_prompt_init", "obvious_x_prompt_init",
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def reject_keys(value, path="document"):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def visible_names(prompt: str) -> set[str]:
    context = prompt.split("Visible statement-only context", 1)[-1]
    return set(re.findall(r"(?m)^([A-Za-z_][A-Za-z0-9_]*)\s*==", context))


def feature_vector(candidate: str, prompt: str) -> list[float]:
    identifiers = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", candidate))
    visible = visible_names(prompt)
    defs = candidate.split(" DEF ", 1)[1].split(", ") if " DEF " in candidate else []
    prompt_lower = prompt.lower()
    prompt_next = float(bool(re.search(r"\bNext\b", prompt)))
    prompt_init = float(bool(re.search(r"\bInit\b", prompt)))
    prompt_typeok = float(bool(re.search(r"\bTypeOK\b", prompt)))
    overlap = len(identifiers & visible)
    candidate_overlap_ratio = overlap / max(1, len(identifiers))
    smt_def = float(candidate.startswith("BY SMT DEF "))
    has_def = float(" DEF " in candidate)
    obvious = float(candidate == "OBVIOUS")
    return [
        1.0,
        obvious,
        float("SMT" in candidate),
        has_def,
        smt_def,
        min(len(defs), 32) / 32.0,
        min(len(identifiers), 64) / 64.0,
        min(len(candidate), 512) / 512.0,
        min(overlap, 16) / 16.0,
        float("SetExtensionality" in identifiers),
        min(len(visible), 64) / 64.0,
        prompt_init,
        prompt_next,
        prompt_typeok,
        min(len(prompt), 4096) / 4096.0,
        candidate_overlap_ratio,
        smt_def * prompt_next,
        has_def * prompt_init,
        obvious * prompt_init,
    ]


def sigmoid(value: float) -> float:
    value = max(-30.0, min(30.0, value))
    return 1.0 / (1.0 + math.exp(-value))


def fit_pairwise(pairs: list[list[float]], epochs: int = 5000,
                 learning_rate: float = 0.04, l2: float = 0.05) -> list[float]:
    weights = [0.0] * len(FEATURE_NAMES)
    for _ in range(epochs):
        gradient = [l2 * weight for weight in weights]
        for difference in pairs:
            probability = sigmoid(sum(w * x for w, x in zip(weights, difference)))
            for index, value in enumerate(difference):
                gradient[index] += (probability - 1.0) * value
        scale = learning_rate / max(1, len(pairs))
        for index in range(len(weights)):
            weights[index] -= scale * gradient[index]
    return weights


def score(weights: list[float], vector: list[float]) -> float:
    return sum(weight * value for weight, value in zip(weights, vector))


def load_labels(checks_path: Path, train_rows: dict[str, dict]) -> dict[str, dict[int, int]]:
    labels: dict[str, dict[int, int]] = {task_id: {} for task_id in TRAIN_IDS}
    for line in checks_path.read_text().splitlines():
        record = json.loads(line)
        task_id = record.get("task")
        candidate_index = record.get("candidate_index")
        if task_id not in TRAIN_IDS or not isinstance(candidate_index, int):
            raise ValueError("label outside frozen non-protected set")
        row = train_rows[task_id]
        if not 0 <= candidate_index < len(row["candidate_proposals"]):
            raise ValueError("label candidate index outside packet")
        if record.get("candidate") != row["candidate_proposals"][candidate_index]:
            raise ValueError("label candidate mismatch")
        labels[task_id][candidate_index] = int(bool(record.get("certified")))
    if sum(len(values) for values in labels.values()) < 17:
        raise ValueError("insufficient strict labels")
    return labels


def rank_rows(rows: list[dict], weights: list[float]) -> dict[str, list[dict]]:
    result = {}
    for row in rows:
        scored = []
        for index, candidate in enumerate(row["candidate_proposals"]):
            vector = feature_vector(candidate, row["prompt"])
            value = score(weights, vector)
            scored.append({
                "candidate_index": index,
                "candidate": candidate,
                "mean_logp": value,
                "pairwise_score": value,
            })
        result[row["id"]] = sorted(
            scored, key=lambda item: (-item["pairwise_score"], item["candidate_index"]))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-packet", type=Path, required=True)
    parser.add_argument("--train-checks", type=Path, required=True)
    parser.add_argument("--official-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-train-packet-sha256", required=True)
    parser.add_argument("--expected-train-checks-sha256", required=True)
    parser.add_argument("--expected-official-packet-sha256", required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    train_packet_bytes = args.train_packet.read_bytes()
    checks_bytes = args.train_checks.read_bytes()
    official_packet_bytes = args.official_packet.read_bytes()
    if sha(train_packet_bytes) != args.expected_train_packet_sha256:
        raise ValueError("train packet hash mismatch")
    if sha(checks_bytes) != args.expected_train_checks_sha256:
        raise ValueError("train checks hash mismatch")
    if sha(official_packet_bytes) != args.expected_official_packet_sha256:
        raise ValueError("official packet hash mismatch")
    train_packet = json.loads(train_packet_bytes)
    official_packet = json.loads(official_packet_bytes)
    reject_keys(train_packet)
    reject_keys(official_packet)
    if (train_packet.get("packet_kind") != "answer_free_multistep_symbolic_action_coverage" or
            train_packet.get("denominator") != 17 or
            set(row["id"] for row in train_packet["rows"]) != TRAIN_IDS):
        raise ValueError("unexpected non-protected training packet")
    if (official_packet.get("packet_kind") != "answer_free_official_symbolic_candidate_ranking" or
            official_packet.get("denominator") != 119):
        raise ValueError("unexpected official packet")
    train_rows = {row["id"]: row for row in train_packet["rows"]}
    labels = load_labels(args.train_checks, train_rows)

    pairs = []
    pair_tasks = []
    for task_id in sorted(TRAIN_IDS - HOLDOUT_IDS):
        row = train_rows[task_id]
        positives = [index for index, label in labels[task_id].items() if label]
        negatives = [index for index, label in labels[task_id].items() if not label]
        for positive in positives:
            for negative in negatives:
                pairs.append([
                    good - bad for good, bad in zip(
                        feature_vector(row["candidate_proposals"][positive], row["prompt"]),
                        feature_vector(row["candidate_proposals"][negative], row["prompt"]),
                    )
                ])
                pair_tasks.append(task_id)
    if not pairs:
        raise ValueError("no within-task positive-vs-negative training pairs")
    weights = fit_pairwise(pairs)
    holdout_rankings = rank_rows(
        [train_rows[task_id] for task_id in sorted(HOLDOUT_IDS)], weights)
    official_rankings = rank_rows(official_packet["rows"], weights)

    holdout_rank1 = 0
    holdout_tasks_with_certified = 0
    for task_id, ranked in holdout_rankings.items():
        if any(labels[task_id].get(item["candidate_index"]) == 1 for item in ranked):
            holdout_tasks_with_certified += 1
        if labels[task_id].get(ranked[0]["candidate_index"]) == 1:
            holdout_rank1 += 1

    args.output.mkdir(parents=True)
    (args.output / "model.json").write_text(json.dumps({
        "feature_names": FEATURE_NAMES,
        "weights": weights,
        "train_packet_sha256": args.expected_train_packet_sha256,
        "train_checks_sha256": args.expected_train_checks_sha256,
        "training_task_ids": sorted(TRAIN_IDS - HOLDOUT_IDS),
        "holdout_task_ids": sorted(HOLDOUT_IDS),
        "pair_count": len(pairs),
        "pair_task_count": len(set(pair_tasks)),
        "protected_packet_used_for_training": False,
        "reference_fragment_used": False,
        "verifier_feedback_from_protected_set": False,
    }, indent=2) + "\n")
    (args.output / "rankings.json").write_text(json.dumps(official_rankings, indent=2) + "\n")
    (args.output / "holdout-rankings.json").write_text(
        json.dumps(holdout_rankings, indent=2) + "\n")
    (args.output / "config.json").write_text(json.dumps({
        "packet_sha256": args.expected_official_packet_sha256,
        "checkpoint_sha256": "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511",
        "selection_method": "non-protected within-task pairwise TLAPS labels with task-context features",
        "training_checks_sha256": args.expected_train_checks_sha256,
        "training_examples": len(pairs),
        "holdout_tasks": len(HOLDOUT_IDS),
        "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_tasks_with_certified,
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
    }, indent=2) + "\n")
    (args.output / "summary.json").write_text(json.dumps({
        "training_tasks": len(TRAIN_IDS - HOLDOUT_IDS),
        "holdout_tasks": len(HOLDOUT_IDS),
        "pair_count": len(pairs),
        "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_tasks_with_certified,
        "official_tasks_ranked": len(official_rankings),
        "official_candidates_ranked": sum(len(rows) for rows in official_rankings.values()),
        "representation": "candidate features plus task-context interactions",
        "learning_signal": "within-task positive-vs-negative pairwise logistic ranking",
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
        "training_executed": True,
        "proof_or_quality_claim": False,
        "gate_claim": False,
    }, indent=2) + "\n")
    print(json.dumps({
        "pair_count": len(pairs), "holdout_rank1_certified": holdout_rank1,
        "official_tasks_ranked": len(official_rankings),
    }, indent=2))


if __name__ == "__main__":
    main()
