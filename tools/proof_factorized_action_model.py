#!/usr/bin/env python3
"""Train an answer-separated factorized action selector on non-protected rows.

Only the frozen 17-row packet and its strict-TLAPS labels are used for fitting.
The protected official packet is used only to emit predictions; its verifier
outcomes are never read by this tool.
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
FEATURE_NAMES = (
    "bias", "obvious", "smt", "def", "smt_def", "def_count",
    "identifier_count", "candidate_chars", "visible_overlap", "set_extensionality",
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


def features(candidate: str, prompt: str) -> list[float]:
    identifiers = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", candidate))
    visible = visible_names(prompt)
    defs = candidate.split(" DEF ", 1)[1].split(", ") if " DEF " in candidate else []
    return [
        1.0,
        float(candidate == "OBVIOUS"),
        float("SMT" in candidate),
        float(" DEF " in candidate),
        float(candidate.startswith("BY SMT DEF ")),
        min(len(defs), 32) / 32.0,
        min(len(identifiers), 64) / 64.0,
        min(len(candidate), 512) / 512.0,
        min(len(identifiers & visible), 16) / 16.0,
        float("SetExtensionality" in identifiers),
    ]


def sigmoid(value: float) -> float:
    value = max(-30.0, min(30.0, value))
    return 1.0 / (1.0 + math.exp(-value))


def fit(examples: list[tuple[list[float], int]], epochs: int = 4000,
        learning_rate: float = 0.04, l2: float = 0.05) -> list[float]:
    weights = [0.0] * len(FEATURE_NAMES)
    for _ in range(epochs):
        gradient = [l2 * weight for weight in weights]
        for vector, label in examples:
            probability = sigmoid(sum(w * x for w, x in zip(weights, vector)))
            for index, value in enumerate(vector):
                gradient[index] += (probability - label) * value
        scale = learning_rate / max(1, len(examples))
        for index in range(len(weights)):
            weights[index] -= scale * gradient[index]
    return weights


def score(weights: list[float], vector: list[float]) -> float:
    return sum(weight * value for weight, value in zip(weights, vector))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--train-packet", type=Path, required=True)
    parser.add_argument("--train-checks", type=Path, required=True)
    parser.add_argument("--official-packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-train-packet-sha256", required=True)
    parser.add_argument("--expected-official-packet-sha256", required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    train_packet_bytes = args.train_packet.read_bytes()
    official_packet_bytes = args.official_packet.read_bytes()
    if sha(train_packet_bytes) != args.expected_train_packet_sha256:
        raise ValueError("train packet hash mismatch")
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
    examples = []
    observed = 0
    positives = 0
    for raw in args.train_checks.read_text().splitlines():
        record = json.loads(raw)
        task_id = record.get("task")
        candidate_index = record.get("candidate_index")
        if task_id not in TRAIN_IDS or not isinstance(candidate_index, int):
            raise ValueError("training check outside frozen non-protected set")
        row = train_rows[task_id]
        if not 0 <= candidate_index < len(row["candidate_proposals"]):
            raise ValueError("training candidate index outside packet")
        candidate = row["candidate_proposals"][candidate_index]
        if record.get("candidate") != candidate:
            raise ValueError("training candidate mismatch")
        label = int(bool(record.get("certified")))
        examples.append((features(candidate, row["prompt"]), label))
        observed += 1
        positives += label
    if observed < 17 or positives == 0:
        raise ValueError("insufficient non-protected labels")
    weights = fit(examples)

    rankings = {}
    for row in official_packet["rows"]:
        scored = []
        for index, candidate in enumerate(row["candidate_proposals"]):
            scored.append({
                "candidate_index": index,
                "candidate": candidate,
                "mean_logp": score(weights, features(candidate, row["prompt"])),
                "factorized_score": score(weights, features(candidate, row["prompt"])),
            })
        rankings[row["id"]] = sorted(
            scored, key=lambda item: (-item["factorized_score"], item["candidate_index"]))

    args.output.mkdir(parents=True)
    (args.output / "model.json").write_text(json.dumps({
        "feature_names": FEATURE_NAMES,
        "weights": weights,
        "train_packet_sha256": args.expected_train_packet_sha256,
        "train_checks_sha256": sha(args.train_checks.read_bytes()),
        "protected_packet_used_for_training": False,
        "reference_fragment_used": False,
        "verifier_feedback_from_protected_set": False,
    }, indent=2) + "\n")
    (args.output / "rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.output / "config.json").write_text(json.dumps({
        "packet_sha256": args.expected_official_packet_sha256,
        "checkpoint_sha256": "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511",
        "selection_method": "non-protected TLAPS-trained factorized action features",
        "training_examples": observed,
        "positive_examples": positives,
        "parameter_updates": 4000,
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
    }, indent=2) + "\n")
    (args.output / "summary.json").write_text(json.dumps({
        "training_tasks": 17,
        "training_examples": observed,
        "positive_examples": positives,
        "official_tasks_ranked": len(rankings),
        "official_candidates_ranked": sum(len(rows) for rows in rankings.values()),
        "representation": "backend/fact-count/visible-overlap factorized action features",
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
        "training_executed": True,
        "parameter_updates": 4000,
        "proof_or_quality_claim": False,
        "gate_claim": False,
    }, indent=2) + "\n")
    print(json.dumps({"training_examples": observed, "positive_examples": positives,
                      "official_tasks_ranked": len(rankings)}, indent=2))


if __name__ == "__main__":
    main()
