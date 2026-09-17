#!/usr/bin/env python3
"""Rank symbolic proof actions with answer-free retrieval prototypes.

This branch is deliberately not a scalar classifier or pairwise orderer.  It
stores only visible-prompt token signatures of non-protected tasks whose
candidate was independently certified, then scores a new candidate by prompt
similarity and candidate-family support.  The fixed holdout is scored after
prototype construction; the official packet is prediction-only.
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


def visible_prompt(prompt: str) -> str:
    return prompt.split("Visible statement-only context", 1)[-1]


def tokens(prompt: str) -> set[str]:
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_]{2,}", visible_prompt(prompt).lower()))


def family(candidate: str) -> str:
    if candidate == "OBVIOUS":
        return "obvious"
    if candidate.startswith("BY SMT DEF "):
        return "smt_def"
    if candidate.startswith("BY DEF "):
        return "def"
    if candidate == "BY SMT":
        return "smt"
    if candidate.startswith("BY SMT"):
        return "smt_context"
    return "other"


def cosine(left: set[str], right: set[str]) -> float:
    if not left or not right:
        return 0.0
    return len(left & right) / math.sqrt(len(left) * len(right))


def build_prototypes(train_rows: dict[str, dict], labels: dict[str, dict[int, int]]):
    prototypes = []
    family_counts: dict[str, int] = {}
    for task_id in sorted(TRAIN_IDS - HOLDOUT_IDS):
        row = train_rows[task_id]
        for index, label in labels[task_id].items():
            if not label:
                continue
            kind = family(row["candidate_proposals"][index])
            family_counts[kind] = family_counts.get(kind, 0) + 1
            prototypes.append({
                "task_id": task_id,
                "family": kind,
                "tokens": sorted(tokens(row["prompt"])),
            })
    if not prototypes:
        raise ValueError("no certified non-protected prototypes")
    return prototypes, family_counts


def load_labels(checks_path: Path, train_rows: dict[str, dict]) -> dict[str, dict[int, int]]:
    labels: dict[str, dict[int, int]] = {task_id: {} for task_id in TRAIN_IDS}
    for line in checks_path.read_text().splitlines():
        record = json.loads(line)
        task_id = record.get("task")
        index = record.get("candidate_index")
        if task_id not in TRAIN_IDS or not isinstance(index, int):
            raise ValueError("label outside frozen non-protected set")
        row = train_rows[task_id]
        if not 0 <= index < len(row["candidate_proposals"]):
            raise ValueError("label index outside packet")
        if record.get("candidate") != row["candidate_proposals"][index]:
            raise ValueError("label candidate mismatch")
        labels[task_id][index] = int(bool(record.get("certified")))
    if sum(len(values) for values in labels.values()) < 17:
        raise ValueError("insufficient strict labels")
    return labels


def candidate_score(candidate: str, prompt: str, prototypes, family_counts):
    kind = family(candidate)
    current = tokens(prompt)
    same_family = [p for p in prototypes if p["family"] == kind]
    similarities = [cosine(current, set(p["tokens"])) for p in same_family]
    similarity = max(similarities, default=0.0)
    support = family_counts.get(kind, 0) / max(1, len(prototypes))
    # Support is a small prior; retrieval similarity remains the primary signal.
    return 0.8 * similarity + 0.2 * support


def rank_rows(rows, prototypes, family_counts):
    rankings = {}
    for row in rows:
        scored = []
        for index, candidate in enumerate(row["candidate_proposals"]):
            value = candidate_score(candidate, row["prompt"], prototypes, family_counts)
            scored.append({
                "candidate_index": index,
                "candidate": candidate,
                "mean_logp": value,
                "retrieval_score": value,
            })
        rankings[row["id"]] = sorted(
            scored, key=lambda item: (-item["retrieval_score"], item["candidate_index"]))
    return rankings


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
        raise ValueError("unexpected training packet")
    if (official_packet.get("packet_kind") != "answer_free_official_symbolic_candidate_ranking" or
            official_packet.get("denominator") != 119):
        raise ValueError("unexpected official packet")
    train_rows = {row["id"]: row for row in train_packet["rows"]}
    labels = load_labels(args.train_checks, train_rows)
    prototypes, family_counts = build_prototypes(train_rows, labels)
    holdout = rank_rows([train_rows[task_id] for task_id in sorted(HOLDOUT_IDS)], prototypes, family_counts)
    official = rank_rows(official_packet["rows"], prototypes, family_counts)
    holdout_rank1 = sum(
        labels[task_id].get(rows[0]["candidate_index"]) == 1
        for task_id, rows in holdout.items())
    holdout_solvable = sum(
        any(labels[task_id].get(row["candidate_index"]) == 1 for row in rows)
        for task_id, rows in holdout.items())
    args.output.mkdir(parents=True)
    (args.output / "prototypes.json").write_text(json.dumps({
        "prototypes": prototypes,
        "family_counts": family_counts,
        "train_packet_sha256": args.expected_train_packet_sha256,
        "train_checks_sha256": args.expected_train_checks_sha256,
        "holdout_task_ids": sorted(HOLDOUT_IDS),
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
    }, indent=2) + "\n")
    (args.output / "holdout-rankings.json").write_text(json.dumps(holdout, indent=2) + "\n")
    (args.output / "rankings.json").write_text(json.dumps(official, indent=2) + "\n")
    (args.output / "config.json").write_text(json.dumps({
        "packet_sha256": args.expected_official_packet_sha256,
        "checkpoint_sha256": "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511",
        "selection_method": "non-protected answer-free retrieval prototypes by prompt signature and candidate family",
        "training_checks_sha256": args.expected_train_checks_sha256,
        "prototype_count": len(prototypes),
        "holdout_tasks": len(HOLDOUT_IDS),
        "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
    }, indent=2) + "\n")
    (args.output / "summary.json").write_text(json.dumps({
        "training_tasks": len(TRAIN_IDS - HOLDOUT_IDS),
        "prototype_count": len(prototypes),
        "holdout_tasks": len(HOLDOUT_IDS),
        "holdout_rank1_certified": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "official_tasks_ranked": len(official),
        "official_candidates_ranked": sum(len(rows) for rows in official.values()),
        "representation": "retrieval prototypes over visible prompt tokens and candidate families",
        "learning_signal": "certified non-protected prototypes only",
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
        "training_executed": False,
        "proof_or_quality_claim": False,
        "gate_claim": False,
    }, indent=2) + "\n")
    print(json.dumps({
        "prototype_count": len(prototypes),
        "holdout_rank1_certified": holdout_rank1,
        "official_tasks_ranked": len(official),
    }, indent=2))


if __name__ == "__main__":
    main()
