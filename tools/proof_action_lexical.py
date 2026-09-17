#!/usr/bin/env python3
"""Rank frozen proof actions from answer-free theorem/goal lexical geometry.

This is a deliberately CPU-only breadth diagnostic.  Features are deterministic
hashed word and bigram counts from the theorem, goal, and visible-context lines
of the prompt only.  The sanitized TRAIN action signatures supervise a small
logistic head; candidate text and verifier outcomes never enter the fit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

_ADMISSION_PATH = Path(__file__).with_name("proof_action_signature_admission.py")
import importlib.util

_SPEC = importlib.util.spec_from_file_location("action_signature_admission_lexical", _ADMISSION_PATH)
if _SPEC is None or _SPEC.loader is None:
    raise ImportError(f"cannot load staged admission module: {_ADMISSION_PATH}")
_ADMISSION = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_ADMISSION)

HOLDOUT_IDS = _ADMISSION.HOLDOUT_IDS
LABELS_SHA256 = _ADMISSION.LABELS_SHA256
OFFICIAL_SHA256 = _ADMISSION.OFFICIAL_SHA256
PACKET_SHA256 = _ADMISSION.PACKET_SHA256
SLOTS = _ADMISSION.SLOTS
action_signature = _ADMISSION.action_signature
sha = _ADMISSION.sha
target_signatures = _ADMISSION.target_signatures

PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
DIMENSIONS = 4096
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|\\|->|<=>|=>|<=|>=|/=|[^\s]")


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def prompt_sections(prompt: str) -> dict[str, str]:
    lines = prompt.splitlines()
    values = {}
    for prefix, name in (("theorem=", "theorem"), ("goal=", "goal"),
                         ("Visible statement-only context", "context")):
        matches = [line[len(prefix):] if prefix.endswith("=") else line
                   for line in lines if line.startswith(prefix)]
        if len(matches) != 1:
            raise ValueError(f"expected one {name} prompt section")
        values[name] = matches[0]
    return values


def feature_index(namespace: str, token: str, dimension: int) -> int:
    digest = hashlib.blake2b(f"{namespace}\x00{token}".encode(), digest_size=8).digest()
    return int.from_bytes(digest, "big") % dimension


def features(prompt: str, dimension: int = DIMENSIONS) -> list[float]:
    sections = prompt_sections(prompt)
    vector = [0.0] * dimension
    for namespace, text in sections.items():
        tokens = [token.lower() for token in TOKEN_RE.findall(text)]
        for token in tokens:
            vector[feature_index(namespace, token, dimension)] += 1.0
        for left, right in zip(tokens, tokens[1:]):
            vector[feature_index(namespace + ":bigram", left + "\x00" + right, dimension)] += 0.5
    norm = math.sqrt(sum(value * value for value in vector))
    if norm == 0.0:
        raise ValueError("empty lexical feature vector")
    return [value / norm for value in vector]


def sigmoid(value: float) -> float:
    if value >= 0.0:
        z = math.exp(-value)
        return 1.0 / (1.0 + z)
    z = math.exp(value)
    return z / (1.0 + z)


def fit(rows: list[dict], targets: dict[str, tuple[int, ...]], updates: int,
        learning_rate: float, dimension: int):
    matrix = [features(row["prompt"], dimension) for row in rows]
    weights = [[0.0] * dimension for _ in SLOTS]
    bias = [0.0] * len(SLOTS)
    losses = []
    for _ in range(updates):
        gradients = [[0.0] * dimension for _ in SLOTS]
        bias_grad = [0.0] * len(SLOTS)
        loss = 0.0
        for vector, row in zip(matrix, rows):
            target = targets[row["id"]]
            for slot, expected in enumerate(target):
                logit = bias[slot] + sum(a * b for a, b in zip(weights[slot], vector))
                probability = sigmoid(logit)
                loss += -(expected * math.log(max(probability, 1e-12)) +
                           (1 - expected) * math.log(max(1 - probability, 1e-12)))
                error = probability - expected
                bias_grad[slot] += error
                for index, value in enumerate(vector):
                    gradients[slot][index] += error * value
        scale = 1.0 / (len(rows) * len(SLOTS))
        for slot in range(len(SLOTS)):
            bias[slot] -= learning_rate * bias_grad[slot] * scale
            for index in range(dimension):
                gradients[slot][index] *= scale
                gradients[slot][index] += 0.01 * weights[slot][index]
                weights[slot][index] -= learning_rate * gradients[slot][index]
        losses.append(loss * scale)
    return matrix, weights, bias, losses


def rank_rows(rows, weights, bias, dimension):
    rankings = {}
    probabilities = {}
    for row in rows:
        vector = features(row["prompt"], dimension)
        probs = [sigmoid(offset + sum(a * b for a, b in zip(weight, vector)))
                 for weight, offset in zip(weights, bias)]
        values = []
        for index, candidate in enumerate(row["candidate_proposals"]):
            signature = action_signature(candidate)
            distance = sum(abs(prob - bit) for prob, bit in zip(probs, signature))
            values.append({"candidate_index": index, "candidate": candidate,
                           "signature": signature, "signature_distance": distance})
        rankings[row["id"]] = sorted(values,
                                      key=lambda item: (item["signature_distance"],
                                                        item["candidate_index"]))
        probabilities[row["id"]] = dict(zip(SLOTS, probs))
    return rankings, probabilities


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--train-packet", required=True, type=Path)
    parser.add_argument("--official-packet", required=True, type=Path)
    parser.add_argument("--labels", required=True, type=Path)
    parser.add_argument("--parent-sha256", default=PARENT_SHA256)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--updates", type=int, default=96)
    parser.add_argument("--lr", type=float, default=0.4)
    parser.add_argument("--dimension", type=int, default=DIMENSIONS)
    args = parser.parse_args()
    if not 1 <= args.updates <= 256 or not 0 < args.lr <= 1.0:
        parser.error("bounded lexical fit contract required")
    train_bytes = args.train_packet.read_bytes()
    official_bytes = args.official_packet.read_bytes()
    labels_bytes = args.labels.read_bytes()
    if sha(train_bytes) != PACKET_SHA256 or sha(official_bytes) != OFFICIAL_SHA256:
        raise ValueError("packet hash mismatch")
    if sha(labels_bytes) != LABELS_SHA256:
        raise ValueError("label hash mismatch")
    packet, official, labels = _ADMISSION.load_packets(args.train_packet,
                                                        args.official_packet,
                                                        args.labels)
    targets = target_signatures(packet, labels)
    fit_rows = [row for row in packet["rows"] if row["id"] not in HOLDOUT_IDS
                and targets[row["id"]] is not None]
    holdout_rows = [row for row in packet["rows"] if row["id"] in HOLDOUT_IDS]
    if len(fit_rows) != 4 or len(holdout_rows) != 4:
        raise ValueError("frozen lexical fit/holdout contract mismatch")
    if args.parent_sha256 != PARENT_SHA256:
        raise ValueError("parent checkpoint hash mismatch")
    _, weights, bias, losses = fit(fit_rows, targets, args.updates, args.lr, args.dimension)
    holdout, holdout_probs = rank_rows(holdout_rows, weights, bias, args.dimension)
    official_rankings, official_probs = rank_rows(official["rows"], weights, bias, args.dimension)
    holdout_rank1 = sum(bool(ranking and ranking[0]["candidate_index"] in
                             {i for i, candidate in enumerate(row["candidate_proposals"])
                              if labels.get((row["id"], i), 0)})
                        for row in holdout_rows
                        for ranking in [holdout[row["id"]]])
    holdout_solvable = sum(any(labels.get((row["id"], item["candidate_index"]), 0)
                              for item in holdout[row["id"]]) for row in holdout_rows)
    output = args.output
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "holdout-rankings.json", holdout)
    dump(output / "holdout-probabilities.json", holdout_probs)
    dump(output / "rankings.json", official_rankings)
    dump(output / "probabilities.json", official_probs)
    dump(output / "config.json", {
        "train_packet_sha256": PACKET_SHA256, "packet_sha256": OFFICIAL_SHA256,
        "labels_sha256": LABELS_SHA256, "checkpoint_sha256": args.parent_sha256,
        "representation": "answer-free theorem/goal/context hashed lexical unigrams and bigrams",
        "dimension": args.dimension, "fit_tasks": len(fit_rows),
        "holdout_tasks": len(holdout_rows), "parameter_updates": args.updates,
        "candidate_response_hidden_state_used": False,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "tlaps_executed": False, "quality_claim": False, "gate_claim": False,
    })
    summary = {
        "fit_tasks": len(fit_rows), "holdout_tasks": len(holdout_rows),
        "parameter_updates": args.updates, "holdout_rank1": holdout_rank1,
        "holdout_tasks_with_certified_candidate": holdout_solvable,
        "official_tasks_ranked": len(official_rankings),
        "official_candidates_ranked": sum(len(values) for values in official_rankings.values()),
        "representation": "answer-free theorem/goal/context hashed lexical unigrams and bigrams",
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "tlaps_executed": False, "proof_or_quality_claim": False, "gate_claim": False,
        "loss_first_last": [losses[0], losses[-1]],
    }
    dump(output / "summary.json", summary)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
