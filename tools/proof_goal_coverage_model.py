#!/usr/bin/env python3
"""Fit an answer-free goal-to-premise coverage model over strict TLAPS labels.

This bounded CPU diagnostic is deliberately not a proof generator.  It uses
only the frozen theorem goal, visible/imported statement text, and candidate
syntax.  A candidate is represented by coverage of goal tokens by its selected
premises, premise redundancy, provenance, and solver/action shape.  No
declaration dependency graph, reference fragment, proof body, verifier
feedback, repair, reward, or official outcome is read.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from harness.runner import TLA_LIBRARY
from tools.proof_dependency_graph_model import (
    HOLDOUT_IDS, TRAIN_IDS, EXPECTED_MANIFEST_SHA, goal_text, load_tasks,
    sha, task_candidates,
)
from tools.proof_fact_search import libraries, statements, tokens


def candidate_parts(candidate: str) -> tuple[str, tuple[str, ...]]:
    if re.search(r"\b(?:AXIOM|OMITTED)\b", candidate):
        raise ValueError("unsafe admission atom")
    if candidate == "OBVIOUS":
        return "obvious", ()
    for prefix, solver in (("BY SMT DEF ", "smt_def"), ("BY DEF ", "def"),
                           ("BY SMT, ", "smt_facts"), ("BY ", "facts")):
        if candidate.startswith(prefix):
            return solver, tuple(part.strip() for part in candidate[len(prefix):].split(",")
                                 if part.strip())
    raise ValueError(f"unsupported candidate syntax: {candidate!r}")


def statement_index(task: dict) -> dict:
    dependencies = [Path(path) for path in task.get("dependencies", [])]
    dependency_texts = [path.read_text() for path in dependencies]
    library_paths = libraries(task["prefix"], dependency_texts, TLA_LIBRARY.split(":"))
    result = {}
    for provenance, facts in (
        ("local", statements(task["prefix"], task["theorem_name"])),
        ("dependency", [fact for source in dependency_texts
                         for fact in statements(source, task["theorem_name"], exported=True)]),
        ("imported", [fact for path in library_paths
                       for fact in statements(path.read_text(), task["theorem_name"], exported=True)]),
    ):
        for fact in facts:
            result.setdefault(fact["name"], {**fact, "provenance": provenance})
    return {"facts": result,
            "library_sha256": {str(path): sha(path.read_bytes()) for path in library_paths}}


def _tokens(text: str) -> set[str]:
    return {token.upper() for token in tokens(text)}


def _bin(value: int | float, maximum: int = 16) -> str:
    return str(max(0, min(maximum, int(value))))


def coverage_features(task: dict, candidate: str, index: dict | None = None) -> tuple[str, ...]:
    index = index or statement_index(task)
    solver, names = candidate_parts(candidate)
    goal = _tokens(goal_text(task))
    facts = index["facts"]
    selected = [facts[name] for name in names if name in facts]
    selected_terms = [_tokens(fact["statement"]) for fact in selected]
    union = set().union(*selected_terms) if selected_terms else set()
    covered = goal & union
    uncovered = goal - union
    values = {
        "solver:" + solver,
        "candidate:names:" + _bin(len(names)),
        "candidate:resolved:" + _bin(len(selected)),
        "candidate:unresolved:" + _bin(len(names) - len(selected)),
        "goal:size:" + _bin(len(goal), 32),
        "goal:covered:" + _bin(len(covered), 32),
        "goal:uncovered:" + _bin(len(uncovered), 32),
        "goal:coverage_ratio:" + _bin(round(8 * len(covered) / max(1, len(goal))), 8),
        "goal:quantifiers:" + _bin(len(re.findall(r"\\[AE]", goal_text(task))), 8),
        "goal:conjunctions:" + _bin(goal_text(task).count("/\\"), 8),
        "goal:temporal:" + str(int(bool(re.search(r"\[\]|<>|WF_|SF_", goal_text(task))))),
        "facts:local:" + _bin(sum(fact["provenance"] == "local" for fact in selected)),
        "facts:dependency:" + _bin(sum(fact["provenance"] == "dependency" for fact in selected)),
        "facts:imported:" + _bin(sum(fact["provenance"] == "imported" for fact in selected)),
        "facts:union_terms:" + _bin(len(union), 32),
    }
    overlap_values = [len(goal & terms) for terms in selected_terms]
    if overlap_values:
        values.update({"fact:max_overlap:" + _bin(max(overlap_values), 16),
                       "fact:sum_overlap:" + _bin(sum(overlap_values), 32),
                       "fact:mean_overlap:" + _bin(round(sum(overlap_values) / len(overlap_values)), 16),
                       "fact:max_terms:" + _bin(max(map(len, selected_terms)), 32)})
        pair_overlaps = [len(selected_terms[i] & selected_terms[j])
                         for i in range(len(selected_terms))
                         for j in range(i + 1, len(selected_terms))]
        values.add("facts:redundant_pairs:" + _bin(sum(value > 0 for value in pair_overlaps), 32))
        values.add("facts:redundant_terms:" + _bin(sum(pair_overlaps), 32))
    for feature in ("covered", "uncovered", "resolved"):
        value = next(item.rsplit(":", 1)[1] for item in values
                     if item.startswith("goal:" + feature + ":") or
                     item.startswith("candidate:" + feature + ":"))
        values.add("solver_goal:" + solver + ":" + feature + ":" + value)
    return tuple(sorted(values))


def fit_logistic(examples: list[tuple[tuple[str, ...], int]], epochs=3000,
                 learning_rate=0.08, l2=0.12) -> tuple[dict[str, float], float]:
    vocabulary = sorted({token for feature_set, _ in examples for token in feature_set})
    weights = {token: 0.0 for token in vocabulary}
    bias = 0.0
    for _ in range(epochs):
        gradients = {token: l2 * value for token, value in weights.items()}
        bias_gradient = l2 * bias
        for feature_set, target in examples:
            value = max(-30.0, min(30.0, bias + sum(weights[token] for token in feature_set)))
            probability = 1.0 / (1.0 + math.exp(-value))
            delta = probability - target
            bias_gradient += delta
            for token in feature_set:
                gradients[token] += delta
        scale = learning_rate / max(1, len(examples))
        bias -= scale * bias_gradient
        for token in weights:
            weights[token] -= scale * gradients[token]
    return weights, bias


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if not 1 <= args.timeout <= 10 or not 60 <= args.seconds <= 900:
        parser.error("bounded timeout/seconds required")
    tasks = load_tasks(args.manifest)
    args.output.mkdir(parents=True)
    indexes = {task_id: statement_index(task) for task_id, task in tasks.items()}
    candidate_map = {task_id: task_candidates(task) for task_id, task in tasks.items()}
    (args.output / "candidates.json").write_text(json.dumps(candidate_map, indent=2) + "\n")
    (args.output / "index-summary.json").write_text(json.dumps({
        task_id: {"facts": len(index["facts"]), "library_sha256": index["library_sha256"]}
        for task_id, index in sorted(indexes.items())
    }, indent=2) + "\n")
    started = time.monotonic()
    examples, labels = [], []
    with (args.output / "strict-labels.jsonl").open("x") as stream:
        for task_id in sorted(tasks):
            task = tasks[task_id]
            for candidate_index, candidate in enumerate(candidate_map[task_id]):
                if time.monotonic() + args.timeout > started + args.seconds:
                    raise TimeoutError("strict verifier budget exhausted before complete coverage")
                result = certify_fragment(task["prefix"], candidate, task["suffix"],
                                          theorem_name=task["theorem_name"],
                                          dependencies=tuple(Path(x) for x in task.get("dependencies", [])),
                                          work_root=args.output / "checks" / task_id / str(candidate_index),
                                          timeout=args.timeout)
                record = {"task": task_id, "split": task["split"], "candidate_index": candidate_index,
                          "candidate": candidate, "certified": bool(result["certified"]),
                          "status": result["status"], "proved": result["proved"],
                          "total": result["total"], "seconds": result["seconds"],
                          "sha256": result["sha256"]}
                labels.append(record)
                stream.write(json.dumps(record) + "\n"); stream.flush()
                if task_id in TRAIN_IDS:
                    examples.append((coverage_features(task, candidate, indexes[task_id]),
                                     int(record["certified"])))
    weights, bias = fit_logistic(examples)
    label_map = {(row["task"], row["candidate_index"]): row["certified"] for row in labels}
    rankings = {}
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        values = [{"candidate_index": index, "candidate": candidate,
                   "coverage_score": bias + sum(weights.get(token, 0.0)
                                                 for token in coverage_features(task, candidate, indexes[task_id])),
                   "certified": bool(label_map[(task_id, index)])}
                  for index, candidate in enumerate(candidate_map[task_id])]
        rankings[task_id] = sorted(values, key=lambda row: (-row["coverage_score"], row["candidate_index"]))
    rank1 = sum(int(rows[0]["certified"]) for rows in rankings.values())
    top4 = sum(int(any(row["certified"] for row in rows[:4])) for rows in rankings.values())
    (args.output / "holdout-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.output / "model.json").write_text(json.dumps({
        "representation": "goal-to-premise set coverage and redundancy",
        "source_manifest_sha256": sha(args.manifest.read_bytes()), "training_tasks": sorted(TRAIN_IDS),
        "holdout_tasks": sorted(HOLDOUT_IDS), "training_examples": len(examples),
        "bias": bias, "weights": weights, "reference_fragment_used": False,
        "protected_verifier_feedback_used": False, "repair_or_reward_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
    }, indent=2) + "\n")
    summary = {
        "kind": "proof_goal_coverage_model_v1", "strict_label_records": len(labels),
        "train_positive_labels": sum(int(row["certified"]) for row in labels if row["split"] == "train"),
        "holdout_positive_labels": sum(int(row["certified"]) for row in labels if row["split"] == "development"),
        "train_tasks": len(TRAIN_IDS), "holdout_tasks": len(HOLDOUT_IDS),
        "holdout_rank1": rank1, "holdout_top4": top4, "denominator_fixed": True,
        "checker": "strict uncached TLAPS", "training_executed": False,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "official_packet_used": False,
        "quality_claim": False, "gate_claim": False,
        "manifest_sha256": sha(args.manifest.read_bytes()),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
