#!/usr/bin/env python3
"""Train a proof-role premise selector from the disjoint TRAIN references.

This is a bounded supervised diagnostic, not RL.  Only the frozen 17-task
``train`` reference fragments are used to label which visible declarations
played a role in a human proof.  The four development reference fragments are
never read or exported.  A fact-role model then ranks answer-free symbolic
``BY`` proposals, and an independent scorer runs fresh strict TLAPS checks on
the fixed four-task development denominator.

Verifier outcomes, feedback, repairs, rewards, and official rows are not
training inputs.  A successful ranking is still not a model or gate claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.proof_dependency_graph_model import HOLDOUT_IDS, TRAIN_IDS, goal_text, sha, task_candidates
from tools.proof_goal_coverage_model import candidate_parts
from tools.proof_obligation_residual_model import shape_atoms


def load_train_and_holdout(path: Path) -> dict[str, dict]:
    raw = path.read_bytes()
    if sha(raw) != "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344":
        raise ValueError("unexpected frozen 21-task manifest")
    document = json.loads(raw)
    result = {}
    for source in document.get("tasks", []):
        task_id = source.get("id")
        if task_id not in TRAIN_IDS | HOLDOUT_IDS:
            continue
        task = {key: source.get(key, []) if key == "dependencies" else source[key]
                for key in ("id", "split", "theorem_name", "prefix", "suffix", "dependencies")}
        if task["split"] == "train":
            reference = source.get("reference_fragment")
            if not isinstance(reference, str) or not reference.strip():
                raise ValueError(f"missing train reference: {task_id}")
            task["train_reference"] = reference
        # Deliberately do not even copy a development reference field.
        result[task_id] = task
    if set(result) != TRAIN_IDS | HOLDOUT_IDS:
        raise ValueError("exact 17/4 population required")
    if any("train_reference" in result[task_id] for task_id in HOLDOUT_IDS):
        raise ValueError("development reference crossed the training boundary")
    return result


def reference_solver(reference: str) -> str:
    upper = reference.upper()
    if "OBVIOUS" in upper:
        return "obvious"
    if "PTL" in upper:
        return "ptl"
    if "SMT" in upper and "DEF" in upper:
        return "smt_def"
    if "SMT" in upper:
        return "smt"
    if "DEF" in upper:
        return "def"
    return "facts"


DECLARATION_RE = re.compile(
    r"(?m)^[ \t]*(?:LOCAL[ \t]+)?(?P<name>[A-Za-z_][A-Za-z0-9_]*)"
    r"[ \t]*(?:\([^\n]*\))?[ \t]*==[ \t]*"
)


def role_index(task: dict) -> dict:
    """Index only visible operator bodies before the target theorem."""
    prefix = task["prefix"]
    marker = re.search(r"(?m)^\s*(?:THEOREM|LEMMA)\s+" +
                       re.escape(task["theorem_name"]) + r"\s*==", prefix)
    if not marker:
        raise ValueError(f"target theorem missing: {task['id']}")
    source = prefix[:marker.start()]
    matches = list(DECLARATION_RE.finditer(source))
    facts = {}
    for index, match in enumerate(matches):
        start = match.end()
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        statement = source[start:end].strip()
        if statement:
            facts[match.group("name")] = {
                "name": match.group("name"), "statement": statement,
                "provenance": "local",
            }
    return {"facts": facts, "library_sha256": {}}


def candidate_solver(candidate: str) -> str:
    if candidate == "OBVIOUS":
        return "obvious"
    if candidate.startswith("BY SMT DEF "):
        return "smt_def"
    if candidate.startswith("BY DEF "):
        return "def"
    if candidate.startswith("BY SMT, "):
        return "smt"
    if candidate.startswith("BY PTL"):
        return "ptl"
    return "facts"


def fact_features(task: dict, fact: dict) -> tuple[str, ...]:
    goal = goal_text(task)
    statement = fact["statement"]
    goal_shapes = shape_atoms(goal)
    fact_shapes = shape_atoms(statement)
    values = {
        "fact:provenance:" + fact["provenance"],
        "fact:shape_count:" + str(min(32, len(fact_shapes))),
        "fact:token_count:" + str(min(64, len(set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", statement))))),
        "goal:shape_count:" + str(min(32, len(goal_shapes))),
        "goal:fact_shape_overlap:" + str(min(32, len(goal_shapes & fact_shapes))),
        "goal:fact_shape_missing:" + str(min(32, len(goal_shapes - fact_shapes))),
    }
    for atom in sorted(fact_shapes & goal_shapes):
        values.add("shared_shape:" + atom)
    for atom in sorted(fact_shapes - goal_shapes):
        values.add("fact_only_shape:" + atom)
    return tuple(sorted(values))


def fit_logistic(examples: list[tuple[tuple[str, ...], int]], epochs: int = 2600,
                 learning_rate: float = 0.07, l2: float = 0.12) -> tuple[dict[str, float], float]:
    vocabulary = sorted({token for features, _ in examples for token in features})
    weights = {token: 0.0 for token in vocabulary}
    bias = 0.0
    for _ in range(epochs):
        gradients = {token: l2 * value for token, value in weights.items()}
        bias_gradient = l2 * bias
        for features, target in examples:
            value = max(-30.0, min(30.0, bias + sum(weights[token] for token in features)))
            probability = 1.0 / (1.0 + math.exp(-value))
            delta = probability - target
            bias_gradient += delta
            for token in features:
                gradients[token] += delta
        scale = learning_rate / max(1, len(examples))
        bias -= scale * bias_gradient
        for token in weights:
            weights[token] -= scale * gradients[token]
    return weights, bias


def fact_score(weights: dict[str, float], bias: float, features: tuple[str, ...]) -> float:
    return bias + sum(weights.get(token, 0.0) for token in features)


def solver_prior(counts: Counter[str], solver: str) -> float:
    total = sum(counts.values())
    return math.log((counts[solver] + 1.0) / (total + 5.0))


def rank_task(task: dict, index: dict, candidates: list[str], model: dict) -> list[dict]:
    counts = Counter(model["solver_counts"])
    values = []
    for candidate_index, candidate in enumerate(candidates):
        _, names = candidate_parts(candidate)
        resolved = [index["facts"][name] for name in names if name in index["facts"]]
        score = solver_prior(counts, candidate_solver(candidate))
        score += sum(fact_score(model["weights"], model["bias"], fact_features(task, fact))
                     for fact in resolved)
        values.append({"candidate_index": candidate_index, "candidate": candidate,
                       "role_score": score,
                       "resolved_facts": len(resolved)})
    return sorted(values, key=lambda row: (-row["role_score"], row["candidate_index"]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    tasks = load_train_and_holdout(args.manifest)
    indexes = {task_id: role_index(task) for task_id, task in tasks.items()}
    candidates = {task_id: task_candidates(task) for task_id, task in tasks.items()}
    examples = []
    solver_counts = Counter()
    train_selected = {}
    for task_id in sorted(TRAIN_IDS):
        task = tasks[task_id]
        index = indexes[task_id]
        selected = {name for name in index["facts"]
                    if re.search(r"(?<![A-Za-z0-9_])" + re.escape(name) + r"(?![A-Za-z0-9_])",
                                 task["train_reference"])}
        if not selected:
            raise ValueError(f"no visible train premise selected: {task_id}")
        train_selected[task_id] = sorted(selected)
        solver_counts[reference_solver(task["train_reference"])] += 1
        for name, fact in index["facts"].items():
            examples.append((fact_features(task, fact), int(name in selected)))
    weights, bias = fit_logistic(examples)
    model = {
        "representation": "train-reference-supervised fact role and solver family",
        "learning_signal": "human TRAIN reference premise inclusion, no verifier reward",
        "source_manifest_sha256": sha(args.manifest.read_bytes()),
        "training_tasks": sorted(TRAIN_IDS), "holdout_tasks": sorted(HOLDOUT_IDS),
        "training_fact_examples": len(examples), "train_selected_fact_names": train_selected,
        "solver_counts": dict(sorted(solver_counts.items())), "bias": bias, "weights": weights,
        "train_reference_rows_used": len(TRAIN_IDS), "development_references_used": False,
        "verifier_feedback_used": False, "repair_or_reward_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
    }
    args.output.mkdir(parents=True)
    rankings = {task_id: rank_task(tasks[task_id], indexes[task_id], candidates[task_id], model)
                for task_id in sorted(HOLDOUT_IDS)}
    (args.output / "model.json").write_text(json.dumps(model, indent=2) + "\n")
    (args.output / "holdout-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    summary = {
        "kind": "proof_train_reference_premise_model_v1",
        "train_reference_rows_used": len(TRAIN_IDS), "development_references_used": False,
        "training_fact_examples": len(examples), "holdout_tasks": len(HOLDOUT_IDS),
        "candidate_rows": sum(len(values) for values in rankings.values()),
        "denominator_fixed": True, "strict_tlaps_checks_in_worker": False,
        "verifier_feedback_used": False, "repair_or_reward_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
        "manifest_sha256": sha(args.manifest.read_bytes()),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
