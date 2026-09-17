#!/usr/bin/env python3
"""Learn an answer-free proof-obligation residual ranker.

The model sees only a theorem's visible prefix and an answer-free symbolic
candidate proposal.  It represents each candidate by which observable
obligation-shape atoms remain unsatisfied after the candidate's visible
premises are considered.  Fresh strict TLAPS labels are used only on the
17-task training split to fit a pairwise margin; the four development tasks
are ranked and independently rechecked by a separate scorer.

This is intentionally a diagnostic, not a proof or gate claim.  It does not
load reference fragments, proof bodies, feedback, repairs, rewards, or the
official population.
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
from tools.proof_dependency_graph_model import (
    HOLDOUT_IDS, TRAIN_IDS, goal_text, load_tasks, sha, task_candidates,
)
from tools.proof_goal_coverage_model import candidate_parts, statement_index
from tools.proof_fact_search import tokens


OBLIGATION_PATTERNS = {
    "conjunction": r"/\\",
    "implication": r"=>",
    "equality": r"(?<![<>=#])=(?!=)",
    "inequality": r"#|<=|>=|<|>",
    "quantifier": r"\\[AE]",
    "temporal": r"\[\]|<>|WF_|SF_",
    "prime": r"[A-Za-z_][A-Za-z0-9_]*'",
    "set": r"\\in|SUBSET|UNION|DOMAIN|\\subseteq",
    "function": r"\[[^\n]+\|->",
    "sequence": r"SEQ\(|Len\(|Head\(|Tail\(|Append",
    "unchanged": r"UNCHANGED",
}


def _bin(value: int | float, maximum: int = 16) -> str:
    return str(max(0, min(maximum, int(value))))


def _atoms(text: str) -> set[str]:
    return {token.upper() for token in tokens(text)}


def shape_atoms(text: str) -> set[str]:
    """Return coarse obligation atoms, deliberately independent of names."""
    upper = text.upper()
    result = {name for name, pattern in OBLIGATION_PATTERNS.items()
              if re.search(pattern, upper)}
    # Preserve the token-level lexical demand without exporting identifiers.
    result.add("lexical_tokens:" + _bin(len(_atoms(text)), 64))
    result.add("line_count:" + _bin(len(text.splitlines()), 32))
    return result


def _solver(candidate: str) -> str:
    if candidate == "OBVIOUS":
        return "obvious"
    if candidate.startswith("BY SMT DEF "):
        return "smt_def"
    if candidate.startswith("BY DEF "):
        return "def"
    if candidate.startswith("BY SMT, "):
        return "smt_facts"
    return "facts"


def residual_features(task: dict, candidate: str, index: dict | None = None) -> tuple[str, ...]:
    """Encode goal/candidate residual shape without candidate identities."""
    index = index or statement_index(task)
    solver, names = candidate_parts(candidate)
    goal = goal_text(task)
    goal_shapes = shape_atoms(goal)
    facts = index["facts"]
    selected = [facts[name] for name in names if name in facts]
    selected_text = "\n".join(fact["statement"] for fact in selected)
    premise_shapes = shape_atoms(selected_text) if selected else set()
    residual = {atom for atom in goal_shapes if atom not in premise_shapes}

    values = {
        "solver:" + solver,
        "candidate:atoms:" + _bin(len(names), 16),
        "candidate:resolved:" + _bin(len(selected), 16),
        "candidate:unresolved:" + _bin(len(names) - len(selected), 16),
        "goal:shape_count:" + _bin(len(goal_shapes), 32),
        "premise:shape_count:" + _bin(len(premise_shapes), 32),
        "residual:shape_count:" + _bin(len(residual), 32),
        "residual:coverage_ratio:" + _bin(8 * (len(goal_shapes) - len(residual)) /
                                             max(1, len(goal_shapes)), 8),
        "premise:statement_count:" + _bin(len(selected), 16),
        "premise:token_count:" + _bin(len(_atoms(selected_text)), 64),
    }
    for atom in sorted(goal_shapes):
        values.add("goal_has:" + atom)
        values.add("satisfied:" + atom + ":" + str(int(atom not in residual)))
    for atom in sorted(residual):
        values.add("residual_has:" + atom)
    # Solver-shape interaction is a learning signal, not a lookup of a proof.
    for solver_name in ("obvious", "facts", "def", "smt_facts", "smt_def"):
        if solver == solver_name:
            values.add("solver_residual_count:" + solver_name + ":" + _bin(len(residual), 32))
    return tuple(sorted(values))


def fit_pairwise(examples: list[tuple[tuple[str, ...], tuple[str, ...]]],
                 epochs: int = 1800, learning_rate: float = 0.06,
                 margin: float = 1.0, l2: float = 0.08) -> tuple[dict[str, float], float]:
    """Fit a deterministic linear pairwise hinge model over feature sets."""
    vocabulary = sorted({token for left, right in examples for token in (*left, *right)})
    weights = {token: 0.0 for token in vocabulary}
    bias = 0.0
    for _ in range(epochs):
        gradients = {token: l2 * value for token, value in weights.items()}
        bias_gradient = l2 * bias
        for positive, negative in examples:
            delta = bias + sum(weights.get(token, 0.0) for token in positive) \
                - sum(weights.get(token, 0.0) for token in negative)
            if delta < margin:
                scale = -1.0 / max(1, len(examples))
                bias_gradient += scale
                for token in positive:
                    gradients[token] += scale
                for token in negative:
                    gradients[token] -= scale
        step = learning_rate / max(1, len(examples))
        bias -= step * bias_gradient
        for token in weights:
            weights[token] -= step * gradients[token]
    return weights, bias


def score(weights: dict[str, float], bias: float, features: tuple[str, ...]) -> float:
    return bias + sum(weights.get(token, 0.0) for token in features)


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
    indexes = {task_id: statement_index(task) for task_id, task in tasks.items()}
    candidate_map = {task_id: task_candidates(task) for task_id, task in tasks.items()}
    args.output.mkdir(parents=True)
    (args.output / "candidates.json").write_text(json.dumps(candidate_map, indent=2) + "\n")
    started = time.monotonic()
    labels: list[dict] = []
    train_rows: dict[str, list[tuple[tuple[str, ...], int]]] = {}
    with (args.output / "strict-labels.jsonl").open("x") as stream:
        for task_id in sorted(tasks):
            task = tasks[task_id]
            rows = []
            for candidate_index, candidate in enumerate(candidate_map[task_id]):
                if time.monotonic() + args.timeout > started + args.seconds:
                    raise TimeoutError("strict verifier budget exhausted before complete coverage")
                result = certify_fragment(
                    task["prefix"], candidate, task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(x) for x in task.get("dependencies", [])),
                    work_root=args.output / "checks" / task_id / str(candidate_index),
                    timeout=args.timeout,
                )
                record = {
                    "task": task_id, "split": task["split"],
                    "candidate_index": candidate_index, "candidate": candidate,
                    "certified": bool(result["certified"]), "status": result["status"],
                    "proved": result["proved"], "total": result["total"],
                    "seconds": result["seconds"], "sha256": result["sha256"],
                }
                labels.append(record); rows.append(record)
                stream.write(json.dumps(record) + "\n"); stream.flush()
            if task_id in TRAIN_IDS:
                train_rows[task_id] = [
                    (residual_features(task, row["candidate"], indexes[task_id]),
                     int(row["certified"])) for row in rows]

    pairs = []
    for task_id in sorted(TRAIN_IDS):
        positives = [features for features, label in train_rows[task_id] if label]
        negatives = [features for features, label in train_rows[task_id] if not label]
        pairs.extend((positive, negative) for positive in positives for negative in negatives)
    if not pairs:
        raise ValueError("no strict training pairs")
    weights, bias = fit_pairwise(pairs)
    label_map = {(row["task"], row["candidate_index"]): row["certified"] for row in labels}
    rankings = {}
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        values = [{
            "candidate_index": index, "candidate": candidate,
            "residual_score": score(weights, bias,
                                    residual_features(task, candidate, indexes[task_id])),
            "certified": bool(label_map[(task_id, index)]),
        } for index, candidate in enumerate(candidate_map[task_id])]
        rankings[task_id] = sorted(values, key=lambda row: (-row["residual_score"], row["candidate_index"]))

    (args.output / "holdout-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.output / "model.json").write_text(json.dumps({
        "representation": "answer-free proof-obligation residual shape",
        "learning_signal": "within-task positive-vs-negative strict-TLAPS hinge pairs",
        "source_manifest_sha256": sha(args.manifest.read_bytes()),
        "training_tasks": sorted(TRAIN_IDS), "holdout_tasks": sorted(HOLDOUT_IDS),
        "training_pairs": len(pairs), "bias": bias, "weights": weights,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "official_packet_used": False,
        "quality_claim": False, "gate_claim": False,
    }, indent=2) + "\n")
    summary = {
        "kind": "proof_obligation_residual_model_v1",
        "strict_label_records": len(labels),
        "train_positive_labels": sum(int(row["certified"]) for row in labels if row["split"] == "train"),
        "holdout_positive_labels": sum(int(row["certified"]) for row in labels if row["split"] == "development"),
        "train_tasks": len(TRAIN_IDS), "holdout_tasks": len(HOLDOUT_IDS),
        "training_pairs": len(pairs),
        "holdout_rank1": sum(int(rows[0]["certified"]) for rows in rankings.values()),
        "holdout_top4": sum(int(any(row["certified"] for row in rows[:4])) for rows in rankings.values()),
        "denominator_fixed": True, "checker": "strict uncached TLAPS",
        "training_executed": False, "reference_fragment_used": False,
        "protected_verifier_feedback_used": False, "repair_or_reward_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
        "manifest_sha256": sha(args.manifest.read_bytes()),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
