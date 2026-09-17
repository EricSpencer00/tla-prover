#!/usr/bin/env python3
"""Independently re-rank and re-check a dependency-graph CPU diagnostic.

This scorer deliberately ignores the worker's strict-label file and ranking
file.  It reconstructs candidates and answer-free graph features from the
frozen manifest, loads only the learned feature weights, then performs fresh
strict uncached TLAPS checks on the four highest-ranked candidates per
development task.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools.proof_dependency_graph_model import (
    HOLDOUT_IDS, EXPECTED_MANIFEST_SHA, declaration_graph, graph_features,
    load_tasks, sha, task_candidates,
)


def rank(task: dict, candidates: list[str], graph: dict, model: dict) -> list[dict]:
    weights = model["weights"]
    bias = model["bias"]
    rows = []
    for index, candidate in enumerate(candidates):
        features = graph_features(task, candidate, graph)
        rows.append({"candidate_index": index, "candidate": candidate,
                     "graph_score": bias + sum(weights.get(token, 0.0) for token in features)})
    return sorted(rows, key=lambda row: (-row["graph_score"], row["candidate_index"]))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    args = parser.parse_args()
    tasks = load_tasks(args.manifest)
    model = json.loads((args.run / "model.json").read_text())
    if model.get("source_manifest_sha256") != sha(args.manifest.read_bytes()):
        raise ValueError("model/source manifest mismatch")
    if model.get("reference_fragment_used") or model.get("protected_verifier_feedback_used"):
        raise ValueError("unsafe model provenance")
    graphs = {task_id: declaration_graph(tasks[task_id]) for task_id in HOLDOUT_IDS}
    candidates = {task_id: task_candidates(tasks[task_id]) for task_id in HOLDOUT_IDS}
    rankings = {task_id: rank(tasks[task_id], candidates[task_id], graphs[task_id], model)
                for task_id in sorted(HOLDOUT_IDS)}
    checked = []
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        for rank_index, row in enumerate(rankings[task_id][:4], 1):
            result = certify_fragment(
                task["prefix"], row["candidate"], task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                work_root=args.run / "independent-checks" / task_id / str(rank_index),
                timeout=args.timeout,
            )
            checked.append({"task": task_id, "rank": rank_index,
                            "candidate_index": row["candidate_index"],
                            "candidate": row["candidate"],
                            "graph_score": row["graph_score"],
                            "certified": bool(result["certified"]),
                            "status": result["status"], "proved": result["proved"],
                            "total": result["total"], "seconds": result["seconds"],
                            "sha256": result["sha256"]})
    by_task = {task_id: [row for row in checked if row["task"] == task_id]
               for task_id in sorted(HOLDOUT_IDS)}
    summary = {
        "kind": "proof_dependency_graph_independent_score_v1",
        "tasks": len(HOLDOUT_IDS), "denominator_fixed": True,
        "rankings_recomputed": True, "checks": len(checked),
        "rank1": sum(int(rows[0]["certified"]) for rows in by_task.values()),
        "top4": sum(int(any(row["certified"] for row in rows)) for rows in by_task.values()),
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "official_packet_used": False,
        "quality_claim": False, "gate_claim": False,
        "manifest_sha256": sha(args.manifest.read_bytes()),
        "model_sha256": sha((args.run / "model.json").read_bytes()),
    }
    (args.run / "independent-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.run / "independent-checks.jsonl").write_text(
        "".join(json.dumps(row) + "\n" for row in checked))
    (args.run / "independent-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
