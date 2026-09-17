#!/usr/bin/env python3
"""Recompute and independently strict-check a goal-coverage CPU ranking."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools.proof_dependency_graph_model import HOLDOUT_IDS, load_tasks, sha, task_candidates
from tools.proof_goal_coverage_model import coverage_features, statement_index


def rank(task, candidates, index, model):
    weights, bias = model["weights"], model["bias"]
    rows = []
    for candidate_index, candidate in enumerate(candidates):
        rows.append({"candidate_index": candidate_index, "candidate": candidate,
                     "coverage_score": bias + sum(weights.get(token, 0.0)
                                                 for token in coverage_features(task, candidate, index))})
    return sorted(rows, key=lambda row: (-row["coverage_score"], row["candidate_index"]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    args = parser.parse_args()
    tasks = load_tasks(args.manifest)
    model = json.loads((args.run / "model.json").read_text())
    if model.get("source_manifest_sha256") != sha(args.manifest.read_bytes()):
        raise ValueError("model/source mismatch")
    if model.get("reference_fragment_used") or model.get("protected_verifier_feedback_used"):
        raise ValueError("unsafe model provenance")
    indexes = {task_id: statement_index(tasks[task_id]) for task_id in HOLDOUT_IDS}
    candidates = {task_id: task_candidates(tasks[task_id]) for task_id in HOLDOUT_IDS}
    rankings = {task_id: rank(tasks[task_id], candidates[task_id], indexes[task_id], model)
                for task_id in sorted(HOLDOUT_IDS)}
    checks = []
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        for rank_index, row in enumerate(rankings[task_id][:4], 1):
            result = certify_fragment(task["prefix"], row["candidate"], task["suffix"],
                                      theorem_name=task["theorem_name"],
                                      dependencies=tuple(Path(x) for x in task.get("dependencies", [])),
                                      work_root=args.run / "independent-checks" / task_id / str(rank_index),
                                      timeout=args.timeout)
            checks.append({"task": task_id, "rank": rank_index,
                           "candidate_index": row["candidate_index"], "candidate": row["candidate"],
                           "coverage_score": row["coverage_score"],
                           "certified": bool(result["certified"]), "status": result["status"],
                           "proved": result["proved"], "total": result["total"],
                           "seconds": result["seconds"], "sha256": result["sha256"]})
    by_task = {task_id: [row for row in checks if row["task"] == task_id]
               for task_id in sorted(HOLDOUT_IDS)}
    summary = {"kind": "proof_goal_coverage_independent_score_v1", "tasks": len(HOLDOUT_IDS),
               "denominator_fixed": True, "rankings_recomputed": True, "checks": len(checks),
               "rank1": sum(int(rows[0]["certified"]) for rows in by_task.values()),
               "top4": sum(int(any(row["certified"] for row in rows)) for rows in by_task.values()),
               "reference_fragment_used": False, "protected_verifier_feedback_used": False,
               "repair_or_reward_used": False, "official_packet_used": False,
               "quality_claim": False, "gate_claim": False,
               "manifest_sha256": sha(args.manifest.read_bytes()),
               "model_sha256": sha((args.run / "model.json").read_bytes())}
    (args.run / "independent-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.run / "independent-checks.jsonl").write_text("".join(json.dumps(row) + "\n" for row in checks))
    (args.run / "independent-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
