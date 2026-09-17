#!/usr/bin/env python3
"""Independently re-rank and strict-check the residual CPU diagnostic."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.proof_dependency_graph_model import HOLDOUT_IDS, load_tasks, sha, task_candidates
from tools.proof_obligation_residual_model import residual_features, score, statement_index
from harness.proof_fragment_check import certify_fragment


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    args = parser.parse_args()
    tasks = load_tasks(args.manifest)
    model = json.loads((args.run / "model.json").read_text())
    if model.get("source_manifest_sha256") != sha(args.manifest.read_bytes()):
        raise ValueError("model/source mismatch")
    if any(model.get(key) for key in ("reference_fragment_used", "protected_verifier_feedback_used",
                                      "repair_or_reward_used", "official_packet_used")):
        raise ValueError("unsafe model provenance")
    indexes = {task_id: statement_index(tasks[task_id]) for task_id in HOLDOUT_IDS}
    candidates = {task_id: task_candidates(tasks[task_id]) for task_id in HOLDOUT_IDS}
    rankings = {}
    checks = []
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        ranked = [{"candidate_index": index, "candidate": candidate,
                   "residual_score": score(model["weights"], model["bias"],
                                            residual_features(task, candidate, indexes[task_id]))}
                  for index, candidate in enumerate(candidates[task_id])]
        rankings[task_id] = sorted(ranked, key=lambda row: (-row["residual_score"], row["candidate_index"]))
        for rank_index, row in enumerate(rankings[task_id][:4], 1):
            result = certify_fragment(task["prefix"], row["candidate"], task["suffix"],
                                      theorem_name=task["theorem_name"],
                                      dependencies=tuple(Path(x) for x in task.get("dependencies", [])),
                                      work_root=args.run / "independent-checks" / task_id / str(rank_index),
                                      timeout=args.timeout)
            checks.append({"task": task_id, "rank": rank_index,
                           "candidate_index": row["candidate_index"], "candidate": row["candidate"],
                           "residual_score": row["residual_score"],
                           "certified": bool(result["certified"]), "status": result["status"],
                           "proved": result["proved"], "total": result["total"],
                           "seconds": result["seconds"], "sha256": result["sha256"]})
    by_task = {task_id: [row for row in checks if row["task"] == task_id]
               for task_id in sorted(HOLDOUT_IDS)}
    summary = {
        "kind": "proof_obligation_residual_independent_score_v1",
        "tasks": len(HOLDOUT_IDS), "denominator_fixed": True, "rankings_recomputed": True,
        "checks": len(checks),
        "rank1": sum(int(rows[0]["certified"]) for rows in by_task.values()),
        "top4": sum(int(any(row["certified"] for row in rows)) for rows in by_task.values()),
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "official_packet_used": False,
        "quality_claim": False, "gate_claim": False,
        "manifest_sha256": sha(args.manifest.read_bytes()),
        "model_sha256": sha((args.run / "model.json").read_bytes()),
    }
    (args.run / "independent-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.run / "independent-checks.jsonl").write_text("".join(json.dumps(row) + "\n" for row in checks))
    (args.run / "independent-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
