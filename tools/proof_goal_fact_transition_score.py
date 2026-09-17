#!/usr/bin/env python3
"""Independently score goal/fact transition selections with strict uncached TLAPS."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools import proof_goal_fact_transition as transition


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def load_generations(path: Path, packet: dict) -> list[dict]:
    rows = json.loads(path.read_text())
    expected = {row["id"] for row in packet["development_rows"]}
    if len(rows) != len(expected) or {row.get("id") for row in rows} != expected:
        raise ValueError("generation ids do not bind exact DEVELOPMENT population")
    by_id = {row["id"]: row for row in packet["development_rows"]}
    for row in rows:
        task = by_id[row["id"]]
        index = row.get("candidate_index")
        if row.get("valid") is not True or not isinstance(index, int):
            raise ValueError("generation row is not a valid renderer selection")
        if not 0 <= index < len(task["candidate_proposals"]):
            raise ValueError("candidate index outside frozen renderer lattice")
        if row.get("candidate") != task["candidate_proposals"][index]:
            raise ValueError("candidate bytes changed after worker")
        if row.get("transition_events") != task["candidate_transition_events"][index]:
            raise ValueError("candidate transition trace changed after worker")
    return rows


def load_frozen_audit(path: Path, packet: dict) -> list[dict]:
    rows = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    expected = sum(len(row["candidate_proposals"]) for row in packet["development_rows"])
    if len(rows) != expected:
        raise ValueError("frozen candidate audit denominator changed")
    by_id = {row["id"]: row for row in packet["development_rows"]}
    for row in rows:
        task = by_id.get(row.get("task"))
        index = row.get("candidate_index", -1)
        if task is None or not isinstance(index, int) or not 0 <= index < len(task["candidate_proposals"]):
            raise ValueError("frozen audit task/index outside packet")
        if row.get("candidate") != task["candidate_proposals"][index]:
            raise ValueError("frozen audit candidate bytes changed")
    return rows


def score(packet_path: Path, generation_paths: dict[str, Path], audit_path: Path,
          output: Path, work_root: Path, timeout: int) -> dict:
    packet = transition.load_packet(packet_path, transition.sha(packet_path.read_bytes()))
    audit = load_frozen_audit(audit_path, packet)
    audit_by_key = {(row["task"], row["candidate_index"]): row for row in audit}
    if len(audit_by_key) != len(audit):
        raise ValueError("duplicate frozen audit key")
    task_by_id = {row["id"]: row for row in packet["development_rows"]}
    rows = []
    for arm, path in generation_paths.items():
        for generated in load_generations(path, packet):
            task = task_by_id[generated["id"]]
            dependencies = tuple(Path(dep) for dep in task["dependencies"])
            result = certify_fragment(
                task["prefix"], generated["candidate"], task["suffix"],
                theorem_name=task["theorem_name"], dependencies=dependencies,
                work_root=work_root / arm / generated["id"], timeout=timeout)
            frozen = audit_by_key[(generated["id"], generated["candidate_index"])]
            rows.append({
                "arm": arm, "id": generated["id"],
                "candidate_index": generated["candidate_index"],
                "candidate": generated["candidate"],
                "fresh_certified": bool(result["certified"]),
                "fresh_status": result["status"], "fresh_proved": result["proved"],
                "fresh_total": result["total"], "fresh_seconds": result["seconds"],
                "frozen_audit_certified": bool(frozen["certified"]),
                "frozen_audit_status": frozen["status"],
                "candidate_sha256": result["sha256"],
            })
    summary = {
        "kind": "independent_goal_fact_transition_selection_score",
        "packet_sha256": sha(packet_path.read_bytes()),
        "generations_sha256": {arm: sha(path.read_bytes()) for arm, path in generation_paths.items()},
        "frozen_audit_sha256": sha(audit_path.read_bytes()),
        "fixed_candidate_denominator": len(audit),
        "fresh_selected_strict_checks": len(rows),
        "arms": list(generation_paths),
        "certified_by_arm": {
            arm: sum(row["fresh_certified"] for row in rows if row["arm"] == arm)
            for arm in generation_paths
        },
        "frozen_audit_certified_by_arm": {
            arm: sum(row["frozen_audit_certified"] for row in rows if row["arm"] == arm)
            for arm in generation_paths
        },
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "training_executed": False, "quality_claim": False, "proof_claim": False,
        "gate_claim": False, "checker": "fresh strict uncached TLAPS for selections",
    }
    output.mkdir(parents=True, exist_ok=False)
    (output / "rows.jsonl").write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--parent", type=Path, required=True)
    parser.add_argument("--child", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=10)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 15:
        parser.error("bounded strict-TLAPS timeout required")
    paths = {"base": args.base, "parent": args.parent, "child": args.child}
    print(json.dumps(score(args.packet, paths, args.audit, args.output, args.work_root, args.timeout), indent=2))


if __name__ == "__main__":
    main()
