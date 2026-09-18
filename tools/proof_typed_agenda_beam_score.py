#!/usr/bin/env python3
"""Fresh strict score of the exact top-k candidate beams from a worker."""
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
from tools import proof_typed_agenda as agenda
from tools.proof_typed_agenda_score import load_frozen_audit, load_generations


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def top_indices(row: dict, width: int) -> list[int]:
    if not 1 <= width <= 8:
        raise ValueError("beam width must be between 1 and 8")
    scores = row.get("scores")
    if scores:
        if not isinstance(scores, list):
            raise ValueError("worker scores must be a list")
        # The scorer binds every returned score to the frozen lattice length.
        return sorted(range(len(scores)), key=lambda index: (scores[index], -index), reverse=True)[:width]
    return list(range(width))


def score(packet_path: Path, generation_paths: dict[str, Path], audit_path: Path,
          output: Path, work_root: Path, timeout: int, width: int) -> dict:
    packet = agenda.load_packet(packet_path, agenda.sha(packet_path.read_bytes()))
    audit = load_frozen_audit(audit_path, packet)
    audit_by_key = {(row["task"], row["candidate_index"]): row for row in audit}
    task_by_id = {row["id"]: row for row in packet["development_rows"]}
    rows = []
    for arm, path in generation_paths.items():
        for generated in load_generations(path, packet):
            task = task_by_id[generated["id"]]
            if generated.get("scores") and len(generated["scores"]) != len(task["candidate_proposals"]):
                raise ValueError("worker score vector does not bind frozen candidate lattice")
            indices = top_indices(generated, width)
            if len(indices) != min(width, len(task["candidate_proposals"])):
                raise ValueError("beam does not cover frozen candidate lattice")
            for index in indices:
                candidate = task["candidate_proposals"][index]
                slots = task["candidate_agenda_slots"][index]
                result = certify_fragment(
                    task["prefix"], candidate, task["suffix"],
                    theorem_name=task["theorem_name"], dependencies=tuple(Path(dep) for dep in task["dependencies"]),
                    work_root=work_root / arm / generated["id"] / str(index), timeout=timeout)
                frozen = audit_by_key[(generated["id"], index)]
                rows.append({
                    "arm": arm, "id": generated["id"], "candidate_index": index,
                    "candidate": candidate, "agenda_slots": slots,
                    "fresh_certified": bool(result["certified"]),
                    "fresh_status": result["status"], "fresh_proved": result["proved"],
                    "fresh_total": result["total"], "fresh_seconds": result["seconds"],
                    "frozen_audit_certified": bool(frozen["certified"]),
                    "frozen_audit_status": frozen["status"],
                    "candidate_sha256": result["sha256"],
                })
    summary = {
        "kind": "independent_typed_agenda_beam_score",
        "packet_sha256": sha(packet_path.read_bytes()),
        "generations_sha256": {arm: sha(path.read_bytes()) for arm, path in generation_paths.items()},
        "frozen_audit_sha256": sha(audit_path.read_bytes()),
        "fixed_candidate_denominator": len(audit), "beam_width": width,
        "fresh_candidate_checks": len(rows), "arms": list(generation_paths),
        "certified_candidates_by_arm": {
            arm: sum(row["fresh_certified"] for row in rows if row["arm"] == arm)
            for arm in generation_paths
        },
        "tasks_with_any_certified_by_arm": {
            arm: sum(any(row["fresh_certified"] for row in rows
                         if row["arm"] == arm and row["id"] == task_id)
                     for task_id in task_by_id)
            for arm in generation_paths
        },
        "frozen_certified_candidates_by_arm": {
            arm: sum(row["frozen_audit_certified"] for row in rows if row["arm"] == arm)
            for arm in generation_paths
        },
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "training_executed": False, "quality_claim": False, "proof_claim": False,
        "gate_claim": False, "checker": "fresh strict uncached TLAPS for exact worker top-k beams",
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
    parser.add_argument("--width", type=int, default=4)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 15:
        parser.error("bounded strict-TLAPS timeout required")
    paths = {"base": args.base, "parent": args.parent, "child": args.child}
    print(json.dumps(score(args.packet, paths, args.audit, args.output,
                           args.work_root, args.timeout, args.width), indent=2))


if __name__ == "__main__":
    main()
