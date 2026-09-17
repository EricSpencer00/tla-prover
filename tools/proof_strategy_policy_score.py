#!/usr/bin/env python3
"""Independently score scaffold-expanded strategy-policy outputs with TLAPS."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_fragment_check import certify_fragment
from tools import proof_strategy_policy as policy


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def score(packet_path: Path, generations_path: Path, output: Path,
          work_root: Path, dependency_root: Path | None, timeout: int) -> dict:
    packet = policy.load_packet(packet_path, policy.sha(packet_path.read_bytes()))
    generations = json.loads(generations_path.read_text())
    by_id = {row["id"]: row for row in packet["development_rows"]}
    if len(generations) != 4 or {row.get("id") for row in generations} != set(by_id):
        raise ValueError("exact four strategy generations required")
    rows = []
    for generated in generations:
        task = by_id[generated["id"]]
        index = generated.get("candidate_index")
        if generated.get("valid") is not True or not isinstance(index, int):
            rows.append({"id": generated["id"], "certified": False,
                         "status": generated.get("status", "invalid_strategy"),
                         "proved": 0, "total": 0, "strategy_id": generated.get("strategy_id")})
            continue
        if not 0 <= index < len(task["candidate_proposals"]):
            raise ValueError("candidate index outside frozen renderer lattice")
        candidate = task["candidate_proposals"][index]
        if candidate != generated.get("candidate"):
            raise ValueError("generated candidate changed after worker")
        dependencies = tuple(Path(path) for path in task["dependencies"])
        if dependency_root is not None:
            dependencies = tuple(dependency_root / path.name for path in dependencies)
        result = certify_fragment(task["prefix"], candidate, task["suffix"],
                                 theorem_name=task["theorem_name"],
                                 dependencies=dependencies,
                                 work_root=work_root / generated["id"], timeout=timeout)
        rows.append({"id": generated["id"], "candidate_index": index,
                     "candidate": candidate, "strategy_id": generated.get("strategy_id"), **result})
    legacy = os.environ.get("PROVE_TLA_TLAPM_LEGACY") == "1"
    summary = {
        "packet_sha256": sha(packet_path.read_bytes()),
        "generations_sha256": sha(generations_path.read_bytes()),
        "rows": rows, "tasks": 4,
        "certified_tasks": sum(row.get("certified") is True for row in rows),
        "verifier_runs": len(rows),
        "verifier_mode": "legacy_tlaps_1.5.0_uncached_nofp_threads1" if legacy else "tlaps_strict_uncached",
        "strict_flags_used": not legacy, "verifier_feedback_used": False,
        "repair_used": False, "reward_used": False, "fixed_denominator": 4,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    (output / "rows.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", required=True, type=Path)
    parser.add_argument("--generations", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--work-root", required=True, type=Path)
    parser.add_argument("--dependency-root", type=Path)
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 120:
        parser.error("timeout must be bounded")
    print(json.dumps(score(args.packet, args.generations, args.output,
                           args.work_root, args.dependency_root, args.timeout), indent=2))


if __name__ == "__main__":
    main()
