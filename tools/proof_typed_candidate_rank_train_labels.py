#!/usr/bin/env python3
"""Generate sanitized strict-TLAPS labels for the typed TRAIN lattice only.

The packet contains exact TRAIN prefixes/suffixes and candidate proposals, but
no reference fragments.  Each candidate is checked in a fresh work directory;
the output exposes only candidate identity and the independent certification
bit, never checker text or answer-bearing bytes.  DEVELOPMENT and official
rows are not inspected.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools import proof_typed_candidate_rank as rank


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def load_packet(path: Path, expected_sha256: str) -> dict:
    packet = rank.load_packet(path, expected_sha256)
    if len(packet.get("train_rows", [])) != 17:
        raise ValueError("exact 17-row TRAIN packet required")
    return packet


def label(packet_path: Path, expected_sha256: str, output: Path,
          work_root: Path, timeout: int) -> dict:
    packet = load_packet(packet_path, expected_sha256)
    if output.exists():
        raise ValueError("output must be new")
    output.mkdir(parents=True, exist_ok=False)
    work_root.mkdir(parents=True, exist_ok=True)
    records: list[dict] = []
    started = time.monotonic()
    for row in packet["train_rows"]:
        for index, candidate in enumerate(row["candidate_proposals"]):
            result = certify_fragment(
                row["prefix"], candidate, row["suffix"],
                theorem_name=row["theorem_name"],
                dependencies=tuple(Path(dep) for dep in row["dependencies"]),
                work_root=work_root / row["id"] / str(index), timeout=timeout,
            )
            records.append({
                "task": row["id"], "candidate_index": index,
                "candidate": candidate, "certified": bool(result["certified"]),
            })
    labels_path = output / "labels.jsonl"
    labels_path.write_text("".join(json.dumps(record, sort_keys=True) + "\n"
                                     for record in records))
    certified_candidates = sum(record["certified"] for record in records)
    tasks_with_certified_candidate = sum(
        any(record["certified"] for record in records if record["task"] == row["id"])
        for row in packet["train_rows"]
    )
    summary = {
        "kind": "typed_candidate_rank_strict_train_labels",
        "packet_sha256": sha(packet_path.read_bytes()),
        "label_sha256": sha(labels_path.read_bytes()),
        "train_tasks": len(packet["train_rows"]),
        "candidate_checks": len(records),
        "certified_candidates": certified_candidates,
        "tasks_with_certified_candidate": tasks_with_certified_candidate,
        "training_eligible": bool(certified_candidates and tasks_with_certified_candidate),
        "development_rows_inspected": 0,
        "official_rows_inspected": 0,
        "reference_fragments_used": False,
        "protected_verifier_feedback_used": False,
        "repair_used": False, "reward_used": False,
        "training_executed": False, "parameter_updates": 0,
        "proof_or_quality_claim": False, "gate_claim": False,
        "checker": "fresh uncached strict TLAPS per TRAIN candidate",
        "timeout_seconds": timeout,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=10)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 15:
        parser.error("bounded strict-TLAPS timeout required")
    print(json.dumps(label(args.packet, args.expected_packet_sha256, args.output,
                           args.work_root, args.timeout), indent=2), flush=True)


if __name__ == "__main__":
    main()
