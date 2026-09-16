#!/usr/bin/env python3
"""Independently certify ranked symbolic candidates with strict uncached TLAPS.

This scorer consumes only the answer-free packet, its rankings, and the frozen
task scaffolds needed to assemble candidates.  It never reads a reference
fragment and does not feed verifier output back into ranking or generation.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def load_tasks(manifest_path: Path, packet: dict, expected_manifest_sha256: str):
    if sha(manifest_path.read_bytes()) != expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(manifest_path.read_bytes())
    # Deliberately select only scaffold fields.  In particular, do not access
    # task['reference_fragment'] or any other held-out response field.
    tasks = {}
    for source in manifest["tasks"]:
        if source.get("split") == "development":
            tasks[source["id"]] = {key: source[key] for key in (
                "id", "prefix", "suffix", "theorem_name", "dependencies",
                "dependency_sha256")}
    if set(tasks) != {row["id"] for row in packet["rows"]}:
        raise ValueError("packet/manifest task coverage mismatch")
    return tasks


def score(packet_path: Path, manifest_path: Path, rankings_path: Path, output: Path,
          expected_packet_sha256: str, expected_manifest_sha256: str,
          expected_checkpoint_sha256: str | None = None) -> dict:
    packet_bytes = packet_path.read_bytes()
    if sha(packet_bytes) != expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_bytes)
    if (packet.get("packet_kind") != "answer_free_symbolic_candidate_ranking" or
            packet.get("denominator") != 4 or packet.get("reference_fragment_used") is not False or
            packet.get("tlaps_executed") is not False):
        raise ValueError("unsupported or answer-bearing packet")
    tasks = load_tasks(manifest_path, packet, expected_manifest_sha256)
    ranking_data = json.loads(rankings_path.read_bytes())
    worker_config_path = rankings_path.parent / "config.json"
    worker_config = json.loads(worker_config_path.read_bytes())
    if sha(packet_bytes) != worker_config.get("packet_sha256"):
        raise ValueError("worker did not bind exact packet")
    if expected_checkpoint_sha256 and worker_config.get("checkpoint_sha256") != expected_checkpoint_sha256:
        raise ValueError("worker did not bind exact parent checkpoint")
    proposal_by_task = {row["id"]: row["candidate_proposals"] for row in packet["rows"]}
    normalized = {}
    for task_id, rows in ranking_data.items():
        if task_id not in proposal_by_task or not isinstance(rows, list):
            raise ValueError("unexpected ranking task")
        seen = set()
        normalized_rows = []
        for row in rows:
            index = row.get("candidate_index")
            if not isinstance(index, int) or not 0 <= index < len(proposal_by_task[task_id]):
                raise ValueError("ranking index outside frozen candidate set")
            if index in seen or row.get("candidate") != proposal_by_task[task_id][index]:
                raise ValueError("ranking candidate mismatch")
            if not isinstance(row.get("mean_logp"), (int, float)):
                raise ValueError("missing numeric candidate score")
            seen.add(index)
            normalized_rows.append(row)
        if len(seen) != len(proposal_by_task[task_id]):
            raise ValueError("incomplete task ranking cannot receive top-k credit")
        normalized[task_id] = sorted(
            normalized_rows, key=lambda row: (-row["mean_logp"], row["candidate_index"]))
    output.mkdir(parents=True, exist_ok=False)
    checks = []
    with (output / "checks.jsonl").open("x") as stream:
        for task_id in tasks:
            ranked = normalized.get(task_id, [])
            task = tasks[task_id]
            for rank, row in enumerate(ranked[:4], 1):
                from harness.proof_fragment_check import certify_fragment
                result = certify_fragment(
                    task["prefix"], row["candidate"], task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task["dependencies"]),
                    work_root=output / "checks" / task_id / str(rank), timeout=30)
                result.update(task=task_id, rank=rank,
                              candidate_index=row["candidate_index"],
                              candidate=row["candidate"])
                checks.append(result)
                stream.write(json.dumps(result) + "\n")
                stream.flush()
                if result["certified"]:
                    break
    certified = {row["task"] for row in checks if row["certified"]}
    summary = {
        "requested_tasks": 4,
        "fully_ranked_tasks": len(normalized),
        "measured_tasks": len(normalized),
        "certified_tasks": len(certified),
        "top1_verified": len({row["task"] for row in checks
                               if row["certified"] and row["rank"] == 1}),
        "top4_verified": len(certified),
        "checker_attempts": len(checks),
        "checker": "strict uncached TLAPS --strict --nofp",
        "reference_fragment_used": False,
        "training_executed": False,
        "repair_or_reward": False,
        "quality_claim": False,
        "gate_claim": False,
        "denominator_fixed": True,
        "method": "independent strict TLAPS over exact-parent ranked symbolic proposals",
    }
    dump(output / "rankings.json", normalized)
    dump(output / "summary.json", summary)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--rankings", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--expected-checkpoint-sha256")
    args = parser.parse_args()
    print(json.dumps(score(args.packet, args.manifest, args.rankings, args.output,
                           args.expected_packet_sha256, args.expected_manifest_sha256,
                           args.expected_checkpoint_sha256), indent=2))


if __name__ == "__main__":
    main()
