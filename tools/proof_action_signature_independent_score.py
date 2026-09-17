#!/usr/bin/env python3
"""Independently strict-TLAPS-score semantic-signature rankings.

This scorer is deliberately separate from the GPU worker.  It validates that
rankings contain exactly the frozen answer-free proposals, then assembles and
checks ranked actions against immutable theorem scaffolds.  It never reads a
reference fragment and never feeds a verifier result back to the ranking.
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

FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}
HOLDOUT_IDS = {
    "highest-done-step", "highest-correctness", "simple-preservation",
    "simple-short-full",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def reject_keys(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def load_tasks(manifest_path: Path, packet: dict, expected_manifest_sha256: str,
               split: str) -> dict:
    raw = manifest_path.read_bytes()
    if sha(raw) != expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    tasks = {}
    for source in manifest.get("tasks", []):
        if source.get("split") != split:
            continue
        if split == "train" and source["id"] not in HOLDOUT_IDS:
            continue
        # Only immutable scaffold fields are selected.  The reference proof
        # field is intentionally not accessed.
        tasks[source["id"]] = {key: source[key] for key in (
            "id", "prefix", "suffix", "theorem_name", "dependencies")}
    if split == "official_test":
        expected = 119
    else:
        expected = 4
    if len(tasks) != expected:
        raise ValueError(f"expected {expected} scoring scaffolds, got {len(tasks)}")
    return tasks


def normalize_rankings(rankings: dict, packet: dict) -> dict:
    proposal_by_task = {row["id"]: row["candidate_proposals"]
                        for row in packet["rows"]}
    normalized = {}
    for task_id, rows in rankings.items():
        if task_id not in proposal_by_task or not isinstance(rows, list):
            raise ValueError("unexpected ranking task")
        seen = set()
        checked = []
        for row in rows:
            index = row.get("candidate_index")
            if not isinstance(index, int) or not 0 <= index < len(proposal_by_task[task_id]):
                raise ValueError("ranking index outside frozen candidate set")
            if index in seen or row.get("candidate") != proposal_by_task[task_id][index]:
                raise ValueError("ranking candidate mismatch")
            distance = row.get("signature_distance")
            if not isinstance(distance, (int, float)):
                raise ValueError("missing signature distance")
            seen.add(index)
            checked.append(row)
        if len(seen) != len(proposal_by_task[task_id]):
            raise ValueError("incomplete task ranking cannot receive credit")
        normalized[task_id] = sorted(
            checked, key=lambda row: (row["signature_distance"], row["candidate_index"]))
    return normalized


def score(packet_path: Path, manifest_path: Path, rankings_path: Path,
          output: Path, expected_packet_sha256: str,
          expected_manifest_sha256: str, expected_checkpoint_sha256: str,
          split: str, timeout: int, seconds: int) -> dict:
    packet_bytes = packet_path.read_bytes()
    if sha(packet_bytes) != expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_bytes)
    reject_keys(packet)
    expected_kind = ("answer_free_official_symbolic_candidate_ranking"
                     if split == "official_test"
                     else "answer_free_multistep_symbolic_action_coverage")
    expected_denominator = 119 if split == "official_test" else 17
    if packet.get("packet_kind") != expected_kind or packet.get("denominator") != expected_denominator:
        raise ValueError("unsupported packet contract")
    tasks = load_tasks(manifest_path, packet, expected_manifest_sha256, split)
    ranking_data = json.loads(rankings_path.read_bytes())
    worker_config = json.loads((rankings_path.parent / "config.json").read_bytes())
    packet_binding_key = "packet_sha256" if split == "official_test" else "train_packet_sha256"
    if worker_config.get(packet_binding_key) != sha(packet_bytes):
        raise ValueError("ranking receipt is not bound to this packet")
    if worker_config.get("checkpoint_sha256") != expected_checkpoint_sha256:
        raise ValueError("worker did not bind exact parent checkpoint")
    normalized = normalize_rankings(ranking_data, packet)
    if not 1 <= timeout <= 15 or not 30 <= seconds <= 900:
        raise ValueError("checker budget outside frozen bound")
    output.mkdir(parents=True, exist_ok=False)
    checks = []
    started = time.monotonic()
    with (output / "checks.jsonl").open("x") as stream:
        for task_id, task in tasks.items():
            ranked = normalized.get(task_id)
            if not ranked:
                continue
            for rank, row in enumerate(ranked[:4], 1):
                if time.monotonic() + timeout > started + seconds:
                    break
                result = certify_fragment(
                    task["prefix"], row["candidate"], task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task["dependencies"]),
                    work_root=output / "checks" / task_id / str(rank),
                    timeout=timeout)
                result.update(task=task_id, rank=rank,
                              candidate_index=row["candidate_index"],
                              candidate=row["candidate"],
                              signature_distance=row["signature_distance"])
                checks.append(result)
                stream.write(json.dumps(result) + "\n")
                stream.flush()
                if result["certified"]:
                    break
    measured = {row["task"] for row in checks}
    certified = {row["task"] for row in checks if row["certified"]}
    top1 = {row["task"] for row in checks
            if row["certified"] and row["rank"] == 1}
    summary = {
        "requested_tasks": len(tasks),
        "fully_ranked_tasks": len(normalized),
        "measured_tasks": len(measured),
        "certified_tasks_top4": len(certified),
        "top1_verified": len(top1),
        "checker_attempts": len(checks),
        "checker": "strict uncached TLAPS --strict --nofp",
        "split": split,
        "reference_fragment_used": False,
        "training_executed": False,
        "repair_or_reward": False,
        "quality_claim": False,
        "gate_claim": False,
        "denominator_fixed": True,
        "method": "independent strict TLAPS over prompt-only semantic-signature ranked proposals",
        "elapsed_seconds": time.monotonic() - started,
    }
    dump(output / "rankings.json", normalized)
    dump(output / "summary.json", summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--rankings", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--expected-checkpoint-sha256", required=True)
    parser.add_argument("--split", choices=("train", "official_test"), required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    print(json.dumps(score(args.packet, args.manifest, args.rankings, args.output,
                           args.expected_packet_sha256, args.expected_manifest_sha256,
                           args.expected_checkpoint_sha256, args.split,
                           args.timeout, args.seconds), indent=2))


if __name__ == "__main__":
    main()
