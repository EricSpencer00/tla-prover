#!/usr/bin/env python3
"""Independently certify model-ranked actions on the frozen official 119 set.

The ranking worker sees only the answer-free packet.  This scorer reads the
frozen theorem scaffolds, selects the model's rank-1 action, and then checks
that action (and, for diagnostic top-4 coverage, later ranked actions) with
strict uncached TLAPS.  It never reads a reference proof or feeds verifier
results back into ranking.
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

FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
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


def load_tasks(manifest_path: Path, packet: dict, expected_manifest_sha256: str):
    manifest_bytes = manifest_path.read_bytes()
    if sha(manifest_bytes) != expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(manifest_bytes)
    tasks = {}
    for source in manifest.get("tasks", []):
        if source.get("split") != "official_test":
            continue
        # Explicitly select scaffold identity and source bytes only.  This is
        # intentional: the scorer has no code path to a reference response.
        tasks[source["id"]] = {key: source[key] for key in (
            "id", "prefix", "suffix", "theorem_name", "dependencies",
            "source_sha256", "category")}
        if sha((source["prefix"] + source["suffix"]).encode()) != source["source_sha256"]:
            raise ValueError("official source reconstruction mismatch")
    if len(tasks) != 119 or set(tasks) != {row["id"] for row in packet["rows"]}:
        raise ValueError("official 119 task coverage mismatch")
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
            if (not isinstance(index, int) or
                    not 0 <= index < len(proposal_by_task[task_id])):
                raise ValueError("ranking index outside frozen candidate set")
            if index in seen or row.get("candidate") != proposal_by_task[task_id][index]:
                raise ValueError("ranking candidate mismatch")
            if not isinstance(row.get("mean_logp"), (int, float)):
                raise ValueError("missing numeric candidate score")
            seen.add(index)
            checked.append(row)
        if len(seen) != len(proposal_by_task[task_id]):
            raise ValueError("incomplete task ranking cannot receive credit")
        normalized[task_id] = sorted(
            checked, key=lambda row: (-row["mean_logp"], row["candidate_index"]))
    return normalized


def validate_answer_free_packet(packet: dict) -> None:
    """Validate either official symbolic packet representation.

    The typed candidate-rank packet deliberately preserves the same frozen
    task/candidate boundary as the original packet, but adds typed agenda
    metadata and records the hash of its answer-free parent packet.
    """
    packet_kind = packet.get("packet_kind")
    if packet_kind not in {
        "answer_free_official_symbolic_candidate_ranking",
        "answer_free_typed_candidate_rank_official",
    }:
        raise ValueError("unsupported or answer-bearing packet")
    if packet_kind == "answer_free_official_symbolic_candidate_ranking":
        expected_flags = {
            "packet_kind": packet_kind,
            "split": "official_test", "denominator": 119,
            "protected_evaluation": True, "reference_fragment_used": False,
            "reference_fragment_exported": False, "proof_bodies_exported": False,
            "successful_candidates_exported": False, "generated_feedback": False,
            "training_executed": False, "parameter_updates": 0,
            "tlaps_executed": False, "proof_or_quality_claim": False,
        }
    else:
        expected_flags = {
            "packet_kind": packet_kind,
            "split": "official_test", "denominator": 119,
            "reference_fragment_used": False,
            "reference_fragment_exported": False, "proof_bodies_exported": False,
            "successful_candidates_exported": False, "generated_feedback": False,
            "training_executed": False, "parameter_updates": 0,
            "tlaps_executed": False, "proof_or_quality_claim": False,
            "gate_claim": False, "development_targets_exported": False,
            "official_packet_sha256":
                "f40539a20e449ad63b8244e85eff33c8022402df11a84e8228b71ccbfeae11b5",
            "source_manifest_sha256":
                "3380cf37c7311466ea7762662d55866839b3c3620ce73fb8d7ad209befe6de1d",
        }
    if any(packet.get(key) != value for key, value in expected_flags.items()):
        raise ValueError("unsupported or answer-bearing packet")


def score(packet_path: Path, manifest_path: Path, rankings_path: Path, output: Path,
          expected_packet_sha256: str, expected_manifest_sha256: str,
          expected_checkpoint_sha256: str | None = None,
          timeout: int = 5, seconds: int = 900) -> dict:
    packet_bytes = packet_path.read_bytes()
    if sha(packet_bytes) != expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_bytes)
    reject_keys(packet)
    validate_answer_free_packet(packet)
    if len(packet.get("rows", [])) != 119:
        raise ValueError("fixed official denominator required")
    tasks = load_tasks(manifest_path, packet, expected_manifest_sha256)
    rankings_path = Path(rankings_path)
    ranking_data = json.loads(rankings_path.read_bytes())
    worker_config = json.loads((rankings_path.parent / "config.json").read_bytes())
    if packet.get("packet_kind") == "answer_free_typed_candidate_rank_official":
        if (worker_config.get("packet_sha256") != packet["official_packet_sha256"] or
                worker_config.get("typed_packet_sha256") != sha(packet_bytes)):
            raise ValueError("ranking receipt is not bound to the typed packet and parent")
    elif worker_config.get("packet_sha256") != sha(packet_bytes):
        raise ValueError("ranking receipt is not bound to this packet")
    if expected_checkpoint_sha256 and worker_config.get("checkpoint_sha256") != expected_checkpoint_sha256:
        raise ValueError("worker did not bind exact parent checkpoint")
    normalized = normalize_rankings(ranking_data, packet)

    if not 1 <= timeout <= 5 or not 0 < seconds <= 900:
        raise ValueError("checker budget outside the frozen bound")
    output.mkdir(parents=True, exist_ok=False)
    checks = []
    started = time.monotonic()
    from harness.proof_fragment_check import certify_fragment
    with (output / "checks.jsonl").open("x") as stream:
        for task_id, task in tasks.items():
            ranked = normalized.get(task_id)
            if not ranked:
                continue
            for rank, row in enumerate(ranked, 1):
                if time.monotonic() - started > seconds - timeout:
                    break
                result = certify_fragment(
                    task["prefix"], row["candidate"], task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task["dependencies"]),
                    work_root=output / "checks" / task_id / str(rank),
                    timeout=timeout)
                result.update(task=task_id, category=task["category"], rank=rank,
                              candidate_index=row["candidate_index"],
                              candidate=row["candidate"],
                              mean_logp=row["mean_logp"])
                checks.append(result)
                stream.write(json.dumps(result) + "\n")
                stream.flush()
                if result["certified"]:
                    break

    ranked_tasks = set(normalized)
    certified = {row["task"] for row in checks if row["certified"]}
    top1 = {row["task"] for row in checks
            if row["certified"] and row["rank"] == 1}
    summary = {
        "requested_tasks": 119,
        "fully_ranked_tasks": len(ranked_tasks),
        "measured_tasks": len({row["task"] for row in checks}),
        "certified_tasks_top4": len(certified),
        "top1_verified": len(top1),
        "checker_attempts": len(checks),
        "checker": "strict uncached TLAPS --strict --nofp",
        "reference_fragment_used": False,
        "training_executed": False,
        "repair_or_reward": False,
        "quality_claim": False,
        "gate_claim": False,
        "denominator_fixed": True,
        "method": "exact-parent conditional rank-1 action, with bounded top-4 strict certification",
        "elapsed_seconds": time.monotonic() - started,
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
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    print(json.dumps(score(args.packet, args.manifest, args.rankings, args.output,
                           args.expected_packet_sha256, args.expected_manifest_sha256,
                           args.expected_checkpoint_sha256, args.timeout, args.seconds),
                   indent=2))


if __name__ == "__main__":
    main()
