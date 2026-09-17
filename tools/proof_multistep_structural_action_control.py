#!/usr/bin/env python3
"""Evaluate a pre-registered answer-free structural ordering control.

The control prefers explicit SMT definitions, then explicit definitions, then
other SMT actions, then the bare SMT action.  It uses only candidate text and
never reads proof answers, verifier outcomes, rewards, or feedback.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment


TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def reject_keys(value, path="document"):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def structural_key(candidate: str, candidate_index: int) -> tuple[int, int]:
    """Return the fixed, answer-free structural priority."""
    if candidate.startswith("BY SMT DEF "):
        tier = 0
    elif candidate.startswith("BY DEF "):
        tier = 1
    elif candidate.startswith("BY SMT") and candidate != "BY SMT":
        tier = 2
    elif candidate == "BY SMT":
        tier = 3
    else:
        tier = 4
    return tier, candidate_index


def visible_statement_names(prompt: str) -> set[str]:
    context = prompt.split("Visible statement-only context", 1)[-1]
    return set(re.findall(r"(?m)^([A-Za-z_][A-Za-z0-9_]*)\s*==", context))


def visible_structural_key(candidate: str, candidate_index: int,
                           visible_names: set[str]) -> tuple[int, int, int]:
    identifiers = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", candidate))
    overlap = len(identifiers & visible_names)
    tier, index = structural_key(candidate, candidate_index)
    return -overlap, tier, index


def evaluate(packet_path: Path, manifest_path: Path, output: Path,
             expected_packet_sha256: str, expected_manifest_sha256: str,
             timeout: int = 5, seconds: int = 900,
             mode: str = "structural") -> dict:
    packet_bytes = packet_path.read_bytes()
    manifest_bytes = manifest_path.read_bytes()
    if sha(packet_bytes) != expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    if sha(manifest_bytes) != expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    packet = json.loads(packet_bytes)
    manifest = json.loads(manifest_bytes)
    reject_keys(packet)
    packet_kind = packet.get("packet_kind")
    if packet_kind == "answer_free_multistep_symbolic_action_coverage":
        denominator, split, expected_ids = 17, "train", TRAIN_IDS
    elif packet_kind == "answer_free_official_symbolic_candidate_ranking":
        denominator, split, expected_ids = 119, "official_test", None
    else:
        raise ValueError("unsupported packet kind")
    if (packet.get("split") != split or packet.get("denominator") != denominator or
            len(packet.get("rows", [])) != denominator):
        raise ValueError("unsupported packet or denominator")
    tasks = {task["id"]: task for task in manifest["tasks"]
             if task.get("split") == split}
    packet_ids = {row["id"] for row in packet["rows"]}
    if len(tasks) != denominator or set(tasks) != packet_ids:
        raise ValueError("frozen task membership mismatch")
    if expected_ids is not None and packet_ids != expected_ids:
        raise ValueError("frozen 17-row task membership mismatch")

    ranked = {}
    for row in packet["rows"]:
        proposals = row["candidate_proposals"]
        visible_names = visible_statement_names(row["prompt"])
        key = (structural_key if mode == "structural" else
               lambda candidate, index: visible_structural_key(
                   candidate, index, visible_names))
        ranked[row["id"]] = [
            {"candidate_index": index, "candidate": proposals[index],
             "structural_key": list(key(proposals[index], index)),
             "visible_overlap": len(
                 set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", proposals[index])) &
                 visible_names)}
            for index in sorted(range(len(proposals)),
                                key=lambda i: key(proposals[i], i))
        ]

    output.mkdir(parents=True, exist_ok=False)
    (output / "rankings.json").write_text(json.dumps(ranked, indent=2) + "\n")
    started = time.monotonic()
    checks = []
    certified = set()
    with (output / "checks.jsonl").open("x") as stream:
        for packet_row in packet["rows"]:
            task_id = packet_row["id"]
            task = tasks[task_id]
            for rank, selection in enumerate(ranked[task_id], 1):
                if time.monotonic() + timeout > started + seconds:
                    break
                candidate_index = selection["candidate_index"]
                candidate = selection["candidate"]
                dependencies = tuple(Path(path) for path in task.get("dependencies", []))
                for dependency in dependencies:
                    expected = task.get("dependency_sha256", {}).get(str(dependency))
                    if expected and sha(dependency.read_bytes()) != expected:
                        raise ValueError(f"dependency hash mismatch: {task_id}")
                result = certify_fragment(
                    task["prefix"], candidate, task["suffix"],
                    theorem_name=task["theorem_name"], dependencies=dependencies,
                    work_root=output / "checks" / task_id / str(rank), timeout=timeout)
                record = {
                    "task": task_id, "rank": rank,
                    "candidate_index": candidate_index, "candidate": candidate,
                    **result,
                }
                checks.append(record)
                stream.write(json.dumps(record) + "\n")
                stream.flush()
                if result["certified"]:
                    certified.add(task_id)
                    break

    summary = {
        "requested_tasks": denominator,
        "measured_tasks": len({row["task"] for row in checks}),
        "certified_tasks": len(certified),
        "top1_certified_tasks": sum(row["certified"] and row["rank"] == 1
                                     for row in checks),
        "checker_attempts": len(checks),
        "candidate_width": max(len(row["candidate_proposals"]) for row in packet["rows"]),
        "ordering": ("SMT+DEF, DEF, other SMT, bare SMT; candidate index tie-break"
                     if mode == "structural" else
                     "visible statement-name overlap, then structural order; candidate index tie-break"),
        "packet_sha256": expected_packet_sha256,
        "manifest_sha256": expected_manifest_sha256,
        "reference_fragment_used": False,
        "training_executed": False,
        "parameter_updates": 0,
        "model_executed": False,
        "reward_or_feedback": False,
        "proof_or_quality_claim": False,
        "gate_claim": False,
        "denominator_fixed": True,
        "elapsed_seconds": time.monotonic() - started,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    parser.add_argument("--mode", choices=("structural", "visible"), default="structural")
    args = parser.parse_args()
    if not 1 <= args.timeout <= 10 or not 30 <= args.seconds <= 900:
        parser.error("bounded timeout/seconds required")
    print(json.dumps(evaluate(args.packet, args.manifest, args.output,
                              args.expected_packet_sha256,
                              args.expected_manifest_sha256,
                              args.timeout, args.seconds, args.mode), indent=2))


if __name__ == "__main__":
    main()
