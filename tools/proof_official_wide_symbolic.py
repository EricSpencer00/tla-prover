#!/usr/bin/env python3
"""Run a wider answer-free symbolic action lattice on official 119.

This is a local diagnostic.  It consumes only the prepared theorem
prefix/suffix bytes and frozen symbolic candidates; it never reads reference
fragments, uses a model, trains, or feeds verifier output back into search.
Unlike the historical evaluator, it does not require the original external
source checkout because the prepared manifest already binds reconstructed
source bytes with ``source_sha256``.
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


def reject_keys(value, path="manifest") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing key: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def load_manifest(path: Path) -> tuple[dict, list[dict]]:
    raw = path.read_bytes()
    manifest = json.loads(raw)
    reject_keys(manifest)
    tasks = manifest.get("tasks", [])
    if (len(tasks) != 119 or len({task.get("id") for task in tasks}) != 119 or
            manifest.get("reference_fragments_used") is not False or
            manifest.get("training") is not False or
            manifest.get("legacy_retrieval_index_used") is not False):
        raise ValueError("exact answer-free official 119 manifest required")
    for task in tasks:
        if task.get("split") != "official_test":
            raise ValueError("official split mismatch")
        if sha((task["prefix"] + task["suffix"]).encode()) != task["source_sha256"]:
            raise ValueError(f"source reconstruction mismatch: {task['id']}")
        candidates = task.get("symbolic_candidates", [])
        if not candidates or len(set(candidates)) != len(candidates):
            raise ValueError(f"candidate set mismatch: {task['id']}")
        if any(candidate != "OBVIOUS" and not candidate.startswith("BY ")
               for candidate in candidates):
            raise ValueError(f"unsafe candidate: {task['id']}")
    return manifest, tasks


def evaluate(manifest_path: Path, output: Path, attempts: int = 8,
             timeout: int = 5, seconds: int = 900) -> dict:
    if not 1 <= attempts <= 8 or not 1 <= timeout <= 5 or not 0 < seconds <= 900:
        raise ValueError("bounded diagnostic budget exceeded")
    raw = manifest_path.read_bytes()
    manifest, tasks = load_manifest(manifest_path)
    output.mkdir(parents=True, exist_ok=False)
    (output / "manifest.json").write_bytes(raw)
    config = {
        "schema_version": 1,
        "method": "wider deterministic answer-free symbolic action lattice",
        "manifest_sha256": sha(raw),
        "requested_tasks": 119,
        "attempts_per_task": attempts,
        "timeout_per_check": timeout,
        "seconds": seconds,
        "reference_fragment_used": False,
        "training_executed": False,
        "tlaps_executed": True,
        "model_used": False,
        "reward_or_feedback_used": False,
        "denominator_fixed": True,
        "quality_claim": False,
        "gate_claim": False,
    }
    (output / "config.json").write_text(json.dumps(config, indent=2) + "\n")
    from harness.proof_fragment_check import certify_fragment
    rows = []
    statuses = {task["id"]: "unattempted_budget" for task in tasks}
    started = time.monotonic()
    with (output / "rows.jsonl").open("x") as stream:
        for task in tasks:
            candidates = task["symbolic_candidates"][:attempts]
            for attempt, candidate in enumerate(candidates):
                if time.monotonic() - started > seconds - timeout:
                    break
                result = certify_fragment(
                    task["prefix"], "\n" + candidate, task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                    work_root=output / "checks" / task["id"] / str(attempt),
                    timeout=timeout)
                row = dict(task=task["id"], category=task["category"], attempt=attempt,
                           candidate=candidate, source_sha256=task["source_sha256"], **result)
                rows.append(row)
                stream.write(json.dumps(row) + "\n")
                stream.flush()
                statuses[task["id"]] = "certified" if result["certified"] else result["status"]
                if result["certified"]:
                    break
    passed = {row["task"] for row in rows if row["certified"]}
    summary = {
        "requested_tasks": 119,
        "attempted_tasks": len({row["task"] for row in rows}),
        "certified_tasks": len(passed),
        "attempts": len(rows),
        "unattempted_tasks": 119 - len({row["task"] for row in rows}),
        "task_statuses": statuses,
        "elapsed_seconds": time.monotonic() - started,
        **config,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--attempts", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    print(json.dumps(evaluate(args.manifest, args.output, args.attempts,
                               args.timeout, args.seconds), indent=2))


if __name__ == "__main__":
    main()
