#!/usr/bin/env python3
"""Measure one additional answer-free candidate on every baseline failure."""
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


def reject_keys(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing key: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def load_frozen(manifest_path: Path, baseline_path: Path):
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    reject_keys(manifest)
    tasks = manifest.get("tasks", [])
    if (len(tasks) != 119 or len({task.get("id") for task in tasks}) != 119 or
            manifest.get("reference_fragments_used") is not False or
            manifest.get("training") is not False):
        raise ValueError("exact answer-free official 119 manifest required")
    for task in tasks:
        if task.get("split") != "official_test" or sha(
                (task["prefix"] + task["suffix"]).encode()) != task["source_sha256"]:
            raise ValueError(f"frozen source mismatch: {task['id']}")
    baseline = json.loads((baseline_path.parent / "summary.json").read_bytes())
    baseline_rows = [json.loads(line) for line in baseline_path.read_text().splitlines()]
    passed = {row["task"] for row in baseline_rows if row.get("certified")}
    attempted = {row["task"] for row in baseline_rows}
    if len(attempted) != 119 or baseline.get("requested_tasks") != 119:
        raise ValueError("baseline must cover the fixed 119 population")
    return manifest_bytes, tasks, passed


def evaluate(manifest_path: Path, baseline_path: Path, output: Path,
             candidate_index: int = 4, timeout: int = 5, seconds: int = 900):
    if candidate_index < 4 or candidate_index > 7 or not 1 <= timeout <= 5 or not 0 < seconds <= 900:
        raise ValueError("tail diagnostic budget outside the frozen bound")
    manifest_bytes, tasks, baseline_passed = load_frozen(manifest_path, baseline_path)
    output.mkdir(parents=True, exist_ok=False)
    (output / "manifest.json").write_bytes(manifest_bytes)
    config = {
        "schema_version": 1,
        "method": "single additional deterministic answer-free symbolic candidate",
        "manifest_sha256": sha(manifest_bytes),
        "baseline_sha256": sha(baseline_path.read_bytes()),
        "candidate_index": candidate_index,
        "requested_tasks": 119,
        "baseline_certified_tasks": len(baseline_passed),
        "timeout_per_check": timeout,
        "seconds": seconds,
        "reference_fragment_used": False,
        "training_executed": False,
        "model_used": False,
        "reward_or_feedback_used": False,
        "denominator_fixed": True,
        "quality_claim": False,
        "gate_claim": False,
    }
    (output / "config.json").write_text(json.dumps(config, indent=2) + "\n")
    from harness.proof_fragment_check import certify_fragment
    rows = []
    started = time.monotonic()
    with (output / "rows.jsonl").open("x") as stream:
        for task in tasks:
            if task["id"] in baseline_passed:
                continue
            candidates = task.get("symbolic_candidates", [])
            if len(candidates) <= candidate_index:
                row = dict(task=task["id"], candidate_index=candidate_index,
                           status="no_candidate", certified=False)
            elif time.monotonic() - started > seconds - timeout:
                row = dict(task=task["id"], candidate_index=candidate_index,
                           status="unmeasured_budget", certified=False)
            else:
                candidate = candidates[candidate_index]
                result = certify_fragment(
                    task["prefix"], "\n" + candidate, task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                    work_root=output / "checks" / task["id"], timeout=timeout)
                row = dict(task=task["id"], candidate_index=candidate_index,
                           candidate=candidate, source_sha256=task["source_sha256"], **result)
            rows.append(row)
            stream.write(json.dumps(row) + "\n")
            stream.flush()
    new_passes = {row["task"] for row in rows if row.get("certified")}
    measured = {row["task"] for row in rows if row.get("status") not in (
        "unmeasured_budget", "no_candidate")}
    summary = {
        **config,
        "measured_tail_tasks": len(measured),
        "new_certified_tasks": len(new_passes),
        "union_certified_tasks": len(baseline_passed | new_passes),
        "baseline_failed_tasks": 119 - len(baseline_passed),
        "unmeasured_tail_tasks": 119 - len(baseline_passed) - len(measured) - sum(
            row.get("status") == "no_candidate" for row in rows),
        "no_candidate_tasks": sum(row.get("status") == "no_candidate" for row in rows),
        "elapsed_seconds": time.monotonic() - started,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--baseline", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--candidate-index", type=int, default=4)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    print(json.dumps(evaluate(args.manifest, args.baseline, args.output,
                               args.candidate_index, args.timeout, args.seconds), indent=2))


if __name__ == "__main__":
    main()
