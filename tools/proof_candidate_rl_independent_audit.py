#!/usr/bin/env python3
"""Independently audit a finite candidate-RL result without loading a model."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


UNKNOWN_STATUSES = {
    "timeout", "infrastructure_error", "unrecognized_output",
    "no_obligations", "contract_reject",
}
INFRASTRUCTURE = re.compile(
    r"(?im)^.*(?:command not found|No such file or directory|Permission denied|"
    r"Cannot find module|could not find module|out of memory|timed out|timeout|"
    r"backend .*not found|backend .*unavailable|exception|segmentation fault|interrupted).*$"
)
STRICT_REJECT = re.compile(r"(?m)^\[ERROR\]: [1-9]\d*/\d+ obligations? failed\.$")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def independent_reward(result: dict):
    """Conservative copy of the public reward contract, based on raw output."""
    if result.get("timed_out") or result.get("status") in UNKNOWN_STATUSES:
        return None
    output = result.get("output", "")
    if INFRASTRUCTURE.search(output):
        return None
    if (result.get("certified") is True and result.get("status") == "pass"
            and result.get("returncode") == 0 and result.get("proved", 0) > 0
            and result.get("proved") == result.get("total")):
        return 1.0
    if result.get("status") not in {"verifier_reject", "error"}:
        return None
    if (STRICT_REJECT.search(output)
            and "[ERROR]: Could not prove or check:" in output):
        return 0.0
    if re.search(r'(?m)^Error: Operator "[^"]+" not found\s*$', output):
        return 0.0
    return None


def audit(stage: Path, result: Path, *, expected_checkpoint: str | None = None) -> dict:
    tasks = json.loads((stage / "frozen.json").read_text())
    summary = json.loads((result / "summary.json").read_text())
    rows = [json.loads(line) for line in (result / "groups.jsonl").read_text().splitlines()]
    ids = {task["id"] for task in tasks}
    if len(tasks) != 17 or not ids:
        raise ValueError("unexpected frozen TRAIN population")
    if any(task.get("context", {}).get("reference_fragment_used") is not False
           for task in tasks):
        raise ValueError("frozen packet does not attest answer-free context")
    if any(row.get("task") not in ids for row in rows):
        raise ValueError("ledger task escaped frozen TRAIN population")
    if len(rows) != summary["groups"] or summary["groups"] != summary["requested_groups"]:
        raise ValueError("group denominator mismatch")

    actual_checks = []
    status_counts = {}
    mismatches = []
    for row in rows:
        if len(row.get("rewards", [])) != 4 or len(row.get("checks", [])) != 4:
            raise ValueError("sample/group denominator mismatch")
        for check in row["checks"]:
            status_counts[check.get("status")] = status_counts.get(check.get("status"), 0) + 1
            if "memoized_from" in check:
                continue
            actual_checks.append(check)
            expected = independent_reward(check)
            if expected != check.get("reward"):
                mismatches.append({"status": check.get("status"),
                                   "stored": check.get("reward"),
                                   "independent": expected})
    if mismatches:
        raise ValueError(f"worker reward mismatch: {mismatches[:3]}")
    updates = sum(bool(row.get("updated")) for row in rows)
    if updates != 0 or summary.get("updates") != 0 or summary.get("parameter_delta_l2") != 0.0:
        raise ValueError("candidate-RL run is not the admitted zero-update result")
    if summary.get("development_responses_forwarded") != 0:
        raise ValueError("development response leaked into TRAIN run")
    if summary.get("checker_attempts") != len(actual_checks):
        raise ValueError("checker-attempt denominator mismatch")
    checkpoint = result / "policy_optimizer.pt"
    checkpoint_sha = sha(checkpoint)
    if expected_checkpoint and checkpoint_sha != expected_checkpoint:
        raise ValueError("checkpoint hash mismatch")
    return {
        "schema": 1,
        "groups": len(rows),
        "requested_groups": summary["requested_groups"],
        "train_tasks": len(tasks),
        "attempted_train_tasks": summary.get("attempted_train_tasks"),
        "sampled_attempts": sum(len(row["rewards"]) for row in rows),
        "checker_attempts": len(actual_checks),
        "status_counts": status_counts,
        "unknown_rewards": sum(check.get("reward") is None for check in actual_checks),
        "strict_reject_rewards": sum(check.get("reward") == 0.0 for check in actual_checks),
        "positive_rewards": sum(check.get("reward") == 1.0 for check in actual_checks),
        "updates": updates,
        "parameter_delta_l2": summary["parameter_delta_l2"],
        "reload_tensors_exact": summary["reload_tensors_exact"],
        "reload_logits_exact": summary["reload_logits_exact"],
        "checkpoint_sha256": checkpoint_sha,
        "development_responses_forwarded": summary["development_responses_forwarded"],
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--result", type=Path, required=True)
    parser.add_argument("--expected-checkpoint-sha256")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    audited = audit(args.stage, args.result,
                    expected_checkpoint=args.expected_checkpoint_sha256)
    args.output.write_text(json.dumps(audited, indent=2) + "\n")
    print(json.dumps(audited, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
