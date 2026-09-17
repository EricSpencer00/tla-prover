#!/usr/bin/env python3
"""Search the frozen answer-free symbolic action lattice on protected rows.

This is a gate-oriented renderer diagnostic, not a model-quality claim.  It
reads only immutable source boundaries and dependency files for the two
protected tasks, enumerates the repository's bounded symbolic proposals, and
checks every proposal with fresh strict uncached TLAPS.  Reference fragments,
model outputs, rewards, repair and protected feedback are never read.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import time
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PROTECTED_IDS = ("crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof", "crdt-sum-zero-proof")
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}
SAFE_AUDIT_FLAGS = {
    "reference_fragments_used", "reference_fragment_used", "training_executed",
    "parameter_updates", "proof_or_quality_claim", "gate_claim",
}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def reject_forbidden(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS or (key in SAFE_AUDIT_FLAGS and child not in (False, 0)):
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_forbidden(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_forbidden(child, f"{path}[{index}]")


def load_tasks(manifest_path: Path) -> tuple[dict[str, dict], bytes]:
    raw = manifest_path.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("protected manifest hash mismatch")
    manifest = json.loads(raw)
    tasks = {}
    for source in manifest.get("tasks", []):
        if source.get("id") in PROTECTED_IDS:
            # Explicit allowlist: reference_fragment is deliberately not read.
            tasks[source["id"]] = {
                key: source[key] for key in
                ("id", "split", "prefix", "suffix", "theorem_name", "target_goal", "dependencies")
            }
    if tuple(sorted(tasks)) != tuple(sorted(PROTECTED_IDS)):
        raise ValueError("protected task membership mismatch")
    for task in tasks.values():
        if task["split"] != "development":
            raise ValueError("protected tasks must remain development-only")
    return tasks, raw


def build_candidates(task: dict) -> list[str]:
    dependencies = tuple(Path(path) for path in task.get("dependencies", []))
    texts = [path.read_text() for path in dependencies]
    library_paths = libraries(task["prefix"], texts, TLA_LIBRARY.split(":"))
    candidates, _ = proposals(
        task["prefix"], task["theorem_name"],
        task.get("target_goal", ""),
        texts, [path.read_text() for path in library_paths])
    candidates = list(dict.fromkeys(candidates))
    if not 1 <= len(candidates) <= 32:
        raise ValueError(f"proposal width outside bound for {task['id']}")
    if any(not candidate.startswith("BY ") or "AXIOM" in candidate or "OMITTED" in candidate
           for candidate in candidates):
        raise ValueError(f"unsafe symbolic proposal in {task['id']}")
    return candidates


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if not 1 <= args.timeout <= 15 or not 60 <= args.seconds <= 900:
        parser.error("bounded strict-TLAPS budget required")
    tasks, manifest_bytes = load_tasks(args.manifest)
    candidates = {task_id: build_candidates(tasks[task_id]) for task_id in PROTECTED_IDS}
    expected_checks = sum(len(values) for values in candidates.values())
    args.output.mkdir(parents=True)
    (args.output / "candidates.json").write_text(json.dumps(candidates, indent=2) + "\n")
    checks = []
    started = time.monotonic()
    for task_id in PROTECTED_IDS:
        task = tasks[task_id]
        for candidate_index, candidate in enumerate(candidates[task_id]):
            if time.monotonic() + args.timeout > started + args.seconds:
                raise TimeoutError("strict-TLAPS budget exhausted before fixed denominator")
            result = certify_fragment(
                task["prefix"], candidate, task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                work_root=args.output / "checks" / task_id / str(candidate_index),
                timeout=args.timeout,
            )
            checks.append({
                "task": task_id, "candidate_index": candidate_index,
                "candidate": candidate, "certified": bool(result["certified"]),
                "status": result["status"], "proved": result["proved"],
                "total": result["total"], "seconds": result["seconds"],
                "sha256": result["sha256"],
            })
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "checks.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in checks))
    certified = [row for row in checks if row["certified"]]
    summary = {
        "kind": "protected_answer_free_symbolic_renderer_search_v1",
        "manifest_sha256": sha(manifest_bytes), "protected_rows": list(PROTECTED_IDS),
        "candidate_denominator": expected_checks, "strict_checks": len(checks),
        "certified_candidates": len(certified),
        "certified_by_task": {task_id: sum(row["certified"] for row in checks if row["task"] == task_id)
                              for task_id in PROTECTED_IDS},
        "reference_fragment_used": False, "protected_feedback_used": False,
        "repair_or_reward_used": False, "training_executed": False,
        "parameter_updates": 0, "quality_claim": False, "proof_claim": False,
        "gate_claim": False, "checker": "fresh strict uncached TLAPS",
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
