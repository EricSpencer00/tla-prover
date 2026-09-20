#!/usr/bin/env python3
"""Freeze an answer-free symbolic-candidate RL packet for one bounded run.

Candidates are derived only from immutable theorem prefixes and explicitly
hashed dependency/library statements.  The reference fragments are used only
for a local leakage audit and are never copied into the packet.  This module
does not load a model, assign verifier rewards, or run CUDA.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.proof_candidate_rl import freeze_train, validate_frozen_tasks
from harness.proof_fragment_check import validate_fragment

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _copy_path(source: Path, root: Path, bucket: str, paths: dict[str, str]) -> str:
    source = source.resolve()
    key = str(source)
    if key in paths:
        return paths[key]
    if not source.is_file():
        raise ValueError(f"missing frozen source: {source}")
    destination = root / "runtime" / bucket / f"{sha(source.read_bytes())[:16]}-{source.name}"
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)
    # Serialize stage-relative paths.  The same frozen packet must be usable
    # after upload; absolute workstation paths would make the remote worker
    # fail before model load.
    paths[key] = str(destination.relative_to(root))
    return paths[key]


def _rewrite_paths(tasks: list[dict], output: Path) -> list[dict]:
    rewritten = json.loads(json.dumps(tasks))
    paths: dict[str, str] = {}
    for task in rewritten:
        dependencies = []
        dependency_hashes = {}
        for path in task["dependencies"]:
            mapped = _copy_path(Path(path), output, "dependencies", paths)
            dependencies.append(mapped)
            dependency_hashes[mapped] = task["dependency_sha256"][path]
        task["dependencies"] = dependencies
        task["dependency_sha256"] = dependency_hashes
        libraries = {}
        for path, expected in task["context"]["library_sha256"].items():
            mapped = _copy_path(Path(path), output, "libraries", paths)
            libraries[mapped] = expected
        task["context"]["library_sha256"] = libraries
    return rewritten


def build(manifest: Path, output: Path, *, candidates: int = 8,
          step_candidates: bool = True, parent_sha256: str = PARENT_SHA256) -> dict:
    raw = manifest.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("exact frozen multistep manifest required")
    if parent_sha256 != PARENT_SHA256:
        raise ValueError("unexpected parent identity")
    tasks = freeze_train(raw, candidates, step_candidates=step_candidates)
    validate_frozen_tasks(tasks)
    manifest_data = json.loads(raw)
    by_id = {task["id"]: task for task in manifest_data["tasks"]}
    for task in tasks:
        reference = by_id[task["id"]]["reference_fragment"]
        if reference in json.dumps(task, ensure_ascii=False):
            raise ValueError(f"reference bytes leaked into frozen task: {task['id']}")
        for candidate in task["candidates"]:
            validate_fragment(task["prefix"], candidate, task["suffix"], task["theorem_name"])

    output.mkdir(parents=True, exist_ok=False)
    rewritten = _rewrite_paths(tasks, output)
    validate_frozen_tasks(rewritten)
    frozen_path = output / "frozen.json"
    frozen_path.write_text(json.dumps(rewritten, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "schema": 1,
        "kind": "answer_free_symbolic_candidate_rl_admission",
        "manifest_sha256": sha(raw),
        "parent_sha256": parent_sha256,
        "frozen_sha256": sha(frozen_path.read_bytes()),
        "train_tasks": len(rewritten),
        "candidates_per_task": sorted({len(task["candidates"]) for task in rewritten}),
        "candidate_contract_validated": sum(len(task["candidates"]) for task in rewritten),
        "development_targets_exported": False,
        "reference_fragment_used": False,
        "reference_fragment_exported": False,
        "verifier_feedback_used": False,
        "repair_used": False,
        "reward_assigned": False,
        "model_loaded": False,
        "cuda_touched": False,
        "optimizer_updates": 0,
        "official_rows_used": False,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
        "scope": "CPU packet/path/contract admission only; strict TLAPS rewards are assigned later by the worker to sampled TRAIN candidates",
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--candidates", type=int, default=8)
    parser.add_argument("--no-step-candidates", action="store_true")
    args = parser.parse_args()
    if not 2 <= args.candidates <= 8:
        parser.error("candidate bound must be 2..8")
    print(json.dumps(build(args.manifest, args.output, candidates=args.candidates,
                           step_candidates=not args.no_step_candidates), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
