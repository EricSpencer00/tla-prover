#!/usr/bin/env python3
"""Build and verify a train-only strict-teacher contrastive selector packet.

The packet intentionally contains exact proof anchors only for the immutable
TRAIN split.  DEVELOPMENT targets never enter the packet.  The model-facing
signal is deterministic contrastive likelihood over one strict-certified
teacher candidate and answer-free hard negatives; it is not sampled reward
RL and it cannot claim development quality.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.proof_candidate_rl import freeze_train
from tools.proof_candidate_rl_admission import _copy_path
from harness.proof_fragment_check import certify_fragment

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def target_scoped_pass(result: dict) -> bool:
    """Accept only the target-module proof line after library prelude output."""
    if result.get("returncode") != 0 or result.get("timed_out"):
        return False
    candidate = result.get("candidate_path")
    if not candidate:
        return False
    module = Path(candidate).stem
    output = result.get("output", "")
    marker = f'File "./{module}.tla"'
    if marker not in output:
        return False
    target_output = output.rsplit(marker, 1)[-1]
    if re.search(r"\b(?:failed|omitted|interrupted|error|exception)\b", target_output, re.I):
        return False
    matches = re.findall(r'^\s*(?:\[INFO\]: )?All ([1-9]\d*) obligations? proved\.?\s*$',
                         target_output, re.M)
    return len(matches) == 1


def build(manifest: Path, output: Path, *, negatives: int = 7) -> dict:
    raw = manifest.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("exact frozen multistep manifest required")
    if not 2 <= negatives <= 7:
        raise ValueError("negative candidate bound must be 2..7")
    manifest_data = json.loads(raw)
    by_id = {task["id"]: task for task in manifest_data["tasks"]}
    if len([t for t in manifest_data["tasks"] if t.get("split") == "development"]) != 4:
        raise ValueError("exact four-row DEVELOPMENT population required")
    frozen = freeze_train(raw, max(negatives + 1, 8), step_candidates=True)
    paths: dict[str, str] = {}
    output.mkdir(parents=True, exist_ok=False)
    rewritten = []
    for task in frozen:
        source = by_id[task["id"]]
        teacher = source["reference_fragment"]
        candidates = [teacher]
        for candidate in task["candidates"]:
            if candidate not in candidates and len(candidates) < negatives + 1:
                candidates.append(candidate)
        if len(candidates) != negatives + 1:
            raise ValueError(f"candidate population incomplete: {task['id']}")
        dependencies = []
        dependency_hashes = {}
        for path in task["dependencies"]:
            mapped = _copy_path(Path(path), output, "dependencies", paths)
            dependencies.append(mapped)
            dependency_hashes[mapped] = task["dependency_sha256"][path]
        libraries = {}
        for path, expected in task["context"]["library_sha256"].items():
            mapped = _copy_path(Path(path), output, "libraries", paths)
            libraries[mapped] = expected
        row = {
            "id": task["id"], "prefix": task["prefix"], "suffix": task["suffix"],
            "theorem_name": task["theorem_name"], "target_goal": task["target_goal"],
            "dependencies": dependencies, "dependency_sha256": dependency_hashes,
            "context": {**task["context"], "library_sha256": libraries,
                         "teacher_anchor_train_only": True},
            "prompt": task["prompt"], "candidates": candidates,
            "teacher_candidate_index": 0,
            "candidate_contract": "strict_teacher_anchor_plus_answer_free_hard_negatives",
            "development_target_exported": False,
        }
        if teacher not in row["candidates"]:
            raise AssertionError("teacher anchor was not serialized")
        rewritten.append(row)
    packet = output / "packet.json"
    packet.write_text(json.dumps(rewritten, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "schema": 1,
        "kind": "train_only_strict_teacher_contrastive_selector_admission",
        "manifest_sha256": sha(raw),
        "parent_sha256": PARENT_SHA256,
        "packet_sha256": sha(packet.read_bytes()),
        "train_tasks": len(rewritten),
        "candidates_per_task": sorted({len(row["candidates"]) for row in rewritten}),
        "teacher_anchor_count": len(rewritten),
        "negative_candidate_count": len(rewritten) * negatives,
        "teacher_strict_verified": False,
        "development_targets_exported": False,
        "development_reference_bytes_exported": False,
        "verifier_feedback_used": False,
        "repair_used": False,
        "model_loaded": False,
        "cuda_touched": False,
        "optimizer_updates": 0,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
        "scope": "CPU packet admission only; TRAIN teacher anchors are checked separately before training",
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def verify(packet_path: Path, output: Path, *, timeout: int = 10) -> dict:
    packet = json.loads(packet_path.read_text())
    if len(packet) != 17:
        raise ValueError("exact17 TRAIN tasks required")
    output.mkdir(parents=True, exist_ok=False)
    checks = []
    for row in packet:
        if row.get("development_target_exported") is not False:
            raise ValueError("DEVELOPMENT target export flag must be false")
        if row.get("teacher_candidate_index") != 0:
            raise ValueError("teacher candidate must be fixed at index zero")
        teacher = row["candidates"][0]
        result = certify_fragment(row["prefix"], teacher, row["suffix"],
                                  theorem_name=row["theorem_name"],
                                  dependencies=tuple(Path(p) for p in row["dependencies"]),
                                  work_root=output / row["id"], timeout=timeout)
        checks.append({"id": row["id"], "teacher_sha256": sha(teacher.encode()),
                       "raw_checker_status": result.get("status"),
                       "target_scoped_pass": target_scoped_pass(result), **result})
    if not all(c["target_scoped_pass"] for c in checks):
        raise ValueError("not every TRAIN teacher anchor was independently strict-certified")
    result = {
        "schema": 1, "packet_sha256": sha(packet_path.read_bytes()),
        "teacher_strict_verified": True, "train_tasks": len(checks),
        "strict_passes": sum(c["target_scoped_pass"] for c in checks),
        "development_targets_exported": False,
        "development_reference_bytes_exported": False,
        "model_loaded": False, "cuda_touched": False, "optimizer_updates": 0,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
        "checks": checks,
    }
    (output / "checks.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--packet", type=Path)
    parser.add_argument("--negatives", type=int, default=7)
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--timeout", type=int, default=10)
    args = parser.parse_args()
    if args.verify:
        if not args.packet:
            parser.error("--verify requires --packet")
        result = verify(args.packet, args.output, timeout=args.timeout)
    else:
        if not args.manifest:
            parser.error("build requires --manifest")
        result = build(args.manifest, args.output, negatives=args.negatives)
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
