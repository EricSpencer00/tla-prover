#!/usr/bin/env python3
"""Measure answer-free symbolic-action coverage on the frozen 17-row train set.

This is a pre-GPU system diagnostic for the constrained action interface.  It
derives the first four deterministic, statement-only proposals from each
training scaffold and checks them with strict uncached TLAPS.  It never reads
or exports ``reference_fragment`` or any other proof answer, and it does not
train, rank with a model, or compute a reward.
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
from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals
from tools.proof_family_manifest import goal_text


TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def target_goal(task: dict) -> str:
    goal = task.get("target_goal")
    if goal is not None:
        return goal
    if "source_path" not in task or "source_theorem_lines" not in task:
        return f"THEOREM {task['theorem_name']}"
    source_lines = Path(task["source_path"]).read_text().splitlines(keepends=True)
    begin, end = task["source_theorem_lines"]
    return goal_text("".join(source_lines[begin - 1:end]))


def answer_free_candidates(task: dict) -> tuple[list[str], dict[str, str]]:
    """Derive proposals from visible statements without touching proof fields."""
    dependencies = tuple(Path(path) for path in task.get("dependencies", []))
    expected = task.get("dependency_sha256", {})
    for dependency in dependencies:
        if sha(dependency.read_bytes()) != expected.get(str(dependency)):
            raise ValueError(f"dependency hash mismatch: {task['id']}:{dependency}")
    dependency_texts = [path.read_text() for path in dependencies]
    library_paths = libraries(task["prefix"], dependency_texts, TLA_LIBRARY.split(":"))
    goal = target_goal(task)
    candidates, context = proposals(
        task["prefix"], task["theorem_name"], goal,
        dependency_texts, [path.read_text() for path in library_paths])
    selected = list(candidates[:4])
    if len(selected) != 4 or len(set(selected)) != 4:
        raise ValueError(f"fewer than four deterministic proposals: {task['id']}")
    if any((not isinstance(candidate, str) or not candidate.startswith("BY ") or
            "OMITTED" in candidate or "AXIOM" in candidate)
           for candidate in selected):
        raise ValueError(f"unsafe proposal: {task['id']}")
    library_hashes = {
        str(path): sha(path.read_bytes()) for path in library_paths
    }
    # The context is used only to bind the answer-free retrieval provenance.
    # Do not serialize statements or any task object wholesale.
    return selected, library_hashes


def freeze(manifest_path: Path, output: Path) -> tuple[dict, dict[str, dict]]:
    raw = manifest_path.read_bytes()
    manifest = json.loads(raw)
    tasks = [task for task in manifest["tasks"] if task.get("split") == "train"]
    if {task.get("id") for task in tasks} != TRAIN_IDS or len(tasks) != 17:
        raise ValueError("exact frozen 17-row train population required")
    rows = []
    safe_tasks = {}
    for task in tasks:
        candidates, library_hashes = answer_free_candidates(task)
        goal = target_goal(task)
        prompt = (
            "Select one valid TLAPS proof action for the fixed final theorem. "
            "Return only an action beginning with OBVIOUS or BY. Do not change "
            "definitions, add axioms, emit a module, or use a reference proof.\n\n"
            f"theorem={task['theorem_name']}\n"
            f"goal={goal}\n"
            "Visible statement-only context is fixed by the local scaffold.\n"
        )
        rows.append({
            "id": task["id"],
            "split": "train",
            "theorem_name": task["theorem_name"],
            "prompt": prompt,
            "prompt_sha256": sha(prompt.encode()),
            "candidate_proposals": candidates,
            "candidate_proposals_sha256": digest(candidates),
            "source_sha256": task["source_sha256"],
            "library_sha256": library_hashes,
        })
        safe_tasks[task["id"]] = {
            "prefix": task["prefix"],
            "suffix": task["suffix"],
            "theorem_name": task["theorem_name"],
            "dependencies": tuple(Path(path) for path in task.get("dependencies", [])),
        }
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_multistep_symbolic_action_coverage",
        "manifest_sha256": sha(raw),
        "split": "train",
        "denominator": 17,
        "population": "frozen multistep train 17",
        "rows": rows,
        "reference_fragment_used": False,
        "reference_fragment_exported": False,
        "proof_bodies_exported": False,
        "successful_candidates_exported": False,
        "generated_feedback": False,
        "training_executed": False,
        "parameter_updates": 0,
        "tlaps_executed": False,
        "proof_or_quality_claim": False,
        "method": "first-four deterministic answer-free symbolic action coverage",
    }
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_text(json.dumps(packet, indent=2) + "\n")
    (output / "source-manifest-sha256.txt").write_text(sha(raw) + "\n")
    return packet, safe_tasks


def evaluate(manifest_path: Path, output: Path, timeout: int, seconds: int) -> dict:
    packet, safe_tasks = freeze(manifest_path, output)
    started = time.monotonic()
    statuses = {row["id"]: "unattempted_budget" for row in packet["rows"]}
    records = []
    with (output / "rows.jsonl").open("x") as stream:
        # Round-robin preserves fixed denominator coverage before extra tries.
        for candidate_index in range(4):
            for row in packet["rows"]:
                task_id = row["id"]
                if statuses[task_id] == "certified":
                    continue
                if time.monotonic() + timeout > started + seconds:
                    break
                task = safe_tasks[task_id]
                result = certify_fragment(
                    task["prefix"], row["candidate_proposals"][candidate_index],
                    task["suffix"], theorem_name=task["theorem_name"],
                    dependencies=task["dependencies"],
                    work_root=output / "checks" / task_id / str(candidate_index),
                    timeout=timeout,
                )
                record = {
                    "task": task_id,
                    "candidate_index": candidate_index,
                    "candidate": row["candidate_proposals"][candidate_index],
                    **result,
                }
                records.append(record)
                statuses[task_id] = "certified" if result["certified"] else result["status"]
                stream.write(json.dumps(record) + "\n")
                stream.flush()
            else:
                continue
            break
    certified = {record["task"] for record in records if record["certified"]}
    summary = {
        "requested_tasks": 17,
        "attempted_tasks": len({record["task"] for record in records}),
        "certified_tasks": len(certified),
        "top1_certified_tasks": len({record["task"] for record in records
                                     if record["certified"] and record["candidate_index"] == 0}),
        "checker_attempts": len(records),
        "candidate_width": 4,
        "elapsed_seconds": time.monotonic() - started,
        "manifest_sha256": packet["manifest_sha256"],
        "reference_fragment_used": False,
        "training_executed": False,
        "parameter_updates": 0,
        "model_executed": False,
        "reward_or_feedback": False,
        "proof_or_quality_claim": False,
        "gate_claim": False,
        "denominator_fixed": True,
        "method": "strict uncached TLAPS over answer-free deterministic first-four actions",
        "task_statuses": statuses,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if not (1 <= args.timeout <= 10 and 30 <= args.seconds <= 900):
        parser.error("bounded timeout/seconds required")
    print(json.dumps(evaluate(args.manifest, args.output, args.timeout, args.seconds), indent=2))


if __name__ == "__main__":
    main()
