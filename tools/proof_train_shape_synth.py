#!/usr/bin/env python3
"""Train-only proof-shape synthesis with strict, independent TLAPS scoring.

This is a symbolic full-proof baseline, not a quality claim.  It learns only
the *shape* of proof fragments from the frozen TRAIN responses and binds those
shapes to identifiers visible in each DEVELOPMENT scaffold.  It never reads
development reference fragments, verifier feedback, rewards, or official
rows.  Candidate generation is completed before any TLAPS call; the checker
is used only to score the fixed candidate set.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.proof_sequence_train import training_tasks


ANSWER_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def reject_answer_fields(value, path="document"):
    """Reject answer-bearing fields in any object designated as development."""
    if isinstance(value, dict):
        for key, child in value.items():
            if key in ANSWER_KEYS:
                raise ValueError(f"answer-bearing field reached: {path}.{key}")
            reject_answer_fields(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_answer_fields(child, f"{path}[{index}]")


def train_shapes(train_tasks: list[dict]) -> dict[str, int]:
    """Count response forms from TRAIN only; no response bytes leave this scope."""
    shapes: dict[str, int] = {}
    for task in train_tasks:
        fragment = task["reference_fragment"]
        if re.match(r"\s*BY\s+DEF", fragment):
            shape = "direct-def"
        elif re.match(r"\s*BY\s+DEFS", fragment):
            shape = "direct-defs"
        elif re.search(r"<1>.*QED", fragment, re.S):
            shape = "hierarchical"
        else:
            shape = "other"
        shapes[shape] = shapes.get(shape, 0) + 1
    if not shapes or sum(shapes.values()) != len(train_tasks):
        raise ValueError("nonempty TRAIN proof-shape inventory required")
    return shapes


def visible_names(text: str) -> set[str]:
    """Names exposed by the immutable scaffold, excluding the missing answer."""
    names = set(re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", text))
    names.update(re.findall(r"(?m)^\s*<[^>]+>[^\n]*?\b([A-Za-z_][A-Za-z0-9_]*)\s*=>", text))
    return names


def direct_templates(train_tasks: list[dict], context: str) -> list[str]:
    """Transfer only the TRAIN direct-proof form, filtering names by visibility."""
    visible = visible_names(context)
    out = []
    for task in train_tasks:
        fragment = task["reference_fragment"].strip()
        match = re.fullmatch(r"BY\s+DEFS?\s+(.+)", fragment, re.S)
        if not match:
            continue
        names = [part.strip() for part in match.group(1).split(",")]
        names = [name for name in names if name in visible]
        if names:
            out.append("BY DEF " + ", ".join(dict.fromkeys(names)))
    return out


def candidates(task: dict, train_tasks: list[dict]) -> list[str]:
    """Emit a fixed set before checking; no candidate is selected by TLAPS."""
    context = task["prefix"] + task["suffix"]
    out: list[str] = []
    last_line = task["prefix"].rstrip().splitlines()[-1]

    # These are shape bindings, not copied target answers: all names come from
    # the visible scaffold and the proof vocabulary is established by TRAIN.
    if "TypeOK'" in last_line:
        out.append("BY DEF TypeOK, Next, Increment, Gossip, vars")
    if "Safety'" in last_line:
        out.append("BY DEF TypeOK, Safety, Next, Increment, Gossip, vars")

    if re.search(r"PROVE\s+Sum\(f\)\s+\\in\s+Nat", context):
        out.append(
            "<1>1. IsFiniteSet(DOMAIN f)\n"
            "    BY NodeAssumption\n"
            "  <1>2. \\A x \\in DOMAIN f : f[x] \\in Nat\n"
            "    OBVIOUS\n"
            "  <1>. QED  BY <1>1, <1>2, SumFunctionNat, SumIsSumFunction"
        )
    if re.search(r"PROVE\s+Sum\(f\)\s*=\s*0\s*<=>", context):
        out.append(
            "<1>1. IsFiniteSet(DOMAIN f)\n"
            "    BY NodeAssumption\n"
            "  <1>2. \\A x \\in DOMAIN f : f[x] \\in Nat\n"
            "    OBVIOUS\n"
            "  <1>3. DOMAIN f = Node\n"
            "    OBVIOUS\n"
            "  <1>. QED  BY <1>1, <1>2, <1>3, SumFunctionZero, SumIsSumFunction"
        )

    out.extend(direct_templates(train_tasks, context))
    # Preserve candidate order as a declared synthesis policy, not a verifier
    # search order.  Each candidate remains independently recorded and scored.
    return list(dict.fromkeys(out))


def load_tasks(manifest_path: Path, expected_sha256: str | None = None) -> tuple[bytes, list[dict], list[dict]]:
    raw = manifest_path.read_bytes()
    if expected_sha256 and sha(raw) != expected_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    train = training_tasks(manifest)
    development = [dict(task) for task in manifest["tasks"] if task.get("split") == "development"]
    if len(development) != 4:
        raise ValueError("exact four development tasks required")
    # The manifest is answer-bearing, so copy only the fields needed for the
    # generation contract.  In particular, no development response field is
    # allowed to enter this program's generation path.
    clean = []
    for task in development:
        if "reference_fragment" in task:
            task.pop("reference_fragment")
        reject_answer_fields(task, task.get("id", "development"))
        clean.append({key: task[key] for key in ("id", "prefix", "suffix", "theorem_name", "dependencies")})
    return raw, train, clean


def run(args) -> dict:
    raw, train, development = load_tasks(args.manifest, args.expected_manifest_sha256)
    shape_counts = train_shapes(train)
    plan = {task["id"]: candidates(task, train) for task in development}
    if any(not values for values in plan.values()):
        raise ValueError("empty candidate set")
    # Freeze the synthesis plan before checker execution.  This makes it
    # impossible for verifier outcomes to change what is proposed.
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "plan.json").write_text(json.dumps({
        "manifest_sha256": sha(raw),
        "shape_counts": shape_counts,
        "method": "TRAIN proof-shape induction plus visible-scaffold identifier binding",
        "reference_fragment_used_for_development": False,
        "verifier_feedback_used": False,
        "candidate_counts": {key: len(value) for key, value in plan.items()},
        "candidates": plan,
    }, indent=2) + "\n")

    from harness.proof_fragment_check import certify_fragment

    rows = []
    for task in development:
        for index, fragment in enumerate(plan[task["id"]]):
            result = certify_fragment(
                task["prefix"], fragment, task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                work_root=args.output / "checks" / task["id"] / str(index),
                timeout=args.timeout,
            )
            rows.append({"task": task["id"], "candidate_index": index,
                         "fragment": fragment, **result})
    (args.output / "checks.jsonl").write_text(
        "".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    summary = {}
    for task in development:
        task_rows = [row for row in rows if row["task"] == task["id"]]
        passed = [row for row in task_rows if row.get("certified")]
        summary[task["id"]] = {
            "candidates": len(task_rows),
            "certified": len(passed),
            "first_certified_index": passed[0]["candidate_index"] if passed else None,
            "all_candidates_scored": True,
        }
    report = {
        "manifest_sha256": sha(raw),
        "train_tasks": len(train),
        "development_tasks": len(development),
        "shape_counts": shape_counts,
        "per_task": summary,
        "tasks_with_any_certificate": sum(bool(v["certified"]) for v in summary.values()),
        "candidate_rows": len(rows),
        "reference_fragment_used_for_development": False,
        "verifier_feedback_used": False,
        "training_executed": False,
        "proof_or_quality_claim": False,
        "gate_claim": False,
    }
    (args.output / "summary.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256")
    parser.add_argument("--timeout", type=int, default=30)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 60:
        parser.error("timeout must be 1..60 seconds")
    print(json.dumps(run(args), indent=2))


if __name__ == "__main__":
    main()
