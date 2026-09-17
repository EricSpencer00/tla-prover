#!/usr/bin/env python3
"""Freeze an answer-free variable-width symbolic-action packet.

The packet expands each official task with bounded visible-statement proposals
from ``proof_fact_search``.  It exports only the official task prompt and
candidate action strings; source prefixes, proof fragments and verifier
outcomes never enter the packet.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals

FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def reject_keys(value, path="manifest") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing key: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def prompt(task: dict) -> str:
    retrieval = task.get("retrieval", {})
    facts = list(retrieval.get("visible_facts", []))
    facts += list(retrieval.get("ranked_imported_facts", []))[:8]
    rendered = "\n".join(
        f"{fact['name']} == {fact['statement']}" for fact in facts)
    return (
        "Select one valid TLAPS proof action for the fixed final theorem. "
        "Return only a proof action beginning with OBVIOUS or BY. Do not "
        "change definitions, add axioms, emit a module, or use a reference "
        "proof. The verifier will independently check the selected action.\n\n"
        f"theorem={task['theorem_name']}\n"
        f"goal={task['target_goal']}\n\n"
        "Visible statement-only context (proof bodies withheld):\n"
        f"{rendered if rendered else '(none)'}\n"
    )


def build(manifest_path: Path, output: Path, expected_manifest_sha256: str) -> dict:
    raw = manifest_path.read_bytes()
    if sha(raw) != expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    reject_keys(manifest)
    tasks = manifest.get("tasks", [])
    if (len(tasks) != 119 or len({task.get("id") for task in tasks}) != 119 or
            manifest.get("reference_fragments_used") is not False or
            any(task.get("split") != "official_test" for task in tasks)):
        raise ValueError("exact answer-free official 119 population required")
    rows = []
    widths = []
    for task in tasks:
        dependencies = [Path(path) for path in task.get("dependencies", [])]
        expected = task.get("dependency_sha256", {})
        for dependency in dependencies:
            if expected and sha(dependency.read_bytes()) != expected.get(str(dependency)):
                raise ValueError(f"dependency hash mismatch: {task['id']}:{dependency}")
        dependency_texts = [dependency.read_text() for dependency in dependencies]
        library_paths = libraries(task["prefix"], dependency_texts, TLA_LIBRARY.split(":"))
        candidates, _ = proposals(
            task["prefix"], task["theorem_name"], task["target_goal"],
            dependency_texts, [path.read_text() for path in library_paths])
        candidates = list(dict.fromkeys(candidates))
        if not 1 <= len(candidates) <= 32:
            raise ValueError(f"proposal width outside bound: {task['id']}")
        if any(not candidate.startswith("BY ") or "AXIOM" in candidate or "OMITTED" in candidate
               for candidate in candidates):
            raise ValueError(f"unsafe candidate: {task['id']}")
        text = prompt(task)
        rows.append({
            "id": task["id"], "split": "official_test",
            "theorem_name": task["theorem_name"], "prompt": text,
            "prompt_sha256": sha(text.encode()), "candidate_proposals": candidates,
            "candidate_proposals_sha256": digest(candidates),
        })
        widths.append(len(candidates))
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_official_variable_symbolic_action_ranking",
        "manifest_sha256": sha(raw), "split": "official_test", "denominator": 119,
        "population": "frozen official 119 variable-width proposals",
        "protected_evaluation": True, "rows": rows,
        "reference_fragment_used": False, "reference_fragment_exported": False,
        "proof_bodies_exported": False, "successful_candidates_exported": False,
        "generated_feedback": False, "training_executed": False,
        "parameter_updates": 0, "tlaps_executed": False,
        "proof_or_quality_claim": False,
        "method": "bounded visible-statement proposal expansion; exact-parent inference only",
    }
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_text(json.dumps(packet, indent=2) + "\n")
    (output / "source-manifest.json").write_bytes(raw)
    (output / "config.json").write_text(json.dumps({
        "packet_sha256": sha((output / "packet.json").read_bytes()),
        "manifest_sha256": sha(raw), "rows": 119,
        "candidate_width_min": min(widths), "candidate_width_max": max(widths),
        "candidate_width_total": sum(widths), "parameter_updates": 0,
        "reference_fragment_used": False, "training_executed": False,
        "tlaps_executed": False, "quality_claim": False, "gate_claim": False,
    }, indent=2) + "\n")
    return dict(rows=119, candidate_width_min=min(widths),
                candidate_width_max=max(widths), candidate_width_total=sum(widths),
                packet_sha256=sha((output / "packet.json").read_bytes()),
                manifest_sha256=sha(raw))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(build(args.manifest, args.output, args.expected_manifest_sha256), indent=2))


if __name__ == "__main__":
    main()
