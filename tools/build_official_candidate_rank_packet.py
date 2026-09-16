#!/usr/bin/env python3
"""Freeze an answer-free 119-task symbolic-action ranking packet.

The official manifest was prepared by ``tools/proof_official_extension.py``
without reference fragments.  This adapter exports only the target goal, the
statement-only retrieval context, and the first four deterministic symbolic
proposals.  It never reads or exports a reference proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def scan_keys(value, path="manifest"):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing key present: {path}.{key}")
            scan_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            scan_keys(child, f"{path}[{index}]")


def answer_free_prompt(task: dict) -> str:
    retrieval = task.get("retrieval", {})
    visible = list(retrieval.get("visible_facts", []))
    imported = list(retrieval.get("ranked_imported_facts", []))[:8]
    facts = visible + imported
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


def build(manifest_path: Path, output: Path) -> dict:
    raw = manifest_path.read_bytes()
    manifest = json.loads(raw)
    scan_keys(manifest)
    tasks = manifest.get("tasks", [])
    if (len(tasks) != 119 or len({task.get("id") for task in tasks}) != 119 or
            manifest.get("reference_fragments_used") is not False or
            any(task.get("split") != "official_test" for task in tasks)):
        raise ValueError("exact answer-free official 119 population required")
    rows = []
    for task in tasks:
        proposals = list(task.get("symbolic_candidates", []))[:4]
        if not 1 <= len(proposals) <= 4 or len(set(proposals)) != len(proposals):
            raise ValueError(f"bounded symbolic proposals missing: {task['id']}")
        if any(not isinstance(candidate, str) or
               (candidate != "OBVIOUS" and not candidate.startswith("BY ")) or
               "OMITTED" in candidate or "AXIOM" in candidate
               for candidate in proposals):
            raise ValueError(f"unsafe symbolic proposal: {task['id']}")
        prompt = answer_free_prompt(task)
        rows.append({
            "id": task["id"],
            "split": "official_test",
            "theorem_name": task["theorem_name"],
            "prompt": prompt,
            "prompt_sha256": sha(prompt.encode()),
            "candidate_proposals": proposals,
            "candidate_proposals_sha256": digest(proposals),
        })
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_official_symbolic_candidate_ranking",
        "manifest_sha256": sha(raw),
        "split": "official_test",
        "denominator": 119,
        "population": "frozen official 119",
        "protected_evaluation": True,
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
        "method": "exact-parent conditional ranking over deterministic answer-free symbolic proposals",
    }
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_text(json.dumps(packet, indent=2) + "\n")
    (output / "source-manifest.json").write_bytes(raw)
    config = {
        "packet_sha256": sha((output / "packet.json").read_bytes()),
        "manifest_sha256": sha(raw),
        "rows": len(rows),
        "candidate_counts": {str(len(row["candidate_proposals"])): sum(
            len(item["candidate_proposals"]) == len(row["candidate_proposals"])
            for item in rows) for row in rows},
        "reference_fragment_used": False,
        "training_executed": False,
        "tlaps_executed": False,
        "parameter_updates": 0,
    }
    (output / "config.json").write_text(json.dumps(config, indent=2) + "\n")
    return config


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(build(args.manifest, args.output), indent=2))


if __name__ == "__main__":
    main()
