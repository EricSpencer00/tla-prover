#!/usr/bin/env python3
"""Build a hash-pinned answer-free symbolic candidate packet.

The input frozen file is produced by the existing statement-only proposal
builder.  This adapter exports only prompts and deterministic BY proposals;
it never exports reference fragments, proof bodies, or verifier results.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

FORBIDDEN = {"reference_fragment", "response", "answer", "proof_body",
             "successful_candidate", "reward", "feedback", "repair"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def scan_keys(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN:
                raise ValueError(f"answer-bearing key present: {key}")
            scan_keys(child)
    elif isinstance(value, list):
        for child in value:
            scan_keys(child)


def build(manifest_path: Path, frozen_path: Path, output: Path) -> dict:
    manifest_bytes = manifest_path.read_bytes()
    manifest = json.loads(manifest_bytes)
    frozen = json.loads(frozen_path.read_bytes())
    if len(frozen) != 4 or {row.get("id") for row in frozen} != {
            task["id"] for task in manifest["tasks"] if task.get("split") == "development"}:
        raise ValueError("frozen candidate population is not the exact four-task development split")
    by_id = {task["id"]: task for task in manifest["tasks"] if task.get("split") == "development"}
    rows = []
    for source in frozen:
        scan_keys(source)
        task = by_id[source["id"]]
        candidates = source.get("candidates")
        if not isinstance(candidates, list) or not 4 <= len(candidates) <= 32:
            raise ValueError("candidate population outside bounded contract")
        if len(set(candidates)) != len(candidates):
            raise ValueError("duplicate candidate proposal")
        if any(not isinstance(candidate, str) or not candidate.startswith("BY ")
               or "OMITTED" in candidate or "AXIOM" in candidate
               for candidate in candidates):
            raise ValueError("non-symbolic or admitted candidate proposal")
        # The reference is consulted only by this anti-leak guard and is never
        # copied into the packet or used to order/filter proposals.
        reference = task.get("reference_fragment")
        if any(candidate.strip() == str(reference).strip() for candidate in candidates):
            raise ValueError("candidate equals held-out reference fragment")
        for key in ("prefix", "suffix", "theorem_name", "target_goal"):
            if source.get(key) != task.get(key):
                raise ValueError(f"frozen task mismatch: {source['id']}:{key}")
        prompt = source.get("prompt")
        if not isinstance(prompt, str) or "<PROOF_HOLE>" not in prompt:
            raise ValueError("frozen prompt is not a proof-hole prompt")
        if sha(prompt.encode()) != source.get("prompt_sha256"):
            raise ValueError("frozen prompt hash mismatch")
        context = source.get("context", {})
        if context.get("reference_fragment_used") is not False:
            raise ValueError("retrieval context is not explicitly answer-free")
        rows.append({
            "id": source["id"],
            "split": "development",
            "theorem_name": source["theorem_name"],
            "prompt": prompt,
            "prompt_sha256": sha(prompt.encode()),
            "candidate_proposals": candidates,
            "candidate_proposals_sha256": digest(candidates),
        })
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_symbolic_candidate_ranking",
        "manifest_sha256": sha(manifest_bytes),
        "source_frozen_sha256": sha(frozen_path.read_bytes()),
        "split": "development",
        "denominator": 4,
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
        "method": "deterministic visible-statement proposals; exact parent ranks candidates; independent TLAPS follows retrieval",
    }
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_text(json.dumps(packet, indent=2) + "\n")
    (output / "source-frozen.json").write_bytes(frozen_path.read_bytes())
    config = {
        "packet_sha256": sha((output / "packet.json").read_bytes()),
        "manifest_sha256": sha(manifest_bytes),
        "source_frozen_sha256": sha(frozen_path.read_bytes()),
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
    parser.add_argument("--frozen", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(build(args.manifest, args.frozen, args.output), indent=2))


if __name__ == "__main__":
    main()
