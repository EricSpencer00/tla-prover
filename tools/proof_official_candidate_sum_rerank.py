#!/usr/bin/env python3
"""Rerank an answer-free official receipt by logged sum response log-probability.

This is a deterministic control over an existing exact-parent receipt.  It
does not read proofs, verifier results, rewards, feedback, or references.
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


def reject_keys(value, path="document"):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def rerank(packet_path: Path, scores_path: Path, output: Path,
           expected_packet_sha256: str) -> dict:
    packet_bytes = packet_path.read_bytes()
    if sha(packet_bytes) != expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_bytes)
    reject_keys(packet)
    rows = packet.get("rows", [])
    if (packet.get("packet_kind") !=
            "answer_free_official_symbolic_candidate_ranking" or
            packet.get("split") != "official_test" or
            packet.get("denominator") != 119 or len(rows) != 119):
        raise ValueError("unsupported packet or denominator")
    candidates = {row["id"]: row["candidate_proposals"] for row in rows}

    observed = {}
    for raw in scores_path.read_text().splitlines():
        row = json.loads(raw)
        reject_keys(row)
        task = row.get("task")
        index = row.get("candidate_index")
        if task not in candidates or not isinstance(index, int):
            raise ValueError("unexpected score row")
        if not 0 <= index < len(candidates[task]):
            raise ValueError("candidate index outside frozen packet")
        if row.get("candidate") != candidates[task][index]:
            raise ValueError("candidate mismatch")
        if not isinstance(row.get("sum_logp"), (int, float)):
            raise ValueError("missing sum_logp")
        key = (task, index)
        if key in observed:
            raise ValueError("duplicate score row")
        observed[key] = row

    rankings = {}
    for task, pool in candidates.items():
        rows_for_task = [observed[(task, index)] for index in range(len(pool))]
        rankings[task] = [
            {"candidate_index": row["candidate_index"],
             "candidate": row["candidate"],
             "sum_logp": row["sum_logp"],
             "mean_logp": row["mean_logp"],
             "response_tokens": row["response_tokens"]}
            for row in sorted(rows_for_task,
                              key=lambda item: (-item["sum_logp"],
                                                item["candidate_index"]))]

    output.write_text(json.dumps(rankings, indent=2) + "\n")
    summary = {
        "requested_tasks": 119,
        "fully_ranked_tasks": len(rankings),
        "candidate_rows": sum(len(rows) for rows in rankings.values()),
        "method": "answer-free exact-parent sum response logp rerank",
        "packet_sha256": expected_packet_sha256,
        "reference_fragment_used": False,
        "training_executed": False,
        "tlaps_executed": False,
        "proof_or_quality_claim": False,
    }
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--scores", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    print(json.dumps(rerank(args.packet, args.scores, args.output,
                             args.expected_packet_sha256), indent=2))


if __name__ == "__main__":
    main()
