#!/usr/bin/env python3
"""Score a neural action inside a pre-registered symbolic proof shortlist.

The shortlist is the first four deterministic, answer-free proposals frozen in
the packet.  Neural scores choose one action within that bounded set; strict
uncached TLAPS then independently certifies the choice.  This is a prover
system diagnostic, not a proxy-quality or reward claim.
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


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def choose(shortlist, scores):
    """Choose the highest neural score without leaving the symbolic shortlist."""
    allowed = {row["candidate_index"] for row in shortlist}
    ranked = [row for row in scores if row["candidate_index"] in allowed]
    if len(ranked) != len(shortlist):
        raise ValueError("neural rankings do not cover the complete symbolic shortlist")
    return min(ranked, key=lambda row: (-row["mean_logp"], row["candidate_index"]))


def score(packet_path: Path, manifest_path: Path, rankings_path: Path, output: Path,
          expected_packet_sha256: str, expected_manifest_sha256: str,
          shortlist_width: int = 4) -> dict:
    if shortlist_width != 4:
        raise ValueError("the frozen diagnostic shortlist width is exactly four")
    packet_bytes = packet_path.read_bytes()
    if sha(packet_bytes) != expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_bytes)
    if (packet.get("packet_kind") != "answer_free_symbolic_candidate_ranking" or
            packet.get("denominator") != 4 or packet.get("reference_fragment_used") is not False):
        raise ValueError("unsupported or answer-bearing packet")
    manifest_bytes = manifest_path.read_bytes()
    if sha(manifest_bytes) != expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(manifest_bytes)
    tasks = {task["id"]: {key: task[key] for key in (
        "prefix", "suffix", "theorem_name", "dependencies")}
             for task in manifest["tasks"] if task.get("split") == "development"}
    rankings = json.loads(rankings_path.read_bytes())
    worker_config = json.loads((rankings_path.parent / "config.json").read_bytes())
    if worker_config.get("packet_sha256") != sha(packet_bytes):
        raise ValueError("ranking receipt is not bound to this packet")
    rows = []
    output.mkdir(parents=True, exist_ok=False)
    with (output / "selected.jsonl").open("x") as stream:
        for packet_row in packet["rows"]:
            task_id = packet_row["id"]
            if task_id not in tasks or task_id not in rankings:
                raise ValueError("task coverage mismatch")
            proposals = packet_row["candidate_proposals"]
            shortlist = [
                {"candidate_index": index, "candidate": proposals[index]}
                for index in range(shortlist_width)
            ]
            selected = choose(shortlist, rankings[task_id])
            task = tasks[task_id]
            from harness.proof_fragment_check import certify_fragment
            result = certify_fragment(
                task["prefix"], selected["candidate"], task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(Path(path) for path in task["dependencies"]),
                work_root=output / "checks" / task_id, timeout=30)
            row = dict(task=task_id, shortlist_width=shortlist_width,
                       shortlist_indices=[item["candidate_index"] for item in shortlist],
                       selected_index=selected["candidate_index"],
                       selected_score=selected["mean_logp"],
                       selected_candidate=selected["candidate"], **result)
            rows.append(row)
            stream.write(json.dumps(row) + "\n")
            stream.flush()
    summary = {
        "requested_tasks": 4,
        "measured_tasks": len(rows),
        "certified_tasks": sum(row["certified"] for row in rows),
        "top1_verified": sum(row["certified"] for row in rows),
        "shortlist_width": shortlist_width,
        "selection": "exact-parent conditional mean response logp within deterministic first-four symbolic proposals",
        "reference_fragment_used": False,
        "training_executed": False,
        "repair_or_reward": False,
        "quality_claim": False,
        "gate_claim": False,
        "denominator_fixed": True,
    }
    dump(output / "summary.json", summary)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--rankings", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    args = parser.parse_args()
    print(json.dumps(score(args.packet, args.manifest, args.rankings, args.output,
                           args.expected_packet_sha256, args.expected_manifest_sha256), indent=2))


if __name__ == "__main__":
    main()
