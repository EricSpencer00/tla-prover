#!/usr/bin/env python3
"""Build an answer-free official-119 packet for typed candidate ranking."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_typed_agenda as agenda

OFFICIAL_PACKET_SHA256 = "f40539a20e449ad63b8244e85eff33c8022402df11a84e8228b71ccbfeae11b5"
SOURCE_MANIFEST_SHA256 = "3380cf37c7311466ea7762662d55866839b3c3620ce73fb8d7ad209befe6de1d"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def build(packet_path: Path, source_manifest_path: Path, output: Path) -> dict:
    packet_raw = packet_path.read_bytes()
    if sha(packet_raw) != OFFICIAL_PACKET_SHA256:
        raise ValueError("official packet hash mismatch")
    source_raw = source_manifest_path.read_bytes()
    if sha(source_raw) != SOURCE_MANIFEST_SHA256:
        raise ValueError("official source-manifest hash mismatch")
    packet = json.loads(packet_raw)
    source = json.loads(source_raw)
    if packet.get("packet_kind") != "answer_free_official_symbolic_candidate_ranking" or packet.get("denominator") != 119:
        raise ValueError("unexpected official packet")
    tasks = {row["id"]: row for row in source["tasks"]}
    if len(tasks) != 119 or len(packet.get("rows", [])) != 119:
        raise ValueError("official119 population required")
    rows = []
    for base in packet["rows"]:
        task = tasks.get(base["id"])
        if task is None or task.get("split") != "official_test":
            raise ValueError("official task membership mismatch")
        if base.get("candidate_proposals") is None:
            raise ValueError("official candidate lattice missing")
        candidates = list(base["candidate_proposals"])
        agendas = [agenda.agenda_signature(candidate, task.get("target_goal") or "")
                   for candidate in candidates]
        ids = [agenda.slot_ids(slots) for slots in agendas]
        prompt = agenda.prompt_for(task)
        rows.append({
            "id": task["id"], "split": "official_test", "theorem_name": task["theorem_name"],
            "target_goal": task.get("target_goal"), "prefix": task["prefix"],
            "suffix": task["suffix"], "dependencies": task.get("dependencies", []),
            "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
            "candidate_proposals": candidates, "candidate_agenda_slots": agendas,
            "candidate_agenda_slot_ids": ids,
        })
    result = {
        "schema_version": 1, "packet_kind": "answer_free_typed_candidate_rank_official",
        "official_packet_sha256": sha(packet_raw), "source_manifest_sha256": sha(source_raw),
        "split": "official_test", "denominator": 119, "rows": rows,
        "reference_fragment_used": False, "reference_fragment_exported": False,
        "proof_bodies_exported": False, "successful_candidates_exported": False,
        "development_targets_exported": False, "generated_feedback": False,
        "training_executed": False, "parameter_updates": 0, "tlaps_executed": False,
        "proof_or_quality_claim": False, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    path = output / "packet.json"
    path.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(path.read_bytes()), "official_packet_sha256": sha(packet_raw),
        "source_manifest_sha256": sha(source_raw), "denominator": 119,
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in rows),
        "reference_fragment_used": False, "reference_fragment_exported": False,
        "training_executed": False, "parameter_updates": 0,
        "tlaps_executed": False, "proof_or_quality_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def load_packet(path: Path, expected_sha: str | None = None) -> dict:
    raw = path.read_bytes()
    if expected_sha is not None and sha(raw) != expected_sha:
        raise ValueError("official typed-rank packet changed")
    packet = json.loads(raw)
    if packet.get("packet_kind") != "answer_free_typed_candidate_rank_official" or packet.get("denominator") != 119:
        raise ValueError("unexpected typed official packet")
    if len(packet.get("rows", [])) != 119 or packet.get("reference_fragment_used") is not False:
        raise ValueError("official packet population or leakage mismatch")
    for row in packet["rows"]:
        candidates = row.get("candidate_proposals", [])
        agendas = row.get("candidate_agenda_slots", [])
        ids = row.get("candidate_agenda_slot_ids", [])
        if not candidates or len(candidates) != len(agendas) or len(candidates) != len(ids):
            raise ValueError("official candidate geometry mismatch")
        for candidate, slots, slot_ids in zip(candidates, agendas, ids):
            if agenda.slot_ids(slots) != slot_ids or slots != agenda.agenda_signature(candidate, row.get("target_goal") or ""):
                raise ValueError("official agenda binding changed")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256")
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("output must be new")
    summary = build(args.packet, args.source_manifest, args.output)
    if args.expected_packet_sha256:
        load_packet(args.output / "packet.json", args.expected_packet_sha256)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
