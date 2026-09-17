#!/usr/bin/env python3
"""Build a train-only candidate-specific typed-agenda ranking packet.

The TRAIN target is the candidate whose typed agenda has the greatest overlap
with the TRAIN reference fragment. DEVELOPMENT contains only its immutable
scaffold and frozen candidate/agenda lattice; no development target or
reference bytes are exported.
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

from tools import proof_typed_agenda as agenda

MANIFEST_SHA256 = agenda.MANIFEST_SHA256
PARENT_SHA256 = agenda.PARENT_SHA256


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def candidate_rows(task: dict) -> tuple[list[str], list[list[str]], list[list[int]]]:
    candidates = agenda.candidate_proposals(task)
    agendas = [agenda.agenda_signature(candidate, task.get("target_goal") or "")
               for candidate in candidates]
    ids = [agenda.slot_ids(slots) for slots in agendas]
    return candidates, agendas, ids


def overlap(reference_slots: list[str], candidate_slots: list[str]) -> float:
    reference = set(reference_slots)
    candidate = set(candidate_slots)
    return len(reference & candidate) / (len(reference | candidate) or 1)


def common_row(task: dict, candidates: list[str], agendas: list[list[str]], ids: list[list[int]]) -> dict:
    clean = {key: task[key] for key in (
        "id", "theorem_name", "prefix", "suffix", "dependencies")}
    clean["target_goal"] = task.get("target_goal")
    agenda.reject_answers(clean, task["id"])
    prompt = agenda.prompt_for(task)
    clean.update({
        "theorem_name": task["theorem_name"], "prompt": prompt,
        "prompt_sha256": sha(prompt.encode()), "candidate_proposals": candidates,
        "candidate_agenda_slots": agendas, "candidate_agenda_slot_ids": ids,
    })
    return clean


def build(manifest_path: Path, output: Path) -> dict:
    raw = manifest_path.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    train = [task for task in manifest["tasks"] if task.get("split") == "train"]
    development = [task for task in manifest["tasks"] if task.get("split") == "development"]
    if len(train) != 17 or len(development) != 4:
        raise ValueError("exact 17/4 population required")

    train_rows = []
    for task in train:
        candidates, agendas, ids = candidate_rows(task)
        reference_slots = agenda.agenda_signature(task["reference_fragment"], task.get("target_goal") or "")
        scores = [overlap(reference_slots, candidate_slots) for candidate_slots in agendas]
        teacher_index = max(range(len(scores)), key=lambda index: (scores[index], -index))
        row = common_row(task, candidates, agendas, ids)
        row.update({
            "id": task["id"], "split": "train", "teacher_candidate_index": teacher_index,
            "agenda_slots": reference_slots, "agenda_slot_ids": agenda.slot_ids(reference_slots),
            "teacher_agenda_overlap": scores[teacher_index],
            "teacher_candidate_scores": scores,
        })
        train_rows.append(row)

    development_rows = []
    for task in development:
        candidates, agendas, ids = candidate_rows(task)
        row = common_row(task, candidates, agendas, ids)
        row.update({"id": task["id"], "split": "development"})
        development_rows.append(row)

    packet = {
        "schema_version": 1, "packet_kind": agenda.PACKET_KIND,
        "representation": "typed_candidate_specific_agenda_ranker",
        "manifest_sha256": sha(raw), "parent_sha256": PARENT_SHA256,
        "slots": list(agenda.SLOTS), "train_rows": train_rows,
        "development_rows": development_rows,
        "development_targets_exported": False, "reference_fragments_exported": False,
        "train_teacher_agenda_labels_used": True, "verifier_feedback_used": False,
        "repair_used": False, "reward_used": False, "candidate_index_labels_used": False,
        "training_executed": False, "parameter_updates": 0, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    path = output / "packet.json"
    path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(path.read_bytes()), "manifest_sha256": sha(raw),
        "parent_sha256": PARENT_SHA256, "train_rows": 17, "development_rows": 4,
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in development_rows),
        "train_candidate_rows": sum(len(row["candidate_proposals"]) for row in train_rows),
        "slot_count": len(agenda.SLOTS), "development_targets_exported": False,
        "reference_fragments_exported": False, "train_teacher_agenda_labels_used": True,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "candidate_index_labels_used": False, "model_loaded": False,
        "cuda_touched": False, "optimizer_updates": 0,
        "proof_or_quality_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def load_packet(path: Path, expected_sha: str | None = None) -> dict:
    raw = path.read_bytes()
    if expected_sha is not None and sha(raw) != expected_sha:
        raise ValueError("exact typed candidate-rank packet required")
    packet = json.loads(raw)
    if packet.get("packet_kind") != agenda.PACKET_KIND or packet.get("representation") != "typed_candidate_specific_agenda_ranker":
        raise ValueError("unexpected typed candidate-rank packet")
    if packet.get("manifest_sha256") != MANIFEST_SHA256 or packet.get("parent_sha256") != PARENT_SHA256:
        raise ValueError("typed candidate-rank binding changed")
    if packet.get("slots") != list(agenda.SLOTS) or len(packet.get("train_rows", [])) != 17 or len(packet.get("development_rows", [])) != 4:
        raise ValueError("typed candidate-rank population mismatch")
    if packet.get("development_targets_exported") is not False or packet.get("candidate_index_labels_used") is not False:
        raise ValueError("development target leakage")
    for row in packet["train_rows"] + packet["development_rows"]:
        agenda.reject_answers(row)
        candidates = row.get("candidate_proposals", [])
        agendas = row.get("candidate_agenda_slots", [])
        ids = row.get("candidate_agenda_slot_ids", [])
        if not candidates or len(candidates) != len(agendas) or len(candidates) != len(ids):
            raise ValueError("candidate geometry mismatch")
        for candidate, slots, slot_ids in zip(candidates, agendas, ids):
            if agenda.slot_ids(slots) != slot_ids or slots != agenda.agenda_signature(candidate, row.get("target_goal") or ""):
                raise ValueError("candidate agenda binding changed")
    for row in packet["train_rows"]:
        index = row.get("teacher_candidate_index")
        if not isinstance(index, int) or not 0 <= index < len(row["candidate_proposals"]):
            raise ValueError("train teacher candidate label outside lattice")
    for row in packet["development_rows"]:
        if "teacher_candidate_index" in row or "teacher_candidate_scores" in row:
            raise ValueError("development teacher label leaked")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--packet", type=Path)
    parser.add_argument("--expected-packet-sha256")
    args = parser.parse_args()
    if args.build:
        if not args.manifest or not args.output:
            parser.error("--build requires --manifest and --output")
        print(json.dumps(build(args.manifest, args.output), indent=2))
    else:
        if not args.packet:
            parser.error("packet validation requires --packet")
        packet = load_packet(args.packet, args.expected_packet_sha256)
        print(json.dumps({"packet_sha256": sha(args.packet.read_bytes()),
                          "train_rows": len(packet["train_rows"]),
                          "development_rows": len(packet["development_rows"]),
                          "candidate_denominator": sum(len(row["candidate_proposals"])
                                                        for row in packet["development_rows"])}, indent=2))


if __name__ == "__main__":
    main()
