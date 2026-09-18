#!/usr/bin/env python3
"""Build a source-separated 32-TRAIN/4-DEVELOPMENT typed ranker packet.

The 32 TRAIN rows come from the already admitted original6+broader26 strict
control populations.  Their reference fragments are used only to derive
coarse TRAIN agenda labels while building the packet and are never exported.
The four CRDT DEVELOPMENT rows are copied from the frozen candidate-rank
packet without targets, reference bytes, verifier feedback, repair, or reward.
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

from tools import proof_broader_packet as broader
from tools import proof_typed_agenda as agenda

PARENT_SHA256 = agenda.PARENT_SHA256
DEV_PACKET = ROOT / "results/runs/proof-typed-candidate-rank-20260917-v2/packet.json"
DEV_PACKET_SHA256 = "42da18eaeca6710cf68eb35c4af8d0d9dffb4e7295c4edca613e0fdf38dfb219"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def candidate_rows(task: dict) -> tuple[list[str], list[list[str]], list[list[int]]]:
    candidates = agenda.candidate_proposals(task)
    slots = [agenda.agenda_signature(candidate, task.get("target_goal") or "")
             for candidate in candidates]
    return candidates, slots, [agenda.slot_ids(item) for item in slots]


def clean_train(task: dict) -> dict:
    candidates, slots, ids = candidate_rows(task)
    goal = task.get("target_goal") or ""
    reference_slots = agenda.agenda_signature(task["reference_fragment"], goal)
    scores = [
        len(set(reference_slots) & set(candidate_slots)) /
        (len(set(reference_slots) | set(candidate_slots)) or 1)
        for candidate_slots in slots
    ]
    prompt = agenda.prompt_for(task)
    row = {
        "id": task["id"], "split": "train", "theorem_name": task["theorem_name"],
        "target_goal": task.get("target_goal"), "prefix": task["prefix"],
        "suffix": task["suffix"], "dependencies": task.get("dependencies", []),
        "source_family": task.get("source_family"),
        "source_sha256": task.get("source_sha256"),
        "assembled_sha256": task.get("assembled_sha256"),
        "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
        "candidate_proposals": candidates, "candidate_agenda_slots": slots,
        "candidate_agenda_slot_ids": ids,
        "teacher_candidate_index": max(range(len(scores)), key=lambda i: (scores[i], -i)),
        "teacher_candidate_scores": scores,
    }
    agenda.reject_answers(row)
    return row


def build(output: Path, dev_packet: Path = DEV_PACKET) -> dict:
    if output.exists():
        raise ValueError("output must be new")
    if sha(dev_packet.read_bytes()) != DEV_PACKET_SHA256:
        raise ValueError("frozen DEVELOPMENT packet changed")
    dev = agenda.load_packet(dev_packet, DEV_PACKET_SHA256)
    manifests = broader.load_manifests()
    train_tasks = broader.combined_tasks(manifests)[:32]
    train_rows = [clean_train(task) for task in train_tasks]
    if len(train_rows) != 32 or len({row["id"] for row in train_rows}) != 32:
        raise ValueError("exact 32-row TRAIN population required")
    development_rows = dev["development_rows"]
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_typed_candidate_specific_agenda_ranker_broader32",
        "representation": "typed_candidate_specific_agenda_ranker",
        "source_manifest_sha256": broader.MANIFEST_SHA256,
        "parent_sha256": PARENT_SHA256,
        "slots": list(agenda.SLOTS), "train_rows": train_rows,
        "development_rows": development_rows,
        "development_targets_exported": False,
        "reference_fragments_exported": False,
        "train_teacher_agenda_labels_used": True,
        "candidate_index_labels_used": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "training_executed": False, "parameter_updates": 0,
        "proof_or_quality_claim": False, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    packet_path = output / "packet.json"
    packet_path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(packet_path.read_bytes()),
        "source_manifest_sha256": broader.MANIFEST_SHA256,
        "development_packet_sha256": DEV_PACKET_SHA256,
        "parent_sha256": PARENT_SHA256, "train_rows": 32, "development_rows": 4,
        "train_candidate_rows": sum(len(row["candidate_proposals"]) for row in train_rows),
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in development_rows),
        "source_families": len({row["source_family"] for row in train_rows}),
        "development_targets_exported": False,
        "reference_fragments_exported": False, "candidate_index_labels_used": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "model_loaded": False, "cuda_touched": False, "optimizer_updates": 0,
        "proof_or_quality_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def load_packet(path: Path, expected_sha256: str | None = None) -> dict:
    raw = path.read_bytes()
    if expected_sha256 is not None and sha(raw) != expected_sha256:
        raise ValueError("broader typed packet hash changed")
    packet = json.loads(raw)
    if (packet.get("packet_kind") != "answer_free_typed_candidate_specific_agenda_ranker_broader32" or
            len(packet.get("train_rows", [])) != 32 or
            len(packet.get("development_rows", [])) != 4 or
            packet.get("development_targets_exported") is not False or
            packet.get("candidate_index_labels_used") is not False):
        raise ValueError("broader typed population or leakage mismatch")
    if packet.get("parent_sha256") != PARENT_SHA256 or packet.get("slots") != list(agenda.SLOTS):
        raise ValueError("broader typed binding changed")
    for row in packet["train_rows"] + packet["development_rows"]:
        agenda.reject_answers(row)
        candidates = row.get("candidate_proposals", [])
        agendas = row.get("candidate_agenda_slots", [])
        ids = row.get("candidate_agenda_slot_ids", [])
        if not candidates or len(candidates) != len(agendas) or len(candidates) != len(ids):
            raise ValueError("broader candidate geometry mismatch")
        for candidate, slots, slot_ids in zip(candidates, agendas, ids):
            if agenda.slot_ids(slots) != slot_ids or slots != agenda.agenda_signature(candidate, row.get("target_goal") or ""):
                raise ValueError("broader agenda binding changed")
    for row in packet["train_rows"]:
        index = row.get("teacher_candidate_index")
        scores = row.get("teacher_candidate_scores")
        if not isinstance(index, int) or not 0 <= index < len(row["candidate_proposals"]):
            raise ValueError("broader TRAIN teacher label outside lattice")
        if not isinstance(scores, list) or len(scores) != len(row["candidate_proposals"]):
            raise ValueError("broader TRAIN score vector mismatch")
    for row in packet["development_rows"]:
        if "teacher_candidate_index" in row or "teacher_candidate_scores" in row:
            raise ValueError("broader DEVELOPMENT teacher label leaked")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--dev-packet", type=Path, default=DEV_PACKET)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--packet", type=Path)
    parser.add_argument("--expected-packet-sha256")
    args = parser.parse_args()
    if args.build:
        if args.output is None:
            parser.error("--build requires --output")
        print(json.dumps(build(args.output, args.dev_packet), indent=2))
    elif args.packet:
        packet = load_packet(args.packet, args.expected_packet_sha256)
        print(json.dumps({"packet_sha256": sha(args.packet.read_bytes()),
                          "train_rows": len(packet["train_rows"]),
                          "development_rows": len(packet["development_rows"])}, indent=2))
    else:
        parser.error("use --build or --packet")


if __name__ == "__main__":
    main()
