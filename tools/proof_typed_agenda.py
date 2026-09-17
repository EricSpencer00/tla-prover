#!/usr/bin/env python3
"""Build an answer-free typed proof-agenda packet.

TRAIN reference fragments are reduced to coarse obligation/lemma slot labels;
their proof bytes are never exported. DEVELOPMENT contains only immutable
statement scaffolds plus the frozen symbolic candidate lattice. A deterministic
renderer maps slot signatures back to candidate bytes without verifier scores,
candidate-index labels, reward, or protected answers.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.runner import TLA_LIBRARY
from tools import proof_goal_fact_transition as transition

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
PACKET_KIND = "answer_free_typed_proof_agenda"
SLOTS = (
    "entry:direct", "entry:structured", "entry:other",
    "goal:membership", "goal:equality", "goal:temporal", "goal:arithmetic",
    "goal:function", "goal:state", "goal:other",
    "lemma:definition", "lemma:state", "lemma:invariant", "lemma:set-function",
    "lemma:arithmetic", "lemma:temporal", "lemma:other",
    "backend:smt", "backend:definition", "backend:other",
    "close:by", "close:qed",
)
SLOT_IDS = {slot: index for index, slot in enumerate(SLOTS)}
ANSWER_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair", "target", "pir_target",
}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def reject_answers(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in ANSWER_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_answers(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_answers(child, f"{path}[{index}]")


def _goal_slots(goal: str) -> set[str]:
    upper = goal.upper()
    slots = set()
    if re.search(r"\b(?:IN|DOMAIN|SUBSET)\b", upper) or "\\IN" in upper:
        slots.add("goal:membership")
    if re.search(r"(?:==|=|EQUAL)", upper):
        slots.add("goal:equality")
    if re.search(r"\b(?:ALWAYS|EVENTUALLY|FAIR|SPEC|NEXT|TEMPORAL)\b|\[.*\]", upper):
        slots.add("goal:temporal")
    if re.search(r"\b(?:SUM|NAT|INTEGER|ADD|PLUS|ZERO|ARITHMETIC)\b", upper):
        slots.add("goal:arithmetic")
    if re.search(r"\b(?:FUNCTION|FUN_|DOMAIN|RANGE|MAPPING|INJECTION)\b", upper):
        slots.add("goal:function")
    if re.search(r"\b(?:INIT|NEXT|TYPEOK|SAFETY|INVARIANT|SPEC|VARS)\b", upper):
        slots.add("goal:state")
    return slots or {"goal:other"}


def _lemma_slots(text: str) -> set[str]:
    upper = text.upper()
    slots = set()
    if re.search(r"\b(?:DEF|DEFS)\b", upper):
        slots.add("lemma:definition")
    if re.search(r"\b(?:INIT|NEXT|TYPEOK|SAFETY|SPEC|VARS)\b", upper):
        slots.add("lemma:state")
    if re.search(r"\b(?:INV|INVARIANT|TYPE|SAFETY|PRESERV)\w*\b", upper):
        slots.add("lemma:invariant")
    if re.search(r"\b(?:SET|EXTENSION|EXTENSIONAL|DOMAIN|RANGE|FUN_|FUNCTION|INJECT|BIJECT)\w*\b", upper):
        slots.add("lemma:set-function")
    if re.search(r"\b(?:SUM|NAT|INTEGER|ADD|PLUS|ZERO|MONOTON|CONVERGEN|ARITHMET)\w*\b", upper):
        slots.add("lemma:arithmetic")
    if re.search(r"\b(?:PTL|TEMPORAL|ALWAYS|EVENTUALLY|FAIR|FAIRNESS|SPEC)\w*\b", upper):
        slots.add("lemma:temporal")
    return slots or {"lemma:other"}


def agenda_signature(text: str, goal: str = "") -> list[str]:
    text = text.strip()
    upper = text.upper()
    if re.search(r"(?m)^\s*<[^>]+>|\b(?:TAKE|ASSUME|CASE|SUFFICES)\b", upper):
        entry = "entry:structured"
    elif re.match(r"\s*BY\s+", upper):
        entry = "entry:direct"
    else:
        entry = "entry:other"
    backend = (
        "backend:smt" if re.search(r"\bSMT\b", upper) else
        "backend:definition" if re.search(r"\bDEFS?\b", upper) else
        "backend:other"
    )
    close = "close:qed" if re.search(r"\bQED\b", upper) else "close:by"
    slots = {entry, backend, close}
    slots.update(_goal_slots(goal))
    slots.update(_lemma_slots(text))
    return sorted(slots, key=SLOT_IDS.__getitem__)


def slot_ids(slots: list[str]) -> list[int]:
    if not slots or any(slot not in SLOT_IDS for slot in slots):
        raise ValueError("invalid typed agenda slots")
    return [SLOT_IDS[slot] for slot in slots]


def prompt_for(task: dict) -> str:
    return (
        "Predict typed proof obligation roles and lemma slots for the fixed theorem. "
        "Return no proof, candidate, module, verifier result, or reference answer.\n\n"
        f"theorem={task['theorem_name']}\n"
        f"goal={task.get('target_goal') or ''}\n"
        "Immutable statement-only scaffold:\n" + task["prefix"] + task["suffix"]
    )


def candidate_proposals(task: dict) -> list[str]:
    dependency_paths = [Path(path) for path in task.get("dependencies", [])]
    dependency_texts = [path.read_text() for path in dependency_paths]
    candidates = transition._candidate_proposals(task, dependency_texts)
    return list(dict.fromkeys(candidates))


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
        prompt = prompt_for(task)
        agenda = agenda_signature(task["reference_fragment"], task.get("target_goal") or "")
        train_rows.append({
            "id": task["id"], "split": "train", "theorem_name": task["theorem_name"],
            "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
            "agenda_slots": agenda, "agenda_slot_ids": slot_ids(agenda),
        })
    dev_rows = []
    for task in development:
        candidates = candidate_proposals(task)
        clean = {key: task[key] for key in (
            "id", "theorem_name", "target_goal", "prefix", "suffix", "dependencies")}
        reject_answers(clean, task["id"])
        prompt = prompt_for(task)
        clean.update({
            "split": "development", "prompt": prompt,
            "prompt_sha256": sha(prompt.encode()), "candidate_proposals": candidates,
            "candidate_agenda_slots": [
                agenda_signature(candidate, task.get("target_goal") or "")
                for candidate in candidates
            ],
            "candidate_agenda_slot_ids": [
                slot_ids(agenda_signature(candidate, task.get("target_goal") or ""))
                for candidate in candidates
            ],
        })
        dev_rows.append(clean)
    packet = {
        "schema_version": 1, "packet_kind": PACKET_KIND,
        "manifest_sha256": sha(raw), "parent_sha256": PARENT_SHA256,
        "slots": list(SLOTS), "train_rows": train_rows, "development_rows": dev_rows,
        "development_targets_exported": False, "reference_fragments_exported": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "candidate_index_labels_used": False, "training_executed": False,
        "parameter_updates": 0, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    path = output / "packet.json"
    path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(path.read_bytes()), "manifest_sha256": sha(raw),
        "parent_sha256": PARENT_SHA256, "train_rows": 17, "development_rows": 4,
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in dev_rows),
        "slot_count": len(SLOTS), "development_targets_exported": False,
        "reference_fragments_exported": False, "verifier_feedback_used": False,
        "repair_used": False, "reward_used": False, "candidate_index_labels_used": False,
        "model_loaded": False, "cuda_touched": False, "optimizer_updates": 0,
        "proof_or_quality_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def load_packet(path: Path, expected_sha: str | None = None) -> dict:
    raw = path.read_bytes()
    if expected_sha is not None and sha(raw) != expected_sha:
        raise ValueError("exact typed-agenda packet required")
    packet = json.loads(raw)
    if packet.get("packet_kind") != PACKET_KIND or packet.get("manifest_sha256") != MANIFEST_SHA256:
        raise ValueError("unexpected typed-agenda packet")
    if packet.get("parent_sha256") != PARENT_SHA256 or packet.get("slots") != list(SLOTS):
        raise ValueError("typed-agenda binding changed")
    if (len(packet.get("train_rows", [])) != 17 or len(packet.get("development_rows", [])) != 4 or
            packet.get("development_targets_exported") is not False or
            packet.get("candidate_index_labels_used") is not False):
        raise ValueError("typed-agenda population mismatch")
    for row in packet["train_rows"] + packet["development_rows"]:
        reject_answers(row)
    for row in packet["train_rows"]:
        if slot_ids(row["agenda_slots"]) != row["agenda_slot_ids"]:
            raise ValueError("TRAIN agenda binding changed")
    for row in packet["development_rows"]:
        candidates = row.get("candidate_proposals", [])
        agendas = row.get("candidate_agenda_slots", [])
        ids = row.get("candidate_agenda_slot_ids", [])
        if not candidates or len(candidates) != len(agendas) or len(candidates) != len(ids):
            raise ValueError("DEVELOPMENT agenda lattice mismatch")
        for candidate, agenda, agenda_ids in zip(candidates, agendas, ids):
            if slot_ids(agenda) != agenda_ids or agenda != agenda_signature(candidate, row.get("target_goal") or ""):
                raise ValueError("candidate agenda binding changed")
    return packet


def render_candidate(row: dict, predicted_slots: list[str]) -> dict:
    if not predicted_slots:
        raise ValueError("empty predicted agenda")
    predicted = set(predicted_slots)
    scores = []
    for index, slots in enumerate(row["candidate_agenda_slots"]):
        actual = set(slots)
        overlap = len(predicted & actual)
        union = len(predicted | actual)
        scores.append((overlap / union if union else 0.0, overlap, -len(actual), -index))
    index = max(range(len(scores)), key=lambda i: scores[i])
    return {"candidate_index": index, "candidate": row["candidate_proposals"][index],
            "agenda_slots": row["candidate_agenda_slots"][index], "agenda_score": scores[index]}


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
