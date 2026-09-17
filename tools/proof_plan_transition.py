#!/usr/bin/env python3
"""Build an answer-free ordered proof-plan transition packet.

The packet learns a short structural transition sketch from TRAIN proof
fragments only. DEVELOPMENT rows retain only their frozen scaffold and
candidate lattice; verifier outcomes, reference fragments, and rewards never
enter packet construction or candidate selection.
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_strategy_policy as policy

MANIFEST_SHA256 = policy.MANIFEST_SHA256
PACKET_SHA256 = "99e13cfb413f1d8d4e2766360be41d29bc7aaf5027e9dba1f3c10a696b952bae"
PARENT_SHA256 = policy.PARENT_SHA256
SLOTS = ("entry", "local", "close")
VOCAB = {
    "entry": ("direct", "structured", "other"),
    "local": ("definitions", "obligations", "assertion", "none"),
    "close": ("qed", "by", "none"),
}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def plan_for_fragment(fragment: str) -> dict[str, str]:
    text = fragment.strip()
    entry = "direct" if re.match(r"BY\s+DEF", text) else (
        "structured" if re.search(r"(?m)^\s*<\d+>", text) else "other")
    if re.search(r"\bBY\s+DEF", text):
        local = "definitions"
    elif re.search(r"\b(?:OBVIOUS|ASSUME|CASE|SUFFICES)\b", text):
        local = "obligations"
    elif text:
        local = "assertion"
    else:
        local = "none"
    close = "qed" if re.search(r"\bQED\b", text) else (
        "by" if re.search(r"\bBY\b", text) else "none")
    return {"entry": entry, "local": local, "close": close}


def candidate_plan(candidate: str) -> dict[str, str]:
    return plan_for_fragment(candidate)


def reject_answers(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in policy.ANSWER_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_answers(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_answers(child, f"{path}[{index}]")


def build(manifest_path: Path, output: Path) -> dict:
    raw, train, development = policy.synth.load_tasks(manifest_path, MANIFEST_SHA256)
    if len(train) != 17 or len(development) != 4:
        raise ValueError("exact 17/4 population required")
    train_rows = []
    for task in train:
        prompt = policy.prompt_for(task)
        plan = plan_for_fragment(task["reference_fragment"])
        train_rows.append({
            "id": task["id"], "split": "train", "theorem_name": task["theorem_name"],
            "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
            "plan": plan, "plan_ids": [VOCAB[slot].index(plan[slot]) for slot in SLOTS],
        })
    dev_rows = []
    for task in development:
        clean = {key: task[key] for key in ("id", "theorem_name", "prefix", "suffix", "dependencies")}
        clean["split"] = "development"
        reject_answers(clean, task["id"])
        candidates = task.get("candidate_proposals")
        if candidates is None:
            candidates = policy.synth.candidates(task, train)
        if not candidates:
            raise ValueError(f"empty renderer lattice for {task['id']}")
        prompt = policy.prompt_for(task)
        clean.update({
            "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
            "candidate_proposals": candidates,
            "candidate_plans": [candidate_plan(candidate) for candidate in candidates],
        })
        dev_rows.append(clean)
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_ordered_proof_plan_transition",
        "manifest_sha256": sha(raw), "source_packet_sha256": PACKET_SHA256,
        "parent_sha256": PARENT_SHA256, "slots": list(SLOTS),
        "vocab": VOCAB, "train_rows": train_rows, "development_rows": dev_rows,
        "development_targets_exported": False, "reference_fragments_exported": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "training_executed": False, "parameter_updates": 0, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    path = output / "packet.json"
    path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(path.read_bytes()), "manifest_sha256": sha(raw),
        "source_packet_sha256": PACKET_SHA256, "train_rows": 17, "development_rows": 4,
        "slots": list(SLOTS), "train_plan_counts": {
            slot: {value: sum(row["plan"][slot] == value for row in train_rows)
                   for value in VOCAB[slot]} for slot in SLOTS},
        "development_targets_exported": False, "reference_fragments_exported": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "model_loaded": False, "cuda_touched": False, "optimizer_updates": 0,
        "proof_or_quality_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def load_packet(path: Path, expected_sha: str) -> dict:
    raw = path.read_bytes()
    if sha(raw) != expected_sha:
        raise ValueError("exact ordered-plan packet required")
    packet = json.loads(raw)
    if packet.get("packet_kind") != "answer_free_ordered_proof_plan_transition":
        raise ValueError("unexpected ordered-plan packet")
    if (packet.get("manifest_sha256") != MANIFEST_SHA256 or
            packet.get("source_packet_sha256") != PACKET_SHA256 or
            packet.get("parent_sha256") != PARENT_SHA256 or
            packet.get("development_targets_exported") is not False):
        raise ValueError("ordered-plan packet binding changed")
    if packet.get("slots") != list(SLOTS) or len(packet.get("train_rows", [])) != 17 or len(packet.get("development_rows", [])) != 4:
        raise ValueError("ordered-plan population mismatch")
    for row in packet["train_rows"] + packet["development_rows"]:
        reject_answers(row)
    for row in packet["train_rows"]:
        if set(row.get("plan", {})) != set(SLOTS) or len(row.get("plan_ids", [])) != len(SLOTS):
            raise ValueError("invalid TRAIN plan")
    for row in packet["development_rows"]:
        if not row.get("candidate_proposals") or len(row["candidate_proposals"]) != len(row.get("candidate_plans", [])):
            raise ValueError("invalid DEVELOPMENT renderer lattice")
    return packet


def select_candidate(row: dict, predicted: dict[str, str]) -> dict:
    def distance(plan: dict[str, str]) -> int:
        return sum(plan[slot] != predicted[slot] for slot in SLOTS)
    distances = [distance(plan) for plan in row["candidate_plans"]]
    index = min(range(len(distances)), key=lambda i: (distances[i], i))
    return {
        "candidate_index": index, "candidate": row["candidate_proposals"][index],
        "plan": predicted, "candidate_plan": row["candidate_plans"][index],
        "plan_distance": distances[index],
    }


def main() -> None:
    parser = __import__("argparse").ArgumentParser()
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--expected-packet-sha256")
    parser.add_argument("--packet", type=Path)
    parser.add_argument("--build", action="store_true")
    args = parser.parse_args()
    if args.build:
        if not args.manifest or not args.output:
            parser.error("--build requires --manifest and --output")
        print(json.dumps(build(args.manifest, args.output), indent=2))
        return
    if not args.packet or not args.expected_packet_sha256:
        parser.error("packet validation requires --packet and --expected-packet-sha256")
    packet = load_packet(args.packet, args.expected_packet_sha256)
    print(json.dumps({"packet_sha256": sha(args.packet.read_bytes()), "train_rows": len(packet["train_rows"]),
                      "development_rows": len(packet["development_rows"]), "slots": list(SLOTS)}, indent=2))


if __name__ == "__main__":
    main()
