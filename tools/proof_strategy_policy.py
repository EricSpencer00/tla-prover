#!/usr/bin/env python3
"""Train a compact proof-strategy policy and expand it without verifier feedback.

The model predicts only a three-way structural plan learned from TRAIN proof
shapes.  A fixed, answer-free renderer maps the predicted plan to a frozen
candidate lattice.  DEVELOPMENT reference fragments and TLAPS outcomes never
enter the worker; the independent scorer owns all certification.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_train_shape_synth as synth

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
STRATEGIES = ("direct_def", "hierarchical", "other")
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


def strategy_for_fragment(fragment: str) -> str:
    if re.search(r"(?m)^\s*<[^>]+>", fragment) or re.search(r"(?m)^\s*(?:OBVIOUS|ASSUME|CASE|SUFFICES)\b", fragment):
        return "hierarchical"
    if re.match(r"\s*BY\s+DEF", fragment):
        return "direct_def"
    return "other"


def prompt_for(task: dict) -> str:
    goal = task.get("target_goal", "")
    return (
        "Predict only the proof strategy class for the fixed final theorem. "
        "Return one of direct_def, hierarchical, other. Do not emit a proof, "
        "candidate, module, verifier result, or reference answer.\n\n"
        f"theorem={task['theorem_name']}\n goal={goal}\n"
        "Immutable statement-only scaffold:\n" + task["prefix"] + task["suffix"]
    )


def build(manifest_path: Path, output: Path) -> dict:
    raw, train, development = synth.load_tasks(manifest_path, MANIFEST_SHA256)
    if len(train) != 17 or len(development) != 4:
        raise ValueError("exact 17/4 population required")
    train_rows = []
    for task in train:
        label = strategy_for_fragment(task["reference_fragment"])
        train_rows.append({
            "id": task["id"], "split": "train", "theorem_name": task["theorem_name"],
            "prompt": prompt_for(task), "prompt_sha256": sha(prompt_for(task).encode()),
            "strategy_label": label, "strategy_id": STRATEGIES.index(label),
        })
    dev_rows = []
    for task in development:
        clean = {key: task[key] for key in ("id", "theorem_name", "prefix", "suffix", "dependencies")}
        clean["split"] = "development"
        reject_answers(clean, task["id"])
        candidates = synth.candidates(task, train)
        if not candidates:
            raise ValueError(f"empty renderer lattice for {task['id']}")
        prompt = prompt_for(task)
        clean.update({
            "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
            "candidate_proposals": candidates,
            "candidate_strategies": [strategy_for_fragment(c) for c in candidates],
        })
        dev_rows.append(clean)
    packet = {
        "schema_version": 1,
        "packet_kind": "answer_free_proof_strategy_policy",
        "manifest_sha256": sha(raw),
        "strategies": list(STRATEGIES),
        "train_rows": train_rows,
        "development_rows": dev_rows,
        "development_targets_exported": False,
        "reference_fragments_exported": False,
        "verifier_feedback_used": False,
        "repair_used": False,
        "reward_used": False,
        "training_executed": False,
        "parameter_updates": 0,
        "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    path = output / "packet.json"
    path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(path.read_bytes()), "manifest_sha256": sha(raw),
        "train_rows": 17, "development_rows": 4,
        "train_strategy_counts": {s: sum(row["strategy_label"] == s for row in train_rows) for s in STRATEGIES},
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
        raise ValueError("exact strategy packet required")
    packet = json.loads(raw)
    if packet.get("packet_kind") != "answer_free_proof_strategy_policy":
        raise ValueError("unexpected strategy packet")
    if packet.get("manifest_sha256") != MANIFEST_SHA256 or packet.get("development_targets_exported") is not False:
        raise ValueError("strategy packet binding changed")
    train, dev = packet.get("train_rows", []), packet.get("development_rows", [])
    if len(train) != 17 or len(dev) != 4 or packet.get("strategies") != list(STRATEGIES):
        raise ValueError("strategy population mismatch")
    for row in train + dev:
        reject_answers(row)
    for row in train:
        if row.get("strategy_label") not in STRATEGIES or row.get("strategy_id") != STRATEGIES.index(row["strategy_label"]):
            raise ValueError("invalid TRAIN strategy label")
    for row in dev:
        if len(row.get("candidate_proposals", [])) == 0 or len(row["candidate_proposals"]) != len(row["candidate_strategies"]):
            raise ValueError("invalid DEVELOPMENT renderer lattice")
    return packet


def select_candidate(row: dict, strategy_id: int) -> dict:
    strategy = STRATEGIES[strategy_id]
    for index, candidate_strategy in enumerate(row["candidate_strategies"]):
        if candidate_strategy == strategy:
            return {"candidate_index": index, "candidate": row["candidate_proposals"][index], "strategy": strategy}
    # Explicit abstention is safer than silently changing the model's plan.
    return {"candidate_index": None, "candidate": None, "strategy": strategy}


def main() -> None:
    parser = argparse.ArgumentParser()
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
                      "development_rows": len(packet["development_rows"]), "strategies": list(STRATEGIES)}, indent=2))


if __name__ == "__main__":
    main()
