#!/usr/bin/env python3
"""Independently score scope-graph action rankings with strict TLAPS."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools.proof_scope_graph_energy import HOLDOUT_IDS, joint_scope_features
from tools.proof_task_context_energy import sha

TRAIN_PACKET_SHA = "c9784d4da893464f23bc27610c5f7aed64c44bf5406a7ec33f27637ad0d7394f"
OFFICIAL_PACKET_SHA = "f40539a20e449ad63b8244e85eff33c8022402df11a84e8228b71ccbfeae11b5"
TRAIN_MANIFEST_SHA = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
OFFICIAL_MANIFEST_SHA = "3380cf37c7311466ea7762662d55866839b3c3620ce73fb8d7ad209befe6de1d"


def load_scaffolds(path: Path, split: str) -> dict:
    raw = path.read_bytes()
    expected = TRAIN_MANIFEST_SHA if split == "train" else OFFICIAL_MANIFEST_SHA
    if sha(raw) != expected:
        raise ValueError("manifest hash mismatch")
    document = json.loads(raw)
    scaffolds = {}
    for source in document["tasks"]:
        if source.get("split") != split:
            continue
        if split == "train" and source["id"] not in HOLDOUT_IDS:
            continue
        fields = ("id", "prefix", "suffix", "theorem_name", "dependencies")
        scaffolds[source["id"]] = {field: source[field] for field in fields}
    expected_count = 4 if split == "train" else 119
    if len(scaffolds) != expected_count:
        raise ValueError("unexpected scaffold denominator")
    return scaffolds


def score(packet_path: Path, manifest_path: Path, model_path: Path,
          output: Path, split: str, timeout: int, seconds: int) -> dict:
    packet_raw = packet_path.read_bytes()
    expected_packet = TRAIN_PACKET_SHA if split == "train" else OFFICIAL_PACKET_SHA
    if sha(packet_raw) != expected_packet:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_raw)
    scaffolds = load_scaffolds(manifest_path, split)
    rows = {row["id"]: row for row in packet["rows"]
            if split == "official_test" or row["id"] in HOLDOUT_IDS}
    if set(rows) != set(scaffolds):
        raise ValueError("packet/scaffold task membership mismatch")
    model = json.loads(model_path.read_bytes())
    if model.get("reference_fragment_used") or model.get("protected_verifier_feedback_used"):
        raise ValueError("model receipt is not answer-free")
    weights, bias = model.get("weights"), model.get("bias")
    if not isinstance(weights, dict) or not isinstance(bias, (int, float)):
        raise ValueError("invalid model receipt")
    rankings = {}
    for task_id in sorted(scaffolds):
        task = scaffolds[task_id]
        candidates = rows[task_id]["candidate_proposals"]
        ranked = [{"candidate_index": index, "candidate": candidate,
                   "energy": float(bias + sum(weights.get(token, 0.0)
                                             for token in joint_scope_features(task, candidate)))}
                  for index, candidate in enumerate(candidates)]
        rankings[task_id] = sorted(ranked, key=lambda value: (-value["energy"], value["candidate_index"]))
    if output.exists():
        raise FileExistsError(output)
    output.mkdir(parents=True)
    checks = []
    started = time.monotonic()
    with (output / "checks.jsonl").open("x") as stream:
        for task_id, ranked in rankings.items():
            task = scaffolds[task_id]
            for rank, proposal in enumerate(ranked[:4], 1):
                if time.monotonic() + timeout > started + seconds:
                    break
                result = certify_fragment(
                    task["prefix"], proposal["candidate"], task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task["dependencies"]),
                    work_root=output / "checks" / task_id / str(rank), timeout=timeout)
                result.update(task=task_id, rank=rank,
                              candidate_index=proposal["candidate_index"],
                              candidate=proposal["candidate"], energy=proposal["energy"])
                checks.append(result)
                stream.write(json.dumps(result) + "\n")
                stream.flush()
                if result["certified"]:
                    break
    measured = {result["task"] for result in checks}
    certified = {result["task"] for result in checks if result["certified"]}
    top1 = {result["task"] for result in checks
            if result["certified"] and result["rank"] == 1}
    summary = {
        "requested_tasks": len(scaffolds), "fully_ranked_tasks": len(rankings),
        "measured_tasks": len(measured), "certified_tasks_top4": len(certified),
        "top1_verified": len(top1), "checker_attempts": len(checks),
        "checker": "strict uncached TLAPS --strict --nofp", "split": split,
        "reference_fragment_used": False, "training_executed": False,
        "repair_or_reward": False, "quality_claim": False, "gate_claim": False,
        "denominator_fixed": True,
        "method": "independent strict TLAPS over proof-state scope-graph action rankings",
        "elapsed_seconds": time.monotonic() - started,
    }
    (output / "rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--split", choices=("train", "official_test"), required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 15 or not 30 <= args.seconds <= 900:
        parser.error("checker budget outside frozen bound")
    print(json.dumps(score(args.packet, args.manifest, args.model, args.output,
                           args.split, args.timeout, args.seconds), indent=2))


if __name__ == "__main__":
    main()
