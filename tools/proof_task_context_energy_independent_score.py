#!/usr/bin/env python3
"""Independently score task-conditioned proof-action rankings with strict TLAPS."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools.proof_task_context_energy import HOLDOUT_IDS, energy, reject_forbidden, sha, task_features

OFFICIAL_PACKET_SHA = "f40539a20e449ad63b8244e85eff33c8022402df11a84e8228b71ccbfeae11b5"
TRAIN_PACKET_SHA = "c9784d4da893464f23bc27610c5f7aed64c44bf5406a7ec33f27637ad0d7394f"
OFFICIAL_MANIFEST_SHA = "3380cf37c7311466ea7762662d55866839b3c3620ce73fb8d7ad209befe6de1d"
TRAIN_MANIFEST_SHA = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def load_tasks(manifest_path: Path, split: str) -> dict:
    raw = manifest_path.read_bytes()
    expected = OFFICIAL_MANIFEST_SHA if split == "official_test" else TRAIN_MANIFEST_SHA
    if sha(raw) != expected:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    tasks = {}
    for source in manifest.get("tasks", []):
        if source.get("split") != split:
            continue
        if split == "train" and source["id"] not in HOLDOUT_IDS:
            continue
        fields = ("id", "prefix", "suffix", "theorem_name", "dependencies")
        tasks[source["id"]] = {key: source[key] for key in fields}
    expected_count = 119 if split == "official_test" else 4
    if len(tasks) != expected_count:
        raise ValueError(f"expected {expected_count} immutable scaffolds")
    return tasks


def rank(task: dict, candidates: list[str], weights: dict[str, float], bias: float) -> list[dict]:
    rows = [{"candidate_index": index, "candidate": candidate,
             "energy": energy(weights, bias, task, candidate)}
            for index, candidate in enumerate(candidates)]
    return sorted(rows, key=lambda row: (-row["energy"], row["candidate_index"]))


def score(packet_path: Path, manifest_path: Path, model_path: Path,
          output: Path, split: str, timeout: int, seconds: int) -> dict:
    packet_raw = packet_path.read_bytes()
    expected_packet = OFFICIAL_PACKET_SHA if split == "official_test" else TRAIN_PACKET_SHA
    if sha(packet_raw) != expected_packet:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_raw)
    reject_forbidden(packet.get("rows", []), "packet.rows")
    tasks = load_tasks(manifest_path, split)
    model = json.loads(model_path.read_bytes())
    if model.get("reference_fragment_used") or model.get("protected_verifier_feedback_used"):
        raise ValueError("model receipt is not answer-free")
    weights = model.get("weights")
    bias = model.get("bias")
    if not isinstance(weights, dict) or not isinstance(bias, (int, float)):
        raise ValueError("invalid model receipt")
    rows = {row["id"]: row for row in packet["rows"]
            if split == "official_test" or row["id"] in HOLDOUT_IDS}
    if set(rows) != set(tasks):
        raise ValueError("packet/scaffold task membership mismatch")
    normalized = {task_id: rank(tasks[task_id], rows[task_id]["candidate_proposals"], weights, bias)
                  for task_id in sorted(tasks)}
    if output.exists():
        raise FileExistsError(output)
    output.mkdir(parents=True)
    checks = []
    started = time.monotonic()
    with (output / "checks.jsonl").open("x") as stream:
        for task_id, task in normalized.items():
            for rank_index, proposal in enumerate(task[:4], 1):
                if time.monotonic() + timeout > started + seconds:
                    break
                scaffold = tasks[task_id]
                result = certify_fragment(
                    scaffold["prefix"], proposal["candidate"], scaffold["suffix"],
                    theorem_name=scaffold["theorem_name"],
                    dependencies=tuple(Path(path) for path in scaffold["dependencies"]),
                    work_root=output / "checks" / task_id / str(rank_index),
                    timeout=timeout,
                )
                result.update(task=task_id, rank=rank_index,
                              candidate_index=proposal["candidate_index"],
                              candidate=proposal["candidate"], energy=proposal["energy"])
                checks.append(result)
                stream.write(json.dumps(result) + "\n")
                stream.flush()
                if result["certified"]:
                    break
    measured = {row["task"] for row in checks}
    certified = {row["task"] for row in checks if row["certified"]}
    top1 = {row["task"] for row in checks if row["certified"] and row["rank"] == 1}
    summary = {
        "requested_tasks": len(tasks), "fully_ranked_tasks": len(normalized),
        "measured_tasks": len(measured), "certified_tasks_top4": len(certified),
        "top1_verified": len(top1), "checker_attempts": len(checks),
        "checker": "strict uncached TLAPS --strict --nofp", "split": split,
        "reference_fragment_used": False, "training_executed": False,
        "repair_or_reward": False, "quality_claim": False, "gate_claim": False,
        "denominator_fixed": True,
        "method": "independent strict TLAPS over task-shape x answer-free action-energy rankings",
        "elapsed_seconds": time.monotonic() - started,
    }
    dump(output / "rankings.json", normalized)
    dump(output / "summary.json", summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--model", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
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
