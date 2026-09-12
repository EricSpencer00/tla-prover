#!/usr/bin/env python3
"""Freeze a leakage-resistant plan for bounded sequence-preference training."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import protected_sequence_objective_contract as contract

KIND = "protected_sequence_training_plan_v1"
SPLIT_SEED = "tla-sequence-preference-split-20260912-v1"
TRAIN_PAIRS = 8
HOLDOUT_PAIRS = 12
BUDGET = {
    "optimizer_updates": 8,
    "learning_rate": 1e-7,
    "margin": 0.25,
    "positive_nll_anchor_weight": 0.1,
    "max_seconds": 600,
    "trainable_tensors": 9,
}


def split(packet):
    value = contract.validate(packet)
    ranked = sorted(
        value["pairs"],
        key=lambda pair: hashlib.sha256(
            (SPLIT_SEED + "\0" + pair["source_id"]).encode()
        ).hexdigest(),
    )
    train, holdout = ranked[:TRAIN_PAIRS], ranked[TRAIN_PAIRS:]
    if len(train) != TRAIN_PAIRS or len(holdout) != HOLDOUT_PAIRS:
        raise ValueError("exact 8-train/12-holdout split required")
    train_ids = [pair["source_id"] for pair in train]
    holdout_ids = [pair["source_id"] for pair in holdout]
    if set(train_ids) & set(holdout_ids):
        raise ValueError("train and holdout must be disjoint")
    return train_ids, holdout_ids


def build(packet):
    train_ids, holdout_ids = split(packet)
    plan = {
        "kind": KIND,
        "split_seed": SPLIT_SEED,
        "train_source_ids": train_ids,
        "holdout_source_ids": holdout_ids,
        "budget": BUDGET,
        "protected_training": False,
        "protected_model_selection": False,
        "internal_holdout_use": "diagnostic_only_no_gate_credit",
        "acceptance_evaluation": packet["evaluation"],
        "retention": packet["retention"],
        "gate_claim": False,
    }
    plan["plan_sha256"] = contract.digest(plan)
    return plan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("append-only output required")
    plan = build(json.loads(args.packet.read_text()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(plan, indent=2) + "\n")
    print(json.dumps(plan, sort_keys=True))


if __name__ == "__main__":
    main()
