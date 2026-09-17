#!/usr/bin/env python3
"""Strictly check parent/child top-k DEVELOPMENT candidates.

Ranking selects candidates; TLAPS decides whether a selected fragment proves
the fixed target.  This audit keeps every raw checker result, checks top four
for each of the four DEVELOPMENT tasks under both policies, and makes no
quality or gate claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

PACKET_SHA256 = "ab311319022b03f09c3a4e039d37f2958ff55ff914c09865f98672d4145a2611"
RANKING_ROWS_SHA256 = "c483731cd7970f6d209dff9bc1ed98d6d2bfdc5ce74b078b7af35e2eecebe2ba"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def target_scoped_pass(result: dict) -> bool:
    if result.get("returncode") != 0 or result.get("timed_out"):
        return False
    candidate = result.get("candidate_path")
    if not candidate:
        return False
    module = Path(candidate).stem
    output = result.get("output", "")
    marker = f'File "./{module}.tla"'
    if marker not in output:
        return False
    target_output = output.rsplit(marker, 1)[-1]
    if re.search(r"\b(?:failed|omitted|interrupted|error|exception)\b", target_output, re.I):
        return False
    matches = re.findall(r'^\s*(?:\[INFO\]: )?All ([1-9]\d*) obligations? proved\.?\s*$',
                         target_output, re.M)
    return len(matches) == 1


def validate_rows(rows: list[dict]) -> list[dict]:
    expected = {"crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof", "crdt-sum-zero-proof"}
    if len(rows) != 4 or {row.get("task") for row in rows} != expected:
        raise ValueError("ranking rows do not contain exact DEVELOPMENT population")
    for row in rows:
        for key in ("parent_order", "child_order"):
            order = row.get(key)
            if not isinstance(order, list) or len(order) != 29 or sorted(order) != list(range(29)):
                raise ValueError("ranking row is not a complete 29-candidate permutation")
    return rows


def worker(args) -> dict:
    from harness.proof_fragment_check import certify_fragment

    packet_raw = args.packet.read_bytes()
    ranking_raw = args.ranking_rows.read_bytes()
    if sha(packet_raw) != args.expected_packet_sha256:
        raise ValueError("strict packet hash mismatch")
    if sha(ranking_raw) != args.expected_ranking_rows_sha256:
        raise ValueError("ranking rows hash mismatch")
    packet = json.loads(packet_raw)
    rows = validate_rows([json.loads(line) for line in ranking_raw.splitlines()])
    by_id = {row["id"]: row for row in packet}
    if set(by_id) != {row["task"] for row in rows}:
        raise ValueError("strict packet/ranking task mismatch")
    if args.output.exists():
        raise ValueError("output already exists")
    args.output.mkdir(parents=True)
    (args.output / "packet.json").write_bytes(packet_raw)
    (args.output / "ranking_rows.jsonl").write_bytes(ranking_raw)

    checks = []
    started = time.monotonic()
    with (args.output / "checks.jsonl").open("x") as stream:
        for policy, order_key in (("parent", "parent_order"), ("child", "child_order")):
            for row in rows:
                task = by_id[row["task"]]
                for rank, index in enumerate(row[order_key][:args.topk], 1):
                    result = certify_fragment(
                        task["prefix"], task["candidates"][index], task["suffix"],
                        theorem_name=task["theorem_name"],
                        dependencies=tuple(Path(path) for path in task["dependencies"]),
                        work_root=args.output / "checks" / policy / task["id"] / str(rank),
                        timeout=args.timeout)
                    record = {
                        "policy": policy, "task": task["id"], "rank": rank,
                        "candidate_index": index,
                        "target_scoped_pass": target_scoped_pass(result),
                        "raw_checker_status": result.get("status"),
                        **result,
                    }
                    checks.append(record)
                    stream.write(json.dumps(record) + "\n")
                    stream.flush()
    summary = {
        "schema": 1,
        "packet_sha256": sha(packet_raw),
        "ranking_rows_sha256": sha(ranking_raw),
        "policies": ["parent", "child"],
        "development_tasks": 4,
        "topk_per_policy": args.topk,
        "attempts": len(checks),
        "target_scoped_passes": sum(row["target_scoped_pass"] for row in checks),
        "parent_passes": sum(row["target_scoped_pass"] for row in checks if row["policy"] == "parent"),
        "child_passes": sum(row["target_scoped_pass"] for row in checks if row["policy"] == "child"),
        "development_reference_bytes_forwarded": False,
        "optimizer_updates": 0,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
        "elapsed_seconds": time.monotonic() - started,
        "scope": f"strict TLAPS top{args.topk} audit of target-free DEVELOPMENT rankings; no promotion claim",
    }
    dump(args.output / "summary.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--ranking-rows", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=10)
    parser.add_argument("--topk", type=int, default=4)
    parser.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    parser.add_argument("--expected-ranking-rows-sha256", default=RANKING_ROWS_SHA256)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 30 or not 1 <= args.topk <= 29:
        parser.error("invalid checker timeout/topk")
    worker(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
