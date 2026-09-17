#!/usr/bin/env python3
"""Independently score paired PIR generations with strict TLAPS.

This process consumes only recorded base/parent/child generations and the
target-free development scaffolds.  It never trains, repairs, ranks, or feeds
verifier output back into a model.  Every malformed decode remains a failure.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_fragment_check import certify_fragment
from tools import proof_fragment_pir as pir


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def score(packet_path: Path, generations_path: Path, output: Path, work_root: Path,
          timeout: int, dependency_root: Path | None = None) -> dict:
    packet = pir.load_packet(packet_path)
    generations = json.loads(generations_path.read_text())
    by_id = {row["id"]: row for row in packet["development_rows"]}
    if set(by_id) != {row.get("id") for row in generations} or len(generations) != 4:
        raise ValueError("exact four paired development generations required")
    rows = []
    for row in generations:
        task = by_id[row["id"]]
        if row.get("valid") is not True:
            rows.append(dict(id=row["id"], certified=False, status=row.get("status", "invalid_decode"),
                             proved=0, total=0, raw_reply=row.get("raw_reply", "")))
            continue
        fragment = pir.decode_tokens(row["typed_tokens"])
        dependencies = tuple(Path(p) for p in task.get("dependencies", []))
        if dependency_root is not None:
            dependencies = tuple(dependency_root / path.name for path in dependencies)
        result = certify_fragment(task["prefix"], fragment, task["suffix"],
                                  theorem_name=task["theorem_name"],
                                  dependencies=dependencies,
                                  work_root=work_root / row["id"], timeout=timeout)
        rows.append(dict(id=row["id"], fragment=fragment, raw_reply=row.get("raw_reply", ""), **result))
    legacy = os.environ.get("PROVE_TLA_TLAPM_LEGACY") == "1"
    summary = dict(packet_sha256=sha(packet_path.read_bytes()), generations_sha256=sha(generations_path.read_bytes()),
                   rows=rows, tasks=4, certified_tasks=sum(row.get("certified") is True for row in rows),
                   verifier_runs=len(rows), verifier_mode=("legacy_tlaps_1.5.0_uncached_nofp_threads1"
                                                          if legacy else "tlaps_strict_uncached"),
                   strict_flags_used=not legacy, verifier_feedback_used=False, repair_used=False,
                   reward_used=False, fixed_denominator=4, quality_claim=False, proof_claim=False, gate_claim=False)
    output.mkdir(parents=True, exist_ok=False)
    (output / "rows.jsonl").write_text("\n".join(json.dumps(row) for row in rows) + "\n")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--packet", type=Path, required=True)
    p.add_argument("--generations", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--work-root", type=Path, required=True)
    p.add_argument("--timeout", type=int, default=60)
    p.add_argument("--dependency-root", type=Path,
                   help="Optional remote directory containing packet dependency basenames")
    args = p.parse_args()
    print(json.dumps(score(args.packet, args.generations, args.output, args.work_root,
                           args.timeout, args.dependency_root), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
