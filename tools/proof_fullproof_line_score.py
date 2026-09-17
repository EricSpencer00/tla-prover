#!/usr/bin/env python3
"""Score full-proof line-event generations with independent strict TLAPS.

This scorer consumes only the frozen target-free packet and recorded generation
files.  Malformed decodes are failures and are never repaired.  Verifier
results are written after generation and are not fed back into any model.
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

from harness.proof_fragment_check import certify_fragment
from tools import proof_fullproof_line_packet as packet_lib
from tools.proof_fullproof_line_cuda_train import decode_reply, load_packet


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def score(packet_path: Path, generations_path: Path, output: Path,
          work_root: Path, timeout: int) -> dict:
    packet = load_packet(packet_path)
    generations = json.loads(generations_path.read_text())
    if not isinstance(generations, list) or len(generations) != 4:
        raise ValueError("exact four development generations required")
    tasks = {row["id"]: row for row in packet["development_rows"]}
    if {row.get("id") for row in generations} != set(tasks):
        raise ValueError("generation ids do not match frozen development rows")

    rows = []
    for recorded in generations:
        task = tasks[recorded["id"]]
        row = {
            "id": recorded["id"],
            "valid": recorded.get("valid") is True,
            "recorded_status": recorded.get("status", "unknown"),
            "raw_reply_sha256": sha(recorded.get("raw_reply", "").encode()),
            "certified": False,
            "proved": 0,
            "total": 0,
        }
        if recorded.get("valid") is not True:
            row["status"] = recorded.get("status", "malformed_line_events")
            row["verifier_run"] = False
            rows.append(row)
            continue

        fragment = recorded.get("fragment")
        if not isinstance(fragment, str):
            decoded = decode_reply(recorded.get("raw_reply", ""))
            if decoded.get("valid") is not True:
                raise ValueError(f"recorded valid row cannot be decoded: {recorded['id']}")
            fragment = decoded["fragment"]
        # Re-check the recorded event representation without changing it.
        decoded = decode_reply(recorded.get("raw_reply", ""))
        if decoded.get("valid") is not True or decoded.get("fragment") != fragment:
            raise ValueError(f"recorded line-event binding changed: {recorded['id']}")
        dependencies = tuple(Path(path) for path in task.get("dependencies", []))
        result = certify_fragment(
            task["prefix"], fragment, task["suffix"],
            theorem_name=task["theorem_name"], dependencies=dependencies,
            work_root=work_root / recorded["id"], timeout=timeout,
        )
        row.update({
            "fragment": fragment,
            "fragment_sha256": sha(fragment.encode()),
            "verifier_run": True,
            "status": result.get("status"),
            "certified": result.get("certified") is True,
            "proved": result.get("proved", 0),
            "total": result.get("total", 0),
            "verifier": result,
        })
        rows.append(row)

    summary = {
        "packet_sha256": sha(packet_path.read_bytes()),
        "generations_sha256": sha(generations_path.read_bytes()),
        "packet_kind": packet["packet_kind"],
        "rows": rows,
        "tasks": 4,
        "decodable_tasks": sum(row["valid"] for row in rows),
        "certified_tasks": sum(row["certified"] for row in rows),
        "verifier_runs": sum(row["verifier_run"] for row in rows),
        "verifier_mode": "tlaps_strict_uncached",
        "strict_flags_used": True,
        "fixed_denominator": 4,
        "verifier_feedback_used": False,
        "repair_used": False,
        "reward_used": False,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    (output / "rows.jsonl").write_text("\n".join(json.dumps(row) for row in rows) + "\n")
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--generations", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--work-root", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    print(json.dumps(score(args.packet, args.generations, args.output,
                           args.work_root, args.timeout), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
