#!/usr/bin/env python3
"""Independently score exact free-generation outputs with strict TLAPS."""
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


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def extract_proof_block(reply: str) -> str | None:
    if not reply:
        return None
    fence = re.search(r"```(?:tla|tlaplus|tla\+)?\s*\n(.*?)```", reply,
                     re.DOTALL | re.IGNORECASE)
    start = re.compile(r"^\s*(PROOF\b|<\d+>|BY\b|OBVIOUS\b|OMITTED\b)")
    if fence and start.match(fence.group(1).strip()):
        return fence.group(1).strip()
    for index, line in enumerate(reply.splitlines()):
        if start.match(line):
            return "\n".join(reply.splitlines()[index:]).strip()
    return None


def target_scoped_pass(result: dict) -> bool:
    if result.get("returncode") != 0 or result.get("timed_out"):
        return False
    candidate = result.get("candidate_path")
    if not candidate:
        return False
    marker = f'File "./{Path(candidate).stem}.tla"'
    output = result.get("output", "")
    if marker not in output:
        return False
    target = output.rsplit(marker, 1)[-1]
    if re.search(r"\b(?:failed|omitted|interrupted|error|exception)\b", target, re.I):
        return False
    matches = re.findall(r"^\s*(?:\[INFO\]: )?All ([1-9]\d*) obligations? proved\.?\s*$",
                         target, re.M)
    return len(matches) == 1


def score(args) -> dict:
    from harness.proof_fragment_check import certify_fragment
    packet_raw = args.packet.read_bytes()
    generation_raw = args.generations.read_bytes()
    if digest(packet_raw) != args.expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    if b"reference_fragment" in packet_raw or b"proof_body" in packet_raw:
        raise ValueError("development packet contains answer-bearing fields")
    packet = json.loads(packet_raw)
    by_id = {row["id"]: row for row in packet["tasks"] if row.get("split") == "development"}
    generations = [json.loads(line) for line in generation_raw.splitlines() if line.strip()]
    expected_policies = {"base", "parent", "child"}
    if len(generations) != len(by_id) * len(expected_policies):
        raise ValueError("generation denominator mismatch")
    seen = set()
    for row in generations:
        key = (row.get("policy"), row.get("task"))
        if key in seen or row.get("policy") not in expected_policies or row.get("task") not in by_id:
            raise ValueError("duplicate or unknown generation row")
        if "reference_fragment" in row or "reference" in row:
            raise ValueError("generation row contains a reference field")
        if row.get("fragment") != extract_proof_block(row.get("raw_reply", "")):
            raise ValueError("stored fragment differs from raw reply extraction")
        seen.add(key)
    if len(seen) != len(generations):
        raise ValueError("incomplete generation population")
    if args.output.exists():
        raise ValueError("output already exists")
    args.output.mkdir(parents=True)
    (args.output / "packet.json").write_bytes(packet_raw)
    (args.output / "generations.jsonl").write_bytes(generation_raw)
    checks = []
    started = time.monotonic()
    with (args.output / "checks.jsonl").open("x") as stream:
        for row in generations:
            task = by_id[row["task"]]
            fragment = row.get("fragment")
            if not isinstance(fragment, str):
                result = {"certified": False, "status": "no_proof_fragment", "proved": 0,
                          "total": 0, "output": "", "returncode": None, "timed_out": False}
            else:
                result = certify_fragment(
                    task["prefix"], fragment, task["suffix"],
                    theorem_name=task["theorem_name"],
                    dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                    work_root=args.output / "checks" / row["policy"] / row["task"],
                    timeout=args.timeout)
            record = {"policy": row["policy"], "task": row["task"],
                      "target_scoped_pass": target_scoped_pass(result),
                      "raw_checker_status": result.get("status"), **result}
            checks.append(record)
            stream.write(json.dumps(record) + "\n")
            stream.flush()
    summary = {
        "schema": 1, "packet_sha256": digest(packet_raw),
        "generations_sha256": digest(generation_raw), "policies": sorted(expected_policies),
        "development_tasks": len(by_id), "attempts": len(checks),
        "target_scoped_passes": sum(row["target_scoped_pass"] for row in checks),
        "passes_by_policy": {policy: sum(row["target_scoped_pass"] for row in checks if row["policy"] == policy)
                             for policy in sorted(expected_policies)},
        "development_reference_bytes_forwarded": False, "optimizer_updates": 0,
        "verifier_feedback_used": False, "reward_used": False,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
        "elapsed_seconds": time.monotonic() - started,
        "scope": "strict uncached TLAPS score of exact free-generation outputs; no promotion claim",
    }
    dump(args.output / "summary.json", summary)
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--generations", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=10)
    parser.add_argument("--expected-packet-sha256", required=True)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 30:
        parser.error("invalid timeout")
    print(json.dumps(score(args), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
