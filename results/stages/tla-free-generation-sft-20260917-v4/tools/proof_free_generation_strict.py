#!/usr/bin/env python3
"""Independently score exact free-generation outputs with SANY-first TLAPS."""
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
    """Accept only a complete SANY pass followed by audited proof success."""
    sany = result.get("sany") or {}
    tlaps = result.get("tlaps") or {}
    diagnostic = result.get("tlaps_diagnostic") or {}
    return bool(
        result.get("certified") is True
        and result.get("status") == "pass"
        and sany.get("status") == "pass"
        and tlaps.get("status") == "pass"
        and tlaps.get("certified") is True
        and diagnostic.get("classification") == "proof_success"
        and isinstance(tlaps.get("proved"), int)
        and tlaps.get("proved") == tlaps.get("total") > 0
    )


def score(args) -> dict:
    from harness.proof_fragment_ladder import certify_fragment
    packet_raw = args.packet.read_bytes()
    generation_raw = args.generations.read_bytes()
    if digest(packet_raw) != args.expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_raw)
    development_answer_fields = {
        "reference_fragment", "proof_body", "pir_target", "candidate", "response",
        "generated", "repair", "feedback", "tlaps_output", "reward",
    }
    development = [row for row in packet["tasks"] if row.get("split") == "development"]
    if any(development_answer_fields.intersection(row) for row in development):
        raise ValueError("development packet contains answer-bearing fields")
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
                      "raw_checker_status": result.get("status"),
                      "sany_status": (result.get("sany") or {}).get("status"),
                      "tlaps_status": (result.get("tlaps") or {}).get("status"),
                      "tlaps_diagnostic": result.get("tlaps_diagnostic"), **result}
            checks.append(record)
            stream.write(json.dumps(record) + "\n")
            stream.flush()
    summary = {
        "schema": 1, "packet_sha256": digest(packet_raw),
        "generations_sha256": digest(generation_raw), "policies": sorted(expected_policies),
        "development_tasks": len(by_id), "attempts": len(checks),
        "target_scoped_passes": sum(row["target_scoped_pass"] for row in checks),
        "sany_passes": sum(row.get("sany_status") == "pass" for row in checks),
        "tlaps_attempts": sum(row.get("tlaps") is not None for row in checks),
        "proof_certified_passes": sum(row["target_scoped_pass"] for row in checks),
        "passes_by_policy": {policy: sum(row["target_scoped_pass"] for row in checks if row["policy"] == policy)
                             for policy in sorted(expected_policies)},
        "development_reference_bytes_forwarded": False, "optimizer_updates": 0,
        "verifier_feedback_used": False, "reward_used": False,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
        "elapsed_seconds": time.monotonic() - started,
        "sany_first": True,
        "scope": "strict SANY-first uncached TLAPS score of exact free-generation outputs; no promotion claim",
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
