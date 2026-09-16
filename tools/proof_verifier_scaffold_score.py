#!/usr/bin/env python3
"""Independently score the answer-free verifier-scaffold GPU diagnostic.

The GPU worker only emits raw inference rows.  This local scorer binds those
rows to the frozen development manifest, extracts a proof fragment, and runs
the strict uncached TLAPS checker on the exact prefix/fragment/suffix bytes.
It never reads a reference fragment, never repairs a reply, and never turns a
partial or verifier-rejected output into a quality claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import time
from pathlib import Path
from typing import Callable, Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_gen import extract_proof_block
from tools.proof_verifier_scaffold import sha
from tools.proof_verifier_scaffold_cuda_eval import BUDGET, validate_packet


HEX64 = re.compile(r"[0-9a-f]{64}\Z")


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def _read_json(path: Path) -> dict:
    value = json.loads(path.read_text())
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def _read_jsonl(path: Path) -> list[dict]:
    if not path.is_file():
        raise ValueError(f"generation ledger missing: {path}")
    rows = []
    with path.open() as stream:
        for line_number, line in enumerate(stream, 1):
            if not line.strip():
                continue
            try:
                value = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"invalid JSON at {path}:{line_number}") from exc
            if not isinstance(value, dict):
                raise ValueError(f"generation row is not an object at {path}:{line_number}")
            rows.append(value)
    return rows


def _hash_file(path: str | Path, expected: str, label: str) -> None:
    path = Path(path)
    if not HEX64.fullmatch(expected or ""):
        raise ValueError(f"{label} hash is not a SHA-256 digest")
    if sha(path.read_bytes()) != expected:
        raise ValueError(f"{label} changed: {path}")


def load_frozen_tasks(manifest_path: str | Path, expected_manifest_sha256: str,
                      packet_rows: list[dict]) -> dict[str, dict]:
    """Load only the immutable task boundaries needed for local scoring.

    The manifest contains reference fragments for controls, but this function
    intentionally does not read that field.  Candidate scoring needs only the
    frozen source boundaries, theorem name, and dependency closure.
    """
    manifest_path = Path(manifest_path)
    raw = manifest_path.read_bytes()
    if sha(raw) != expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    tasks = [task for task in manifest.get("tasks", [])
             if task.get("split") == "development"]
    expected_ids = [row["id"] for row in packet_rows]
    if len(tasks) != 4 or [task.get("id") for task in tasks] != expected_ids:
        raise ValueError("packet is not bound to the exact four development tasks")
    result = {}
    for task in tasks:
        if task.get("id") in result:
            raise ValueError("duplicate development task")
        source_path = task.get("source_path")
        source_sha256 = task.get("source_sha256")
        if not source_path or not source_sha256:
            raise ValueError(f"missing frozen source identity: {task.get('id')}")
        _hash_file(source_path, source_sha256, f"source for {task['id']}")
        dependencies = tuple(Path(path) for path in task.get("dependencies", []))
        dependency_hashes = task.get("dependency_sha256", {})
        if set(map(str, dependencies)) != set(dependency_hashes):
            raise ValueError(f"dependency identity mismatch: {task['id']}")
        for dependency in dependencies:
            _hash_file(dependency, dependency_hashes[str(dependency)],
                       f"dependency for {task['id']}")
        if (not isinstance(task.get("prefix"), str)
                or not isinstance(task.get("suffix"), str)
                or not isinstance(task.get("theorem_name"), str)):
            raise ValueError(f"incomplete frozen task boundary: {task['id']}")
        # Keep only fields consumed by scoring.  In particular, do not pass a
        # reference answer through to the checker or scoring callback.
        result[task["id"]] = {
            "id": task["id"],
            "prefix": task["prefix"],
            "suffix": task["suffix"],
            "theorem_name": task["theorem_name"],
            "dependencies": dependencies,
        }
    return result


def validate_input(packet_path: str | Path, expected_packet_sha256: str,
                   manifest_path: str | Path, expected_manifest_sha256: str
                   ) -> tuple[dict, dict[str, dict]]:
    packet_path = Path(packet_path)
    packet_raw = packet_path.read_bytes()
    if sha(packet_raw) != expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    packet = json.loads(packet_raw)
    packet_rows = validate_packet(packet)
    if packet.get("manifest_sha256") != expected_manifest_sha256:
        raise ValueError("packet/manifest identity mismatch")
    tasks = load_frozen_tasks(manifest_path, expected_manifest_sha256, packet_rows)
    return packet, tasks


def _check_sha(value: str, label: str) -> None:
    if not isinstance(value, str) or not HEX64.fullmatch(value):
        raise ValueError(f"invalid {label} SHA-256")


def validate_generations(packet: dict, generations_dir: str | Path,
                         expected_checkpoint_sha256: str | None = None
                         ) -> tuple[dict, list[dict]]:
    """Validate worker accounting without interpreting proof quality."""
    generations_dir = Path(generations_dir)
    config = _read_json(generations_dir / "config.json")
    rows = _read_jsonl(generations_dir / "generations.jsonl")
    packet_raw = json.dumps(packet, indent=2).encode() + b"\n"
    packet_sha256 = sha(packet_raw)
    # The caller pins the packet bytes separately; this check binds the worker
    # to the same semantic object and catches a copied/rewritten packet only
    # when its exact file is also passed through validate_input.
    if config.get("packet_sha256") != packet_sha256:
        raise ValueError("generation config packet identity mismatch")
    if config.get("budget") != BUDGET:
        raise ValueError("generation budget/profile changed")
    if (config.get("restore_exact") is not True
            or config.get("parameter_updates") != 0
            or config.get("training_executed") is not False
            or config.get("reference_fragment_used") is not False
            or config.get("proof_or_quality_claim") is not False):
        raise ValueError("worker is not inference-only")
    checkpoint_sha256 = config.get("checkpoint_sha256")
    _check_sha(checkpoint_sha256, "checkpoint")
    if expected_checkpoint_sha256 is not None and checkpoint_sha256 != expected_checkpoint_sha256:
        raise ValueError("checkpoint identity mismatch")

    packet_rows = packet["rows"]
    expected = {row["id"]: row for row in packet_rows}
    if len(rows) > len(packet_rows):
        raise ValueError("generation ledger exceeds frozen denominator")
    if [row.get("id") for row in rows] != [row["id"] for row in packet_rows[:len(rows)]]:
        raise ValueError("generation ledger skips or reorders tasks")
    for row in rows:
        task = expected[row["id"]]
        if (row.get("prompt_sha256") != task["prompt_sha256"]
                or row.get("status") not in {"generated", "context_overflow"}):
            raise ValueError("generation prompt/status provenance mismatch")
        rendered = row.get("rendered_prompt")
        input_ids = row.get("input_token_ids")
        if (not isinstance(rendered, str) or sha(rendered.encode()) != row.get("rendered_prompt_sha256")
                or not isinstance(input_ids, list) or not input_ids
                or any(type(token) is not int or token < 0 for token in input_ids)
                or row.get("input_tokens") != len(input_ids)
                or digest(input_ids) != row.get("input_token_ids_sha256")):
            raise ValueError("generation input accounting mismatch")
        if row["status"] == "context_overflow":
            if set(row) != {"id", "prompt_sha256", "rendered_prompt",
                            "rendered_prompt_sha256", "input_token_ids",
                            "input_token_ids_sha256", "input_tokens", "status"}:
                raise ValueError("context-overflow row contains output fields")
            continue
        tokens = row.get("token_ids")
        raw_reply = row.get("raw_reply")
        if (not isinstance(tokens, list)
                or any(type(token) is not int or token < 0 for token in tokens)
                or row.get("output_tokens") != len(tokens)
                or digest(tokens) != row.get("token_ids_sha256")
                or not isinstance(raw_reply, str)
                or sha(raw_reply.encode()) != row.get("raw_reply_sha256")
                or row.get("hit_token_limit") is not (len(tokens) == BUDGET["max_new_tokens"])):
            raise ValueError("generation output accounting mismatch")
        expected_fields = {"id", "prompt_sha256", "rendered_prompt",
                           "rendered_prompt_sha256", "input_token_ids",
                           "input_token_ids_sha256", "input_tokens", "status",
                           "token_ids", "token_ids_sha256", "output_tokens",
                           "hit_token_limit", "raw_reply", "raw_reply_sha256"}
        if set(row) != expected_fields:
            raise ValueError("unexpected generation output field")
    return config, rows


def score(packet_path: str | Path, manifest_path: str | Path,
          generations_dir: str | Path, output: str | Path,
          *, expected_packet_sha256: str, expected_manifest_sha256: str,
          expected_checkpoint_sha256: str | None = None,
          checker: Callable | None = None) -> dict:
    """Write an independent strict-verifier ledger and summary."""
    packet, tasks = validate_input(packet_path, expected_packet_sha256,
                                   manifest_path, expected_manifest_sha256)
    config, generations = validate_generations(packet, generations_dir,
                                               expected_checkpoint_sha256)
    if checker is None:
        from harness.proof_fragment_check import certify_fragment
        checker = certify_fragment
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    by_id = {row["id"]: row for row in generations}
    results = []
    started = time.monotonic()
    with (output / "rows.jsonl").open("x") as stream:
        for task_id in (row["id"] for row in packet["rows"]):
            task = tasks[task_id]
            generation = by_id.get(task_id)
            result = {"id": task_id, "split": "development",
                      "certified": False, "status": "generation_unattempted"}
            if generation is None:
                pass
            elif generation["status"] == "context_overflow":
                result["status"] = "context_overflow"
            else:
                raw_reply = generation["raw_reply"]
                result["raw_reply_sha256"] = generation["raw_reply_sha256"]
                fragment = extract_proof_block(raw_reply)
                if fragment is None:
                    result["status"] = "no_proof_fragment"
                else:
                    result.update(
                        fragment=fragment,
                        fragment_sha256=sha(fragment.encode()),
                        checker="harness.proof_fragment_check.certify_fragment",
                        **checker(
                            task["prefix"], fragment, task["suffix"],
                            theorem_name=task["theorem_name"],
                            dependencies=task["dependencies"],
                            work_root=output / "checks" / task_id,
                            timeout=30,
                        ),
                    )
            results.append(result)
            stream.write(json.dumps(result) + "\n")
            stream.flush()
    summary = {
        "schema_version": 1,
        "packet_sha256": expected_packet_sha256,
        "manifest_sha256": expected_manifest_sha256,
        "checkpoint_sha256": config["checkpoint_sha256"],
        "requested_rows": len(packet["rows"]),
        "generated_rows": sum(row["status"] == "generated" for row in generations),
        "measured_rows": sum(by_id.get(row["id"], {}).get("status") == "generated"
                              for row in packet["rows"]),
        "certified_tasks": sum(row["certified"] for row in results),
        "unmeasured_tasks": sum(row["status"] != "pass" for row in results),
        "parameter_updates": 0,
        "training_executed": False,
        "reference_fragment_read": False,
        "repair_executed": False,
        "reward_executed": False,
        "protected_evaluation": False,
        "proof_or_quality_claim": False,
        "verifier": "strict uncached TLAPS via harness.proof_fragment_check",
        "elapsed_seconds": time.monotonic() - started,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main(argv: Iterable[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--generations", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-packet-sha256", required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    parser.add_argument("--expected-checkpoint-sha256")
    args = parser.parse_args(argv)
    summary = score(
        args.packet, args.manifest, args.generations, args.output,
        expected_packet_sha256=args.expected_packet_sha256,
        expected_manifest_sha256=args.expected_manifest_sha256,
        expected_checkpoint_sha256=args.expected_checkpoint_sha256,
    )
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
