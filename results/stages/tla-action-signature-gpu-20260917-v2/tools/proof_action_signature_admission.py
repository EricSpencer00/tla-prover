#!/usr/bin/env python3
"""Freeze and independently recheck an answer-free proof-action signature.

The packet contains only theorem-context prompts and deterministic symbolic
candidate proposals.  The verifier labels are sanitized booleans over those
proposals; no proof fragment, response text, protected row, or feedback is
exported.  This admission reruns a bounded positive/negative SANY contract
before a GPU worker is allowed to fit the prompt-only signature head.
"""
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

PACKET_SHA256 = "c9784d4da893464f23bc27610c5f7aed64c44bf5406a7ec33f27637ad0d7394f"
OFFICIAL_SHA256 = "f40539a20e449ad63b8244e85eff33c8022402df11a84e8228b71ccbfeae11b5"
LABELS_SHA256 = "bba10249105e1999656dd329a642c079f623f64fd9a4ee49f574c390d34a7854"
MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}
HOLDOUT_IDS = {
    "highest-done-step", "highest-correctness", "simple-preservation",
    "simple-short-full",
}
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair",
}
SLOTS = ("smt", "def", "use", "set_extensionality", "inductive", "instance")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def reject_keys(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_keys(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_keys(child, f"{path}[{index}]")


def action_signature(candidate: str) -> tuple[int, ...]:
    """Map a proposal to a fixed semantic action vocabulary."""
    if candidate == "OBVIOUS":
        return (0,) * len(SLOTS)
    if not isinstance(candidate, str) or not candidate.startswith("BY "):
        raise ValueError("candidate is not a safe BY action")
    upper = candidate.upper()
    return (
        int("SMT" in upper),
        int("DEF " in upper),
        int(" USE" in upper or upper.startswith("BY USE")),
        int("SETEXTENSIONALITY" in upper),
        int(any(name in upper for name in ("INDUCTIVEINVARIANT", "INVARIANTHOLD"))),
        int("INSTANCE" in upper),
    )


def load_packets(packet_path: Path, official_path: Path, labels_path: Path):
    packet_bytes = packet_path.read_bytes()
    official_bytes = official_path.read_bytes()
    labels_bytes = labels_path.read_bytes()
    if sha(packet_bytes) != PACKET_SHA256:
        raise ValueError("training packet hash mismatch")
    if sha(official_bytes) != OFFICIAL_SHA256:
        raise ValueError("official packet hash mismatch")
    if sha(labels_bytes) != LABELS_SHA256:
        raise ValueError("label hash mismatch")
    packet = json.loads(packet_bytes)
    official = json.loads(official_bytes)
    reject_keys(packet)
    reject_keys(official)
    if packet.get("packet_kind") != "answer_free_multistep_symbolic_action_coverage":
        raise ValueError("unexpected training packet kind")
    if packet.get("denominator") != 17 or len(packet.get("rows", [])) != 17:
        raise ValueError("training denominator mismatch")
    if official.get("packet_kind") != "answer_free_official_symbolic_candidate_ranking":
        raise ValueError("unexpected official packet kind")
    if official.get("denominator") != 119 or len(official.get("rows", [])) != 119:
        raise ValueError("official denominator mismatch")
    if {row["id"] for row in packet["rows"]} != TRAIN_IDS:
        raise ValueError("training membership mismatch")
    for row in packet["rows"] + official["rows"]:
        if not row.get("prompt") or not row.get("candidate_proposals"):
            raise ValueError("missing prompt or candidate proposals")
        if len(set(row["candidate_proposals"])) != len(row["candidate_proposals"]):
            raise ValueError(f"duplicate candidates in {row['id']}")
        for candidate in row["candidate_proposals"]:
            action_signature(candidate)
    labels = {}
    for line in labels_bytes.splitlines():
        record = json.loads(line)
        if set(record) != {"task", "candidate_index", "candidate", "certified"}:
            raise ValueError("labels are not sanitized task/index/candidate/boolean records")
        task = record["task"]
        index = record["candidate_index"]
        by_id = {row["id"]: row for row in packet["rows"]}
        if task not in TRAIN_IDS or not isinstance(index, int):
            raise ValueError("label outside training denominator")
        if not 0 <= index < len(by_id[task]["candidate_proposals"]):
            raise ValueError("label index outside candidate width")
        if record["candidate"] != by_id[task]["candidate_proposals"][index]:
            raise ValueError("label candidate mismatch")
        labels[(task, index)] = int(bool(record["certified"]))
    if len(labels) != 54 or sum(labels.values()) != 8:
        raise ValueError("frozen label coverage/positive count mismatch")
    return packet, official, labels


def target_signatures(packet, labels):
    targets = {}
    rows = {row["id"]: row for row in packet["rows"]}
    for task_id, row in rows.items():
        positives = [i for i in range(len(row["candidate_proposals"]))
                     if labels.get((task_id, i), 0)]
        targets[task_id] = (action_signature(row["candidate_proposals"][positives[0]])
                            if positives else None)
    if not all(targets[task_id] is not None for task_id in HOLDOUT_IDS):
        raise ValueError("holdout must contain a frozen positive signature target")
    return targets


def render_rank(target: tuple[float, ...], candidates: list[str]):
    ranked = []
    for index, candidate in enumerate(candidates):
        signature = action_signature(candidate)
        distance = sum(abs(float(a) - b) for a, b in zip(target, signature))
        ranked.append({"candidate_index": index, "candidate": candidate,
                       "signature": signature, "signature_distance": distance})
    return sorted(ranked, key=lambda item: (item["signature_distance"], item["candidate_index"]))


def run_sany_contract(manifest_path: Path, packet, labels, output: Path,
                      timeout: int, seconds: int) -> list[dict]:
    raw = manifest_path.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    task_by_id = {task["id"]: task for task in manifest["tasks"]
                  if task.get("split") == "train"}
    if set(task_by_id) != TRAIN_IDS:
        raise ValueError("manifest does not contain exact train denominator")
    rows = {row["id"]: row for row in packet["rows"]}
    # Recheck every positive label and one fixed negative control per task.
    checks = []
    started = time.monotonic()
    for task_id in sorted(TRAIN_IDS):
        indices = [i for i in range(len(rows[task_id]["candidate_proposals"]))
                   if labels.get((task_id, i), 0)]
        indices = indices + ([0] if 0 not in indices else [])
        for index in indices:
            if time.monotonic() + timeout > started + seconds:
                raise TimeoutError("fresh SANY contract budget exhausted")
            task = task_by_id[task_id]
            candidate = rows[task_id]["candidate_proposals"][index]
            result = certify_fragment(
                task["prefix"], candidate, task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(map(Path, task.get("dependencies", []))),
                work_root=output / "sany" / task_id / str(index), timeout=timeout)
            expected = bool(labels.get((task_id, index), 0))
            checks.append({"task": task_id, "candidate_index": index,
                           "candidate": candidate, "expected": expected,
                           **result})
            if bool(result.get("certified")) != expected:
                raise ValueError(f"fresh SANY mismatch for {task_id}/{index}")
    return checks


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True, type=Path)
    parser.add_argument("--official", required=True, type=Path)
    parser.add_argument("--labels", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--timeout", type=int, default=15)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 45 or not 60 <= args.seconds <= 900:
        parser.error("bounded SANY timeout/budget required")
    args.output.mkdir(parents=True, exist_ok=False)
    packet, official, labels = load_packets(args.packet, args.official, args.labels)
    targets = target_signatures(packet, labels)
    rows = {row["id"]: row for row in packet["rows"]}
    # A deterministic renderer control proves the signature-to-proposal map is
    # total and tie-broken without invoking a model or reading any answer.
    renderer_controls = []
    for task_id in sorted(TRAIN_IDS):
        target = targets[task_id] or (0,) * len(SLOTS)
        ranking = render_rank(target, rows[task_id]["candidate_proposals"])
        renderer_controls.append({"task": task_id, "top_index": ranking[0]["candidate_index"],
                                  "distance": ranking[0]["signature_distance"],
                                  "ranking": ranking})
    checks = run_sany_contract(args.manifest, packet, labels, args.output,
                               args.timeout, args.seconds)
    (args.output / "sany-checks.json").write_text(json.dumps(checks, indent=2) + "\n")
    admission = {
        "schema_version": 1,
        "packet_sha256": PACKET_SHA256,
        "official_packet_sha256": OFFICIAL_SHA256,
        "labels_sha256": LABELS_SHA256,
        "manifest_sha256": MANIFEST_SHA256,
        "slots": list(SLOTS),
        "training_denominator": 17,
        "fit_denominator": 13,
        "holdout_denominator": 4,
        "official_denominator": 119,
        "positive_label_count": 8,
        "sany_checks": len(checks),
        "sany_positive_checks": sum(bool(row["certified"]) for row in checks),
        "sany_negative_checks": sum(not bool(row["certified"]) for row in checks),
        "renderer_controls": len(renderer_controls),
        "reference_fragment_used": False,
        "protected_verifier_feedback_used": False,
        "protected_rows_in_training": False,
        "generated_feedback": False,
        "tlaps_training": False,
        "parameter_updates": 0,
        "quality_claim": False,
        "gate_claim": False,
        "method": "prompt-only multi-label semantic proof-action signature with deterministic proposal renderer",
        "targets": targets,
    }
    (args.output / "renderer-controls.json").write_text(json.dumps(renderer_controls, indent=2) + "\n")
    (args.output / "admission.json").write_text(json.dumps(admission, indent=2) + "\n")
    print(json.dumps(admission, indent=2))


if __name__ == "__main__":
    main()
