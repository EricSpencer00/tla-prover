#!/usr/bin/env python3
"""Fit an answer-free task-conditioned proof-action energy model.

This is a bounded CPU diagnostic.  It labels the fixed action proposals with
fresh strict TLAPS checks, then learns interactions between immutable theorem
shape and candidate syntax.  It never reads reference fragments, candidate
responses, verifier feedback, repairs, rewards, or the official packet while
fitting.  The official 119-row packet is intentionally out of scope here.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment

PACKET_IDS = {
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
FIT_IDS = PACKET_IDS - HOLDOUT_IDS
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair", "generated_feedback",
}
EXPECTED_SOURCE_SHA = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def reject_forbidden(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN_KEYS:
                raise ValueError(f"answer-bearing key: {path}.{key}")
            reject_forbidden(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_forbidden(child, f"{path}[{index}]")


def goal_text(task: dict) -> str:
    prefix = task["prefix"]
    marker = f"THEOREM {task['theorem_name']} =="
    position = prefix.rfind(marker)
    if position < 0:
        raise ValueError(f"theorem declaration missing: {task['id']}")
    value = prefix[position + len(marker):]
    value = re.split(r"\n\s*(?:PROOF|<1>|/\*|\(\*\*\*)", value, maxsplit=1)[0]
    return value.strip()


def task_features(task: dict) -> tuple[str, ...]:
    """Extract coarse, reusable proof-state shape without target text export."""
    prefix = task["prefix"]
    goal = goal_text(task)
    text = (goal + "\n" + prefix).upper()
    features = {
        "task:goal_len:" + str(min(len(goal) // 20, 20)),
        "task:decl_count:" + str(min(len(re.findall(r"(?m)^\s*[A-Za-z_]\w*\s*==", prefix)), 24)),
        "task:theorem:" + re.sub(r"[^A-Z0-9]+", "_", task["theorem_name"].upper()).strip("_")[:32],
    }
    markers = {
        "implies": r"=>",
        "conj": r"/\\",
        "temporal": r"\[\]|<>",
        "prime": r"'",
        "forall": r"\\A",
        "exists": r"\\E",
        "set": r"\\in|SUBSET|DOMAIN|UNION",
        "equality": r"(?<![<>=#])=(?!=)",
        "inequality": r"#|<=|>=|<|>",
        "function": r"\[[^\n]+\|->",
        "sequence": r"SEQ\(|LEN\(|Append|Head|Tail",
        "unchanged": r"UNCHANGED",
        "next": r"\bNEXT\b",
        "init": r"\bINIT\b",
        "type": r"\bTYPE\w*\b",
    }
    for name, pattern in markers.items():
        if re.search(pattern, text):
            features.add("task:" + name)
    for extension in re.findall(r"(?m)^\s*EXTENDS\s+([^\n]+)", prefix, re.I):
        for name in re.findall(r"[A-Za-z][A-Za-z0-9_]*", extension):
            features.add("task:extends:" + name.upper())
    return tuple(sorted(features))


def candidate_features(candidate: str) -> tuple[str, ...]:
    upper = candidate.upper()
    if upper == "OBVIOUS":
        solver = "obvious"
        body = ""
    else:
        solver = "mixed" if " SMT" in upper and " DEF" in upper else (
            "smt" if upper.startswith("BY SMT") else
            "ptl" if upper.startswith("BY PTL") else
            "def" if upper.startswith("BY DEF") else "facts")
        body = upper[3:] if upper.startswith("BY ") else upper
    facts = body.split(" DEF ", 1)[0].replace("SMT,", "").replace("PTL,", "")
    atoms = [part.strip() for part in facts.split(",") if part.strip()]
    values = {
        "action:solver:" + solver,
        "action:fact_count:" + str(min(len(atoms), 16)),
        "action:def_count:" + str(min(len(body.split(" DEF ", 1)[1].split(",")) if " DEF " in body else 0, 16)),
    }
    patterns = {
        "type": r"TYPE|INVARIANT",
        "init": r"\bINIT\b",
        "next": r"\bNEXT\b",
        "spec": r"\bSPEC\b",
        "vars": r"\bVARS\b|UNCHANGED",
        "inductive": r"IND|INVARIANT|SAFETY|CORRECT",
        "set": r"SET|EXTENSION|DOMAIN",
        "temporal": r"PTL|SPEC",
        "definition": r" DEF ",
    }
    for name, pattern in patterns.items():
        if re.search(pattern, upper):
            values.add("action:" + name)
    return tuple(sorted(values))


def joint_features(task: dict, candidate: str) -> tuple[str, ...]:
    task_tokens = task_features(task)
    action_tokens = candidate_features(candidate)
    result = list(task_tokens) + list(action_tokens)
    result.extend("joint:" + task_token + "|" + action_token
                  for task_token in task_tokens
                  for action_token in action_tokens)
    return tuple(result)


def fit_logistic(examples: list[tuple[tuple[str, ...], int]], epochs=2400,
                 learning_rate=0.08, l2=0.15) -> tuple[dict[str, float], float]:
    vocabulary = sorted({token for tokens, _ in examples for token in tokens})
    weights = {token: 0.0 for token in vocabulary}
    bias = 0.0
    for _ in range(epochs):
        gradients = {token: l2 * weight for token, weight in weights.items()}
        bias_gradient = l2 * bias
        for tokens, target in examples:
            value = max(-30.0, min(30.0, bias + sum(weights[token] for token in tokens)))
            probability = 1.0 / (1.0 + math.exp(-value))
            delta = probability - target
            bias_gradient += delta
            for token in tokens:
                gradients[token] += delta
        scale = learning_rate / max(1, len(examples))
        bias -= scale * bias_gradient
        for token in weights:
            weights[token] -= scale * gradients[token]
    return weights, bias


def energy(weights: dict[str, float], bias: float, task: dict, candidate: str) -> float:
    return bias + sum(weights.get(token, 0.0) for token in joint_features(task, candidate))


def load_tasks(source_manifest: Path, packet: Path) -> tuple[dict, dict]:
    source_raw = source_manifest.read_bytes()
    if sha(source_raw) != EXPECTED_SOURCE_SHA:
        raise ValueError("unexpected 21-task source manifest")
    source = json.loads(source_raw)
    packet_value = json.loads(packet.read_bytes())
    # Packet-level audit fields describe prior workflows; only candidate rows
    # are consumed here, and each row is checked for forbidden answer fields.
    reject_forbidden(packet_value.get("rows", []), "packet.rows")
    # The archival source manifest intentionally contains a reference_fragment
    # field for other workflows.  Project the exact immutable fields needed by
    # this diagnostic instead of traversing or reading that answer-bearing key.
    task_fields = ("id", "split", "theorem_name", "prefix", "suffix", "dependencies")
    tasks = {
        raw_task["id"]: {field: raw_task.get(field, []) if field == "dependencies"
                          else raw_task[field] for field in task_fields}
        for raw_task in source["tasks"]
    }
    rows = {row["id"]: row for row in packet_value["rows"]}
    if not PACKET_IDS.issubset(tasks) or set(rows) != PACKET_IDS:
        raise ValueError("exact 17-task packet membership required")
    for task_id, row in rows.items():
        if row.get("split") != tasks[task_id].get("split"):
            raise ValueError("source and packet split mismatch")
        if row.get("prompt_sha256") != sha(row["prompt"].encode()):
            raise ValueError("prompt hash mismatch")
        candidates = row.get("candidate_proposals")
        if not isinstance(candidates, list) or not 1 <= len(candidates) <= 32:
            raise ValueError("candidate width outside fixed bound")
        if any(not (candidate == "OBVIOUS" or candidate.startswith("BY ")) for candidate in candidates):
            raise ValueError("unsafe candidate proposal")
        if "candidate_proposals_sha256" not in row:
            raise ValueError("candidate proposal hash missing")
    return tasks, rows


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-manifest", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if not 1 <= args.timeout <= 10 or not 60 <= args.seconds <= 900:
        parser.error("bounded timeout/seconds required")
    tasks, rows = load_tasks(args.source_manifest, args.packet)
    args.output.mkdir(parents=True)
    started = time.monotonic()
    examples = []
    labels = []
    for task_id in sorted(PACKET_IDS):
        task = tasks[task_id]
        row = rows[task_id]
        for candidate_index, candidate in enumerate(row["candidate_proposals"]):
            if time.monotonic() + args.timeout > started + args.seconds:
                raise TimeoutError("strict verifier budget exhausted before 21-task coverage")
            result = certify_fragment(
                task["prefix"], candidate, task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                work_root=args.output / "checks" / task_id / str(candidate_index),
                timeout=args.timeout,
            )
            record = {
                "task": task_id, "split": row["split"], "candidate_index": candidate_index,
                "candidate": candidate, "certified": bool(result["certified"]),
                "status": result["status"], "proved": result["proved"],
                "total": result["total"], "seconds": result["seconds"],
                "sha256": result["sha256"],
            }
            labels.append(record)
            if task_id in FIT_IDS:
                examples.append((joint_features(task, candidate), int(record["certified"])))
    weights, bias = fit_logistic(examples)
    by_key = {(record["task"], record["candidate_index"]): record["certified"] for record in labels}
    rankings = {}
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        candidates = rows[task_id]["candidate_proposals"]
        ranked = [{"candidate_index": index, "candidate": candidate,
                   "energy": energy(weights, bias, task, candidate),
                   "certified": bool(by_key[(task_id, index)])}
                  for index, candidate in enumerate(candidates)]
        rankings[task_id] = sorted(ranked, key=lambda value: (-value["energy"], value["candidate_index"]))
    rank1 = sum(int(values[0]["certified"]) for values in rankings.values())
    solvable = sum(int(any(value["certified"] for value in values)) for values in rankings.values())
    (args.output / "strict-labels.jsonl").write_text("".join(json.dumps(record) + "\n" for record in labels))
    (args.output / "holdout-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.output / "model.json").write_text(json.dumps({
        "feature": "task-shape x answer-free proof-action syntax energy",
        "training_tasks": sorted(FIT_IDS), "holdout_tasks": sorted(HOLDOUT_IDS),
        "training_examples": len(examples), "source_manifest_sha256": sha(args.source_manifest.read_bytes()),
        "packet_sha256": sha(args.packet.read_bytes()), "reference_fragment_used": False,
        "protected_verifier_feedback_used": False, "repair_or_reward_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
        "bias": bias, "weights": weights,
    }, indent=2) + "\n")
    (args.output / "summary.json").write_text(json.dumps({
        "kind": "proof_task_context_energy_v1", "strict_label_records": len(labels),
        "train_positive_labels": sum(int(record["certified"]) for record in labels if record["split"] == "train"),
        "fit_tasks": len(FIT_IDS), "holdout_tasks": len(HOLDOUT_IDS), "holdout_rank1": rank1,
        "holdout_solvable": solvable, "denominator_fixed": True,
        "checker": "strict uncached TLAPS", "training_executed": False,
        "reference_fragment_used": False, "quality_claim": False, "gate_claim": False,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }, indent=2) + "\n")
    print(json.dumps({"holdout_rank1": rank1, "holdout_solvable": solvable,
                      "strict_label_records": len(labels), "output": str(args.output)}))


if __name__ == "__main__":
    main()
