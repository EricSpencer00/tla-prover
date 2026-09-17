#!/usr/bin/env python3
"""Build an answer-free autoregressive proof-state transition packet.

TRAIN reference fragments are reduced to abstract event traces. DEVELOPMENT
rows retain only statement scaffolds and a frozen symbolic candidate lattice;
their proof bodies and verifier outcomes are never exported. A decoder may
score event traces, but the renderer owns the final candidate bytes.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
PACKET_KIND = "answer_free_autoregressive_proof_state_transition"
EVENTS = (
    "entry:direct", "entry:structured", "entry:other",
    "assume", "case", "use", "suffices", "obvious",
    "solver:smt", "solver:def", "solver:defs", "solver:ptl",
    "solver:z3", "solver:other",
    "facts:zero", "facts:one", "facts:few", "facts:many",
    "close:by", "close:qed", "eos",
)
EVENT_TO_ID = {event: index for index, event in enumerate(EVENTS)}
ANSWER_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair", "target", "pir_target",
}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def reject_answers(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in ANSWER_KEYS:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject_answers(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_answers(child, f"{path}[{index}]")


def prompt_for(task: dict) -> str:
    return (
        "Predict an abstract proof-state transition trace for the fixed theorem. "
        "Return no proof, candidate, module, verifier result, or reference answer.\n\n"
        f"theorem={task['theorem_name']}\n"
        f"goal={task.get('target_goal', '')}\n"
        "Immutable statement-only scaffold:\n" + task["prefix"] + task["suffix"]
    )


def _entry(text: str) -> str:
    if re.search(r"(?m)^\s*<[^>]+>", text) or re.search(
            r"(?m)^\s*(?:TAKE|ASSUME|CASE|SUFFICES)\b", text):
        return "entry:structured"
    if re.match(r"\s*BY\s+", text):
        return "entry:direct"
    return "entry:other"


def _solver_count(text: str) -> tuple[str, int]:
    matches = re.findall(r"\bBY\s+([^\n]+)", text, flags=re.I)
    solvers = []
    facts = 0
    for clause in matches:
        upper = clause.upper()
        if "SMT" in upper:
            solvers.append("solver:smt")
        elif re.search(r"\bDEFS\b", upper):
            solvers.append("solver:defs")
        elif re.search(r"\bDEF\b", upper):
            solvers.append("solver:def")
        elif "PTL" in upper:
            solvers.append("solver:ptl")
        elif re.search(r"\bZ3\b", upper):
            solvers.append("solver:z3")
        else:
            solvers.append("solver:other")
        words = [word for word in re.split(r"[\s,]+", clause.strip()) if word]
        facts += max(0, len(words) - 1)
    solver = solvers[0] if solvers else "solver:other"
    return solver, facts


def transition_trace(text: str) -> list[str]:
    """Reduce a proof-shaped string to a bounded abstract event trace."""
    text = text.strip()
    events = [_entry(text)]
    # Preserve state-changing control events in source order, but not names or
    # proof expressions. This is a shape label, not a proof target.
    for line in text.splitlines():
        upper = line.upper()
        if re.search(r"\b(?:TAKE|ASSUME)\b", upper):
            events.append("assume")
        if re.search(r"\bCASE\b", upper):
            events.append("case")
        if re.search(r"\bUSE\b", upper):
            events.append("use")
        if re.search(r"\bSUFFICES\b", upper):
            events.append("suffices")
        if re.search(r"\bOBVIOUS\b", upper):
            events.append("obvious")
    solver, fact_count = _solver_count(text)
    events.append(solver)
    events.append(
        "facts:zero" if fact_count == 0 else
        "facts:one" if fact_count == 1 else
        "facts:few" if fact_count <= 4 else "facts:many")
    events.append("close:qed" if re.search(r"\bQED\b", text) else "close:by")
    events.append("eos")
    return events[:24]


def trace_ids(events: list[str]) -> list[int]:
    if not events or events[-1] != "eos" or any(event not in EVENT_TO_ID for event in events):
        raise ValueError("invalid bounded transition trace")
    return [EVENT_TO_ID[event] for event in events]


def _candidate_proposals(task: dict, dependency_texts: list[str]) -> list[str]:
    dependency_paths = [Path(path) for path in task.get("dependencies", [])]
    library_paths = libraries(task["prefix"], dependency_texts, TLA_LIBRARY.split(":"))
    candidates, _ = proposals(
        task["prefix"], task["theorem_name"], task.get("target_goal", ""),
        dependency_texts, [path.read_text() for path in library_paths])
    candidates = list(dict.fromkeys(candidates))
    if not 1 <= len(candidates) <= 32:
        raise ValueError(f"proposal width outside bound for {task['id']}")
    if any(not candidate.startswith("BY ") or "AXIOM" in candidate or "OMITTED" in candidate
           for candidate in candidates):
        raise ValueError(f"unsafe symbolic proposal in {task['id']}")
    if not dependency_paths and dependency_texts:
        raise ValueError("dependency projection mismatch")
    return candidates


def build(manifest_path: Path, output: Path) -> dict:
    raw = manifest_path.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("manifest hash mismatch")
    manifest = json.loads(raw)
    train = [task for task in manifest["tasks"] if task.get("split") == "train"]
    development = [task for task in manifest["tasks"] if task.get("split") == "development"]
    if len(train) != 17 or len(development) != 4:
        raise ValueError("exact 17/4 population required")
    train_rows = []
    for task in train:
        events = transition_trace(task["reference_fragment"])
        prompt = prompt_for(task)
        train_rows.append({
            "id": task["id"], "split": "train", "theorem_name": task["theorem_name"],
            "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
            "transition_events": events, "transition_ids": trace_ids(events),
        })
    dev_rows = []
    for task in development:
        dependencies = [Path(path) for path in task.get("dependencies", [])]
        dependency_texts = [path.read_text() for path in dependencies]
        candidates = _candidate_proposals(task, dependency_texts)
        clean = {key: task[key] for key in (
            "id", "theorem_name", "target_goal", "prefix", "suffix", "dependencies")}
        clean["split"] = "development"
        reject_answers(clean, task["id"])
        prompt = prompt_for(task)
        clean.update({
            "prompt": prompt, "prompt_sha256": sha(prompt.encode()),
            "candidate_proposals": candidates,
            "candidate_transition_events": [transition_trace(candidate) for candidate in candidates],
            "candidate_transition_ids": [trace_ids(transition_trace(candidate)) for candidate in candidates],
        })
        dev_rows.append(clean)
    packet = {
        "schema_version": 1, "packet_kind": PACKET_KIND,
        "manifest_sha256": sha(raw), "parent_sha256": PARENT_SHA256,
        "events": list(EVENTS), "train_rows": train_rows, "development_rows": dev_rows,
        "development_targets_exported": False, "reference_fragments_exported": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "training_executed": False, "parameter_updates": 0, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    path = output / "packet.json"
    path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(path.read_bytes()), "manifest_sha256": sha(raw),
        "parent_sha256": PARENT_SHA256, "train_rows": 17, "development_rows": 4,
        "candidate_denominator": sum(len(row["candidate_proposals"]) for row in dev_rows),
        "events": list(EVENTS), "development_targets_exported": False,
        "reference_fragments_exported": False, "verifier_feedback_used": False,
        "repair_used": False, "reward_used": False, "model_loaded": False,
        "cuda_touched": False, "optimizer_updates": 0, "proof_or_quality_claim": False,
        "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def load_packet(path: Path, expected_sha: str | None = None) -> dict:
    raw = path.read_bytes()
    if expected_sha is not None and sha(raw) != expected_sha:
        raise ValueError("exact transition packet required")
    packet = json.loads(raw)
    if packet.get("packet_kind") != PACKET_KIND or packet.get("manifest_sha256") != MANIFEST_SHA256:
        raise ValueError("unexpected transition packet")
    if packet.get("parent_sha256") != PARENT_SHA256 or packet.get("events") != list(EVENTS):
        raise ValueError("transition packet binding changed")
    if (len(packet.get("train_rows", [])) != 17 or len(packet.get("development_rows", [])) != 4 or
            packet.get("development_targets_exported") is not False):
        raise ValueError("transition population mismatch")
    for row in packet["train_rows"] + packet["development_rows"]:
        reject_answers(row)
    for row in packet["train_rows"]:
        if trace_ids(row["transition_events"]) != row["transition_ids"]:
            raise ValueError("TRAIN trace binding changed")
    for row in packet["development_rows"]:
        if (not row.get("candidate_proposals") or
                len(row["candidate_proposals"]) != len(row.get("candidate_transition_ids", []))):
            raise ValueError("DEVELOPMENT renderer lattice mismatch")
        for candidate, ids in zip(row["candidate_transition_events"], row["candidate_transition_ids"]):
            if trace_ids(candidate) != ids:
                raise ValueError("candidate trace binding changed")
    return packet


def candidate_score(log_probabilities: list[float], ids: list[int]) -> float:
    if not ids or len(log_probabilities) != len(ids):
        raise ValueError("transition score shape mismatch")
    return sum(log_probabilities) / len(ids)


def select_candidate(row: dict, scores: list[float]) -> dict:
    if len(scores) != len(row["candidate_proposals"]):
        raise ValueError("candidate score denominator mismatch")
    index = max(range(len(scores)), key=lambda i: (scores[i], -i))
    return {
        "candidate_index": index, "candidate": row["candidate_proposals"][index],
        "transition_score": scores[index],
        "transition_events": row["candidate_transition_events"][index],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--packet", type=Path)
    parser.add_argument("--expected-packet-sha256")
    args = parser.parse_args()
    if args.build:
        if not args.manifest or not args.output:
            parser.error("--build requires --manifest and --output")
        print(json.dumps(build(args.manifest, args.output), indent=2))
    else:
        if not args.packet:
            parser.error("packet validation requires --packet")
        packet = load_packet(args.packet, args.expected_packet_sha256)
        print(json.dumps({"packet_sha256": sha(args.packet.read_bytes()),
                          "train_rows": len(packet["train_rows"]),
                          "development_rows": len(packet["development_rows"]),
                          "candidate_denominator": sum(len(row["candidate_proposals"])
                                                        for row in packet["development_rows"])}, indent=2))


if __name__ == "__main__":
    main()
