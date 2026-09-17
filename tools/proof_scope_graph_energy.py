#!/usr/bin/env python3
"""Fit a proof-state scope-graph action energy model on a CPU-only split.

The representation is deliberately different from theorem-shape bag features:
it parses only the immutable hierarchical proof skeleton before the insertion
point and crosses scope state with answer-free action syntax.  Strict TLAPS
labels are generated locally for the fixed 13/4 split; no reference fragment,
protected feedback, repair, reward, or official outcome is consumed.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.proof_fragment_check import certify_fragment
from tools.proof_task_context_energy import (
    FIT_IDS, HOLDOUT_IDS, PACKET_IDS, candidate_features, fit_logistic,
    load_tasks, sha,
)


SCOPE_HEADER = re.compile(r"(?m)^\s*<(?P<level>[1-9]\d*)>(?P<label>[A-Za-z0-9_]+)?\.?\s+")


def scope_features(task: dict) -> tuple[str, ...]:
    """Represent current proof scope, not proof-body contents."""
    prefix = task["prefix"]
    events = list(SCOPE_HEADER.finditer(prefix))
    if not events:
        return ("scope:no_hierarchical_steps",)
    current = events[-1]
    level = int(current.group("level"))
    segments = []
    for index, event in enumerate(events):
        stop = events[index + 1].start() if index + 1 < len(events) else len(prefix)
        body = prefix[event.end():stop]
        kind = re.match(r"\s*([A-Z][A-Z0-9_]*)\b", body)
        segments.append((int(event.group("level")), kind.group(1) if kind else "ASSERTION", body))
    current_level, current_kind, current_body = segments[-1]
    parent_kind = "none"
    for old_level, old_kind, _ in reversed(segments[:-1]):
        if old_level < current_level:
            parent_kind = old_kind
            break
    same_level = [kind for old_level, kind, _ in segments[:-1] if old_level == current_level]
    completed = sum(bool(re.search(r"\b(?:BY|OBVIOUS)\b", body)) for _, _, body in segments[:-1])
    open_levels = len({old_level for old_level, _, _ in segments})
    values = {
        "scope:depth:" + str(min(level, 12)),
        "scope:steps:" + str(min(len(segments), 32)),
        "scope:siblings:" + str(min(len(same_level), 16)),
        "scope:completed_steps:" + str(min(completed, 32)),
        "scope:open_levels:" + str(min(open_levels, 12)),
        "scope:current_kind:" + current_kind,
        "scope:parent_kind:" + parent_kind,
        "scope:current_has_nested:" + str(int(bool(re.search(r"(?m)^\s*<[2-9]\d*>", current_body)))),
        "scope:current_has_proof:" + str(int(bool(re.search(r"\b(?:BY|OBVIOUS|PROOF)\b", current_body)))),
    }
    return tuple(sorted(values))


def joint_scope_features(task: dict, candidate: str) -> tuple[str, ...]:
    scope = scope_features(task)
    action = candidate_features(candidate)
    return tuple(list(scope) + list(action) + ["scope_action:" + a + "|" + b
                                                for a in scope for b in action])


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
                raise TimeoutError("strict verifier budget exhausted before complete coverage")
            result = certify_fragment(
                task["prefix"], candidate, task["suffix"],
                theorem_name=task["theorem_name"],
                dependencies=tuple(Path(path) for path in task.get("dependencies", [])),
                work_root=args.output / "checks" / task_id / str(candidate_index),
                timeout=args.timeout,
            )
            record = {"task": task_id, "split": row["split"],
                      "candidate_index": candidate_index, "candidate": candidate,
                      "certified": bool(result["certified"]), "status": result["status"],
                      "proved": result["proved"], "total": result["total"],
                      "seconds": result["seconds"], "sha256": result["sha256"]}
            labels.append(record)
            if task_id in FIT_IDS:
                examples.append((joint_scope_features(task, candidate), int(record["certified"])))
    weights, bias = fit_logistic(examples, epochs=2200, learning_rate=0.07, l2=0.2)
    label_map = {(r["task"], r["candidate_index"]): r["certified"] for r in labels}
    holdout = {}
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        ranked = [{"candidate_index": i, "candidate": candidate,
                   "energy": bias + sum(weights.get(token, 0.0)
                                        for token in joint_scope_features(task, candidate)),
                   "certified": bool(label_map[(task_id, i)])}
                  for i, candidate in enumerate(rows[task_id]["candidate_proposals"])]
        holdout[task_id] = sorted(ranked, key=lambda r: (-r["energy"], r["candidate_index"]))
    (args.output / "strict-labels.jsonl").write_text("".join(json.dumps(r) + "\n" for r in labels))
    (args.output / "holdout-rankings.json").write_text(json.dumps(holdout, indent=2) + "\n")
    (args.output / "model.json").write_text(json.dumps({
        "representation": "proof-state scope graph x answer-free action syntax",
        "source_manifest_sha256": sha(args.source_manifest.read_bytes()),
        "packet_sha256": sha(args.packet.read_bytes()), "training_tasks": sorted(FIT_IDS),
        "holdout_tasks": sorted(HOLDOUT_IDS), "reference_fragment_used": False,
        "protected_verifier_feedback_used": False, "repair_or_reward_used": False,
        "official_packet_used": False, "quality_claim": False, "gate_claim": False,
        "bias": bias, "weights": weights,
    }, indent=2) + "\n")
    rank1 = sum(int(rows[0]["certified"]) for rows in holdout.values())
    top4 = sum(int(any(row["certified"] for row in rows)) for rows in holdout.values())
    (args.output / "summary.json").write_text(json.dumps({
        "kind": "proof_scope_graph_energy_v1", "strict_label_records": len(labels),
        "fit_tasks": len(FIT_IDS), "holdout_tasks": len(HOLDOUT_IDS),
        "holdout_rank1": rank1, "holdout_top4": top4, "denominator_fixed": True,
        "checker": "strict uncached TLAPS", "training_executed": False,
        "reference_fragment_used": False, "quality_claim": False, "gate_claim": False,
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }, indent=2) + "\n")
    print(json.dumps({"holdout_rank1": rank1, "holdout_top4": top4,
                      "strict_label_records": len(labels), "output": str(args.output)}))


if __name__ == "__main__":
    main()
