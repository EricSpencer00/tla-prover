#!/usr/bin/env python3
"""Fit an answer-free proof-dependency graph model over strict TLAPS labels.

This is a bounded CPU diagnostic.  It expands each immutable proof skeleton
into visible/imported declaration candidates, labels those candidates with
fresh strict TLAPS checks, and learns graph-structural features from the 17
training tasks.  Candidate identities are not used as features: the model
sees solver kind, graph size/connectivity, declaration provenance, lexical
goal coverage, and declaration-order shape.  The four CRDT tasks are held out
for an independent rank measurement.

No reference fragment, proof body, protected verifier feedback, repair,
reward, official outcome, or generated answer is read by this program.
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
from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals, statements, tokens

TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}
HOLDOUT_IDS = {
    "crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof",
    "crdt-sum-zero-proof",
}
EXPECTED_MANIFEST_SHA = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
FORBIDDEN_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair", "generated_feedback",
}


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
    marker = f"THEOREM {task['theorem_name']} =="
    lemma_marker = f"LEMMA {task['theorem_name']} =="
    position = task["prefix"].rfind(marker)
    marker_used = marker
    if position < 0:
        position = task["prefix"].rfind(lemma_marker)
        marker_used = lemma_marker
    if position < 0:
        raise ValueError(f"target declaration missing: {task['id']}")
    value = task["prefix"][position + len(marker_used):]
    value = re.split(r"\n\s*(?:PROOF|<1>|/\*|\(\*\*\*)", value, maxsplit=1)[0]
    return value.strip()


def candidate_atoms(candidate: str) -> tuple[str, tuple[str, ...]]:
    """Extract solver and declaration atoms without retaining declaration IDs."""
    if re.search(r"\b(?:AXIOM|OMITTED)\b", candidate):
        raise ValueError("unsafe admission atom")
    if candidate == "OBVIOUS":
        return "obvious", ()
    if candidate.startswith("BY SMT DEF "):
        return "smt_def", tuple(x.strip() for x in candidate[11:].split(",") if x.strip())
    if candidate.startswith("BY DEF "):
        return "def", tuple(x.strip() for x in candidate[7:].split(",") if x.strip())
    if candidate.startswith("BY SMT, "):
        return "smt_facts", tuple(x.strip() for x in candidate[8:].split(",") if x.strip())
    if candidate.startswith("BY "):
        return "facts", tuple(x.strip() for x in candidate[3:].split(",") if x.strip())
    raise ValueError(f"unsupported candidate syntax: {candidate!r}")


def _bin(value: int | float, maximum: int = 8) -> str:
    return str(max(0, min(maximum, int(value))))


def declaration_graph(task: dict) -> dict:
    """Build a small lexical dependency graph from immutable source scopes."""
    dependencies = tuple(Path(path) for path in task.get("dependencies", []))
    dependency_texts = [path.read_text() for path in dependencies]
    library_paths = libraries(task["prefix"], dependency_texts, TLA_LIBRARY.split(":"))
    local = statements(task["prefix"], task["theorem_name"])
    dependency_facts = [fact for source in dependency_texts
                        for fact in statements(source, task["theorem_name"], exported=True)]
    imported_facts = [fact for path in library_paths
                      for fact in statements(path.read_text(), task["theorem_name"], exported=True)]
    nodes = {}
    for provenance, facts in (("local", local), ("dependency", dependency_facts),
                              ("imported", imported_facts)):
        for fact in facts:
            nodes.setdefault(fact["name"], {**fact, "provenance": provenance})
    names = set(nodes)
    edges = {name: {other for other in names - {name}
                    if re.search(rf"(?<![A-Za-z0-9_]){re.escape(other)}(?![A-Za-z0-9_])",
                                 node["statement"])}
             for name, node in nodes.items()}
    goal_tokens = tokens(goal_text(task))
    goal_nodes = {name for name, node in nodes.items() if goal_tokens & tokens(node["statement"])}
    return {"nodes": nodes, "edges": edges, "goal_nodes": goal_nodes,
            "library_sha256": {str(path): sha(path.read_bytes()) for path in library_paths}}


def graph_features(task: dict, candidate: str, graph: dict | None = None) -> tuple[str, ...]:
    """Return identity-light graph features for one candidate."""
    graph = graph or declaration_graph(task)
    solver, atom_names = candidate_atoms(candidate)
    nodes = graph["nodes"]
    selected = [nodes[name] for name in atom_names if name in nodes]
    selected_names = [node["name"] for node in selected]
    selected_set = set(selected_names)
    edges = graph["edges"]
    goal_nodes = graph["goal_nodes"]
    goal_tokens = tokens(goal_text(task))
    values = {
        "solver:" + solver,
        "candidate:atoms:" + _bin(len(atom_names), 16),
        "candidate:resolved:" + _bin(len(selected), 16),
        "candidate:unresolved:" + _bin(len(atom_names) - len(selected), 16),
        "candidate:provenance:local:" + _bin(sum(n["provenance"] == "local" for n in selected), 16),
        "candidate:provenance:dependency:" + _bin(sum(n["provenance"] == "dependency" for n in selected), 16),
        "candidate:provenance:imported:" + _bin(sum(n["provenance"] == "imported" for n in selected), 16),
        "graph:all_nodes:" + _bin(len(nodes), 32),
        "graph:all_edges:" + _bin(sum(len(v) for v in edges.values()), 32),
        "graph:goal_nodes:" + _bin(len(goal_nodes), 16),
        "graph:selected_goal_nodes:" + _bin(len(selected_set & goal_nodes), 16),
        "graph:selected_edges:" + _bin(sum(len(edges.get(name, ())) for name in selected_names), 16),
        "graph:internal_edges:" + _bin(sum(len(edges.get(name, ()) & selected_set) for name in selected_names), 16),
    }
    # Candidate declarations that connect to the goal via one graph hop are a
    # structural signal, not a lookup of the proof answer.
    one_hop_goal = {name for name in selected_names
                    if name in goal_nodes or edges.get(name, set()) & goal_nodes
                    or any(name in edges.get(other, set()) for other in goal_nodes)}
    values.add("graph:one_hop_goal:" + _bin(len(one_hop_goal), 16))
    overlap_bins = []
    statement_bins = []
    positions = []
    for position, node in enumerate(selected):
        node_tokens = tokens(node["statement"])
        overlap_bins.append(min(8, len(goal_tokens & node_tokens)))
        statement_bins.append(min(8, len(node_tokens)))
        positions.append(min(8, position))
        values.add("node:overlap:" + _bin(overlap_bins[-1]))
        values.add("node:statement_size:" + _bin(statement_bins[-1]))
        values.add("node:position:" + _bin(positions[-1]))
    if overlap_bins:
        values.add("aggregate:max_overlap:" + _bin(max(overlap_bins)))
        values.add("aggregate:sum_overlap:" + _bin(sum(overlap_bins), 16))
        values.add("aggregate:mean_overlap:" + _bin(round(sum(overlap_bins) / len(overlap_bins)), 8))
        values.add("aggregate:max_position:" + _bin(max(positions)))
    # Cross graph shape with the solver choice; unlike an atom-ID feature this
    # can transfer to a new declaration vocabulary.
    for shape in ("selected_goal_nodes", "internal_edges", "one_hop_goal"):
        values.add("solver_graph:" + solver + ":" + shape + ":" +
                   next(value.rsplit(":", 1)[1] for value in values
                        if value.startswith("graph:" + shape + ":")))
    return tuple(sorted(values))


def fit_logistic(examples: list[tuple[tuple[str, ...], int]], epochs=3000,
                 learning_rate=0.08, l2=0.12) -> tuple[dict[str, float], float]:
    vocabulary = sorted({token for feature_set, _ in examples for token in feature_set})
    weights = {token: 0.0 for token in vocabulary}
    bias = 0.0
    for _ in range(epochs):
        gradients = {token: l2 * value for token, value in weights.items()}
        bias_gradient = l2 * bias
        for feature_set, target in examples:
            value = max(-30.0, min(30.0, bias + sum(weights[token] for token in feature_set)))
            probability = 1.0 / (1.0 + math.exp(-value))
            delta = probability - target
            bias_gradient += delta
            for token in feature_set:
                gradients[token] += delta
        scale = learning_rate / max(1, len(examples))
        bias -= scale * bias_gradient
        for token in weights:
            weights[token] -= scale * gradients[token]
    return weights, bias


def load_tasks(manifest_path: Path) -> dict[str, dict]:
    raw = manifest_path.read_bytes()
    if sha(raw) != EXPECTED_MANIFEST_SHA:
        raise ValueError("unexpected frozen 21-task manifest")
    manifest = json.loads(raw)
    projected = {}
    # Deliberately project before any recursive inspection: this manifest is
    # archival and contains reference fragments for unrelated workflows.
    for source in manifest["tasks"]:
        projected[source["id"]] = {key: source.get(key, []) if key == "dependencies" else source[key]
                                    for key in ("id", "split", "theorem_name", "prefix", "suffix", "dependencies")}
    if set(projected) != TRAIN_IDS | HOLDOUT_IDS:
        raise ValueError("exact 17/4 task population required")
    if {projected[key]["split"] for key in TRAIN_IDS} != {"train"}:
        raise ValueError("training split mismatch")
    if {projected[key]["split"] for key in HOLDOUT_IDS} != {"development"}:
        raise ValueError("holdout split mismatch")
    return projected


def task_candidates(task: dict) -> list[str]:
    dependencies = tuple(Path(path) for path in task.get("dependencies", []))
    dependency_texts = [path.read_text() for path in dependencies]
    library_paths = libraries(task["prefix"], dependency_texts, TLA_LIBRARY.split(":"))
    candidates, _ = proposals(task["prefix"], task["theorem_name"], goal_text(task),
                              dependency_texts, [path.read_text() for path in library_paths])
    candidates = list(dict.fromkeys(candidates))
    if not 1 <= len(candidates) <= 32:
        raise ValueError(f"candidate width outside bound: {task['id']}")
    if any(not candidate.startswith("BY ") or "AXIOM" in candidate or "OMITTED" in candidate
           for candidate in candidates):
        raise ValueError(f"unsafe candidate in {task['id']}")
    return candidates


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--timeout", type=int, default=5)
    parser.add_argument("--seconds", type=int, default=900)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    if not 1 <= args.timeout <= 10 or not 60 <= args.seconds <= 900:
        parser.error("bounded timeout/seconds required")
    tasks = load_tasks(args.manifest)
    args.output.mkdir(parents=True)
    graphs = {task_id: declaration_graph(task) for task_id, task in tasks.items()}
    candidate_map = {task_id: task_candidates(task) for task_id, task in tasks.items()}
    (args.output / "candidates.json").write_text(json.dumps(candidate_map, indent=2) + "\n")
    (args.output / "graph-summary.json").write_text(json.dumps({
        task_id: {"nodes": len(graph["nodes"]), "edges": sum(map(len, graph["edges"].values())),
                  "goal_nodes": len(graph["goal_nodes"]), "library_sha256": graph["library_sha256"]}
        for task_id, graph in sorted(graphs.items())
    }, indent=2) + "\n")
    started = time.monotonic()
    examples = []
    labels = []
    with (args.output / "strict-labels.jsonl").open("x") as stream:
        for task_id in sorted(tasks):
            task = tasks[task_id]
            for index, candidate in enumerate(candidate_map[task_id]):
                if time.monotonic() + args.timeout > started + args.seconds:
                    raise TimeoutError("strict verifier budget exhausted before full 21-task coverage")
                result = certify_fragment(task["prefix"], candidate, task["suffix"],
                                          theorem_name=task["theorem_name"],
                                          dependencies=tuple(Path(x) for x in task.get("dependencies", [])),
                                          work_root=args.output / "checks" / task_id / str(index),
                                          timeout=args.timeout)
                record = {"task": task_id, "split": task["split"], "candidate_index": index,
                          "candidate": candidate, "certified": bool(result["certified"]),
                          "status": result["status"], "proved": result["proved"],
                          "total": result["total"], "seconds": result["seconds"],
                          "sha256": result["sha256"]}
                labels.append(record)
                stream.write(json.dumps(record) + "\n")
                stream.flush()
                if task_id in TRAIN_IDS:
                    examples.append((graph_features(task, candidate, graphs[task_id]),
                                     int(record["certified"])))
    weights, bias = fit_logistic(examples)
    label_map = {(row["task"], row["candidate_index"]): row["certified"] for row in labels}
    rankings = {}
    for task_id in sorted(HOLDOUT_IDS):
        task = tasks[task_id]
        values = [{"candidate_index": index, "candidate": candidate,
                   "graph_score": bias + sum(weights.get(token, 0.0)
                                               for token in graph_features(task, candidate, graphs[task_id])),
                   "certified": bool(label_map[(task_id, index)])}
                  for index, candidate in enumerate(candidate_map[task_id])]
        rankings[task_id] = sorted(values, key=lambda row: (-row["graph_score"], row["candidate_index"]))
    rank1 = sum(int(rows and rows[0]["certified"]) for rows in rankings.values())
    top4 = sum(int(any(row["certified"] for row in rows[:4])) for rows in rankings.values())
    (args.output / "holdout-rankings.json").write_text(json.dumps(rankings, indent=2) + "\n")
    (args.output / "model.json").write_text(json.dumps({
        "representation": "identity-light visible declaration dependency graph",
        "source_manifest_sha256": sha(args.manifest.read_bytes()),
        "training_tasks": sorted(TRAIN_IDS), "holdout_tasks": sorted(HOLDOUT_IDS),
        "training_examples": len(examples), "bias": bias, "weights": weights,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "official_packet_used": False,
        "quality_claim": False, "gate_claim": False,
    }, indent=2) + "\n")
    summary = {
        "kind": "proof_dependency_graph_model_v1", "strict_label_records": len(labels),
        "train_positive_labels": sum(int(row["certified"]) for row in labels if row["split"] == "train"),
        "holdout_positive_labels": sum(int(row["certified"]) for row in labels if row["split"] == "development"),
        "train_tasks": len(TRAIN_IDS), "holdout_tasks": len(HOLDOUT_IDS),
        "holdout_rank1": rank1, "holdout_top4": top4, "denominator_fixed": True,
        "checker": "strict uncached TLAPS", "training_executed": False,
        "reference_fragment_used": False, "protected_verifier_feedback_used": False,
        "repair_or_reward_used": False, "official_packet_used": False,
        "quality_claim": False, "gate_claim": False,
        "manifest_sha256": sha(args.manifest.read_bytes()),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    (args.output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
