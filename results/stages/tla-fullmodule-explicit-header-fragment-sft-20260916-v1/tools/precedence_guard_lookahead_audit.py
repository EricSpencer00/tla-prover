"""Bounded liveness audit for the layout and precedence decoder guards.

This is a CPU-only decoder diagnostic.  It does not run SANY, inspect model
weights, or grant proof/quality credit.  The search treats tokenizer pieces as
finite scored alternatives and uses bounded depth-first backtracking: a piece
is rejected before it is committed when either audited guard fires, and a
branch that later has no continuation is abandoned without post-hoc repair.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.layout_junction_audit import line_guard, known_good as layout_known_good
from tools.precedence_guard_audit import known_good as precedence_known_good
from tools.precedence_guard_audit import precedence_guard


@dataclass(frozen=True)
class Edge:
    label: str
    piece: str
    next_state: str
    score: float


@dataclass(frozen=True)
class Scenario:
    name: str
    prefix: str
    transitions: dict[str, tuple[Edge, ...]]
    start_state: str = "start"
    terminal_states: frozenset[str] = frozenset({"done"})
    max_depth: int = 8
    max_nodes: int = 64


def digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def guard_hits(text: str) -> dict[str, list[dict]]:
    return {"layout": line_guard(text), "precedence": precedence_guard(text)}


def successful_path(scenario: Scenario) -> dict:
    """Find one terminating path, preserving scored order and backtracking."""
    nodes = 0
    guard_rejections = 0
    dead_ends = 0

    def visit(text: str, state: str, path: tuple[Edge, ...], depth: int):
        nonlocal nodes, guard_rejections, dead_ends
        nodes += 1
        if state in scenario.terminal_states:
            return path, text
        if nodes > scenario.max_nodes or depth >= scenario.max_depth:
            dead_ends += 1
            return None
        edges = sorted(scenario.transitions.get(state, ()),
                       key=lambda edge: (-edge.score, edge.label))
        if not edges:
            dead_ends += 1
            return None
        for edge in edges:
            candidate = text + edge.piece
            hits = guard_hits(candidate)
            if hits["layout"] or hits["precedence"]:
                guard_rejections += 1
                continue
            result = visit(candidate, edge.next_state, path + (edge,), depth + 1)
            if result is not None:
                return result
        dead_ends += 1
        return None

    result = visit(scenario.prefix, scenario.start_state, tuple(), 0)
    if result is None:
        return {
            "status": "closed",
            "nodes": nodes,
            "guard_rejections": guard_rejections,
            "dead_ends": dead_ends,
            "path": [],
            "text_sha256": None,
        }
    path, text = result
    return {
        "status": "terminated",
        "nodes": nodes,
        "guard_rejections": guard_rejections,
        "dead_ends": dead_ends,
        "path": [{"label": edge.label, "piece": edge.piece,
                  "score": edge.score} for edge in path],
        "text_sha256": digest(text),
        "text": text,
    }


def scenarios() -> tuple[Scenario, ...]:
    # The higher-scored inline branch creates the exact same-line definition
    # shape seen in row 107.  The lower-scored newline branch is the finite
    # continuation that bounded backtracking must find.
    definition_prefix = (
        "---- MODULE M ----\n"
        "post(b) == snapshot' = snapshot"
    )
    definition = Scenario(
        name="model_shaped_mixed_definition",
        prefix=definition_prefix,
        transitions={
            "start": (
                Edge("inline-or", " \\/ event' = event", "inline-or", 10.0),
                Edge("newline-and", "\n  /\\ event' = event", "newline-and", 8.0),
            ),
            "inline-or": (
                Edge("same-line-and", " /\\ holder' = b", "dead", 10.0),
            ),
            "newline-and": (Edge("module-end", "\n====", "done", 1.0),),
            "dead": (),
        },
    )

    # The higher-scored same-line conjunction is the observed quantified
    # prime form from row 47.  A deeper-indented continuation remains outside
    # the same-indent junction run and is therefore a valid finite branch.
    quantified_prefix = (
        "---- MODULE M ----\n"
        "Next ==\n"
        "  \\/ \\E d \\in D : active'[d] = active[d]"
    )
    quantified = Scenario(
        name="model_shaped_quantified_prime",
        prefix=quantified_prefix,
        transitions={
            "start": (
                Edge("same-line-and", " /\\ ready'[d] = TRUE", "dead", 10.0),
                Edge("deeper-and", "\n    /\\ ready'[d] = TRUE", "deeper-and", 8.0),
            ),
            "deeper-and": (Edge("module-end", "\n====", "done", 1.0),),
            "dead": (),
        },
    )

    # This negative control has only a finite, guard-passing prefix and then
    # no outgoing token.  The diagnostic must close it rather than inventing
    # a fallback or declaring liveness.
    no_continuation = Scenario(
        name="finite_no_continuation_control",
        prefix=definition_prefix,
        transitions={
            "start": (Edge("inline-or", " \\/ event' = event", "dead", 10.0),),
            "dead": (),
        },
    )
    return definition, quantified, no_continuation


def audit_known_good() -> dict:
    layout_paths = {path.resolve(): path for path in layout_known_good()}
    precedence_paths = {path.resolve(): path for path in precedence_known_good()}
    paths = sorted(set(layout_paths) | set(precedence_paths), key=str)
    records = []
    layout_false_rejects = 0
    precedence_false_rejects = 0
    for path in paths:
        text = path.read_text(errors="replace")
        layout_hits = line_guard(text)
        precedence_hits = precedence_guard(text)
        layout_false_rejects += bool(layout_hits)
        precedence_false_rejects += bool(precedence_hits)
        records.append({"path": str(path), "sha256": digest(text),
                        "layout_hits": layout_hits,
                        "precedence_hits": precedence_hits})
    return {
        "requested": len(records),
        "layout_false_rejects": layout_false_rejects,
        "precedence_false_rejects": precedence_false_rejects,
        "records": records,
    }


def targeted_controls() -> dict:
    mixed = (
        "---- MODULE M ----\n"
        "post(b) == snapshot' = snapshot \\/ event' = event /\\ holder' = b\n"
        "===="
    )
    quantified = (
        "---- MODULE M ----\n"
        "Next ==\n"
        "  \\/ \\E d \\in D : active'[d] = active[d] /\\ ready'[d] = TRUE\n"
        "===="
    )
    ordinary = (
        "---- MODULE M ----\n"
        "Next ==\n"
        "  \\/ active' = active\n"
        "  \\/ active' = active + 1\n"
        "===="
    )
    return {
        "mixed_definition": {"hits": precedence_guard(mixed),
                             "layout_hits": line_guard(mixed)},
        "quantified_prime": {"hits": precedence_guard(quantified),
                             "layout_hits": line_guard(quantified)},
        "ordinary": {"hits": precedence_guard(ordinary),
                     "layout_hits": line_guard(ordinary)},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.parent.mkdir(parents=True, exist_ok=True)

    known_good = audit_known_good()
    controls = targeted_controls()
    searches = {scenario.name: successful_path(scenario)
                for scenario in scenarios()}

    result = {
        "kind": "precedence_guard_bounded_lookahead_audit_v1",
        "known_good": known_good,
        "targeted_controls": controls,
        "searches": searches,
        "contract": {
            "cpu_only": True,
            "bounded_backtracking": True,
            "guard_before_commit": True,
            "posthoc_repair": False,
            "sany_claim": False,
            "model_improvement_claim": False,
            "gate_claim": False,
        },
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")

    ok = (
        known_good["requested"] == 438 and
        known_good["layout_false_rejects"] == 0 and
        known_good["precedence_false_rejects"] == 0 and
        bool(controls["mixed_definition"]["hits"]) and
        bool(controls["quantified_prime"]["hits"]) and
        not controls["ordinary"]["hits"] and
        not controls["ordinary"]["layout_hits"] and
        searches["model_shaped_mixed_definition"]["status"] == "terminated" and
        searches["model_shaped_quantified_prime"]["status"] == "terminated" and
        searches["finite_no_continuation_control"]["status"] == "closed"
    )
    print(json.dumps({
        "kind": result["kind"],
        "known_good_requested": known_good["requested"],
        "layout_false_rejects": known_good["layout_false_rejects"],
        "precedence_false_rejects": known_good["precedence_false_rejects"],
        "search_status": {name: item["status"] for name, item in searches.items()},
        "pass": ok,
        "claims": result["contract"],
    }, sort_keys=True))
    if not ok:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
