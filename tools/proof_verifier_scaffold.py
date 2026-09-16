#!/usr/bin/env python3
"""Freeze a verifier-conditioned, answer-free retrieval scaffold.

This is deliberately narrower than ``harness.proof_retrieval``.  Trace rows
are reduced to abstract obligation shapes and the backend that discharged
them.  Proof bodies, BY/USE facts, module names, successful candidates, and
reference fragments are not copied into the index or prompts.  The resulting
packet is an inference scaffold, not training data and not proof evidence.

The source scope is closed by the caller with ``excluded_modules``.  A normal
packet excludes every module named by its frozen train/development manifest;
this prevents an exact task module from becoming a retrieval shortcut while
still allowing cross-module verifier experience to be used.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
import sys
from collections import OrderedDict
from pathlib import Path
from typing import Iterable

# Keep both ``python tools/...`` and ``python -m tools...`` entry points
# reproducible from the repository root.
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.corpora import jaccard, normalize_tla, shingle_set
from tools.proof_family_manifest import named_goals


SCHEMA_VERSION = 1
DEFAULT_K = 5
DEFAULT_SOURCES = ("corpus", "examples")

# These fields can carry a generated answer or an answer-adjacent proof
# decision.  Seeing one in an input trace is a fail-closed condition: callers
# must not silently turn a richer trace into supposedly safe retrieval data.
FORBIDDEN_TRACE_FIELDS = frozenset({
    "proof", "proof_body", "proof_module", "reference", "reference_fragment",
    "response", "answer", "candidate", "candidates", "by_facts", "successful_candidate",
})

_IDENTIFIER = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_NUMBER = re.compile(r"^[0-9]+(?:\.[0-9]+)?$")

_KEYWORDS = frozenset({
    "ASSUME", "PROVE", "NEW", "VARIABLE", "THEOREM", "LEMMA", "COROLLARY",
    "PROPOSITION", "AXIOM", "UNCHANGED", "IF", "THEN", "ELSE", "CASE",
    "SUFFICES", "WITNESS", "QED", "OBVIOUS", "BY", "DEF", "USE", "HAVE",
    "PICK", "CHOOSE", "EXCEPT", "DOMAIN", "SUBSET", "BOOLEAN", "Nat", "Int",
    "Real", "TRUE", "FALSE", "INSTANCE", "EXTENDS", "LOCAL", "LET", "IN",
    "ENABLED", "WF", "SF",
})
_BACKSLASH_OPERATORS = frozenset({"A", "E", "in", "notin", "subseteq", "subset"})


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _abstract_tokens(text: str) -> list[str]:
    """Replace user identifiers and literals while retaining TLA+ syntax."""
    result = []
    raw = normalize_tla(text)
    tokens = []
    index = 0
    while index < len(raw):
        if raw[index] == "\\" and index + 1 < len(raw) and raw[index + 1] in _BACKSLASH_OPERATORS:
            tokens.append("\\" + raw[index + 1])
            index += 2
        else:
            tokens.append(raw[index])
            index += 1
    for token in tokens:
        if _NUMBER.fullmatch(token):
            result.append("<num>")
        elif _IDENTIFIER.fullmatch(token) and token not in _KEYWORDS:
            result.append("<id>")
        else:
            result.append(token)
    return result


def obligation_shape(text: str) -> dict:
    """Return a deterministic, answer-free structural signature for a goal."""
    raw_tokens = normalize_tla(text or "")
    tokens = _abstract_tokens(text or "")
    counts = {
        "tokens": len(tokens),
        "identifiers": sum(t == "<id>" for t in tokens),
        "numbers": sum(t == "<num>" for t in tokens),
        "quantifiers": sum(t in {r"\A", r"\E"} for t in tokens),
        "conjunctions": tokens.count("/\\"),
        "disjunctions": tokens.count(r"\/"),
        "implications": tokens.count("=>"),
        "membership": sum(t in {r"\in", r"\notin", r"\subseteq", "SUBSET"} for t in tokens),
        "temporal": sum(t in {"[]", "<>", "~>", "WF", "SF"} for t in tokens),
        "primed": tokens.count("'"),
        "unchanged": tokens.count("UNCHANGED"),
        "assumptions": tokens.count("ASSUME"),
        "propositions": tokens.count("PROVE"),
    }
    if counts["tokens"] < 16:
        length = "short"
    elif counts["tokens"] < 64:
        length = "medium"
    else:
        length = "long"
    # raw_tokens is intentionally used only to decide whether the input was
    # nonempty; no raw token stream is exported.
    return {
        "signature": " ".join(tokens),
        "features": dict(counts, length=length, nonempty=bool(raw_tokens)),
    }


def _safe_entry(row: dict, ordinal: int) -> dict | None:
    if FORBIDDEN_TRACE_FIELDS & set(row):
        raise ValueError("trace row contains answer-bearing field")
    shape = obligation_shape(row.get("obligation_text", ""))
    if not shape["features"]["nonempty"]:
        return None
    # Do not carry module identity or source paths into the safe index.  The
    # opaque id is only for deterministic audit/debugging, never prompt text.
    identity = "\x00".join([
        shape["signature"], str(row.get("backend") or "unknown"),
        str(row.get("theorem_kind") or "unknown"), str(ordinal),
    ]).encode()
    source = row.get("source")
    return {
        "entry_id": "shape-" + sha(identity)[:16],
        "shape_signature": shape["signature"],
        "features": shape["features"],
        "backend": row.get("backend") or "unknown",
        "theorem_kind": row.get("theorem_kind") or "unknown",
        "source_kind": source if source in DEFAULT_SOURCES else "other",
        "support_count": 1,
    }


def build_index(trace_dirs: Iterable[str | Path], out_path: str | Path,
                *, excluded_modules: Iterable[str] = (),
                allowed_sources: Iterable[str] = DEFAULT_SOURCES) -> list[dict]:
    """Build a safe abstract index from proved trace rows only.

    Duplicate shape/backend/kind observations are collapsed and counted.  A
    module in ``excluded_modules`` is skipped before any data from it can
    enter the index.  No answer-bearing fields are tolerated, even when they
    would otherwise be ignored.
    """
    excluded = set(excluded_modules)
    allowed = set(allowed_sources)
    entries: OrderedDict[tuple, dict] = OrderedDict()
    for trace_dir in trace_dirs:
        rows_path = Path(trace_dir) / "rows.jsonl"
        if not rows_path.exists():
            continue
        with rows_path.open() as stream:
            for ordinal, line in enumerate(stream):
                line = line.strip()
                if not line:
                    continue
                row = json.loads(line)
                if FORBIDDEN_TRACE_FIELDS & set(row):
                    raise ValueError("trace row contains answer-bearing field")
                if row.get("status") != "proved" or row.get("source") not in allowed:
                    continue
                if row.get("module") in excluded:
                    continue
                item = _safe_entry(row, ordinal)
                if item is None:
                    continue
                key = (item["shape_signature"], item["backend"], item["theorem_kind"])
                previous = entries.get(key)
                if previous is None:
                    entries[key] = item
                else:
                    previous["support_count"] += 1
                    if previous["source_kind"] != item["source_kind"]:
                        previous["source_kind"] = "mixed"
    output = Path(out_path)
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w") as stream:
        for item in entries.values():
            stream.write(json.dumps(item, sort_keys=True) + "\n")
    return list(entries.values())


def _trace_inventory(trace_dirs: Iterable[str | Path]) -> list[dict]:
    inventory = []
    for trace_dir in trace_dirs:
        rows_path = Path(trace_dir) / "rows.jsonl"
        if rows_path.exists():
            data = rows_path.read_bytes()
            inventory.append({"path": str(rows_path), "sha256": sha(data), "bytes": len(data)})
    return inventory


def load_index(index_path: str | Path) -> list[dict]:
    entries = []
    with Path(index_path).open() as stream:
        for line in stream:
            if line.strip():
                item = json.loads(line)
                if FORBIDDEN_TRACE_FIELDS & set(item):
                    raise ValueError("safe index contains answer-bearing field")
                entries.append(item)
    return entries


def query(index: list[dict] | str | Path, obligation_text: str, k: int = DEFAULT_K) -> list[dict]:
    if not 1 <= k <= 16:
        raise ValueError("retrieval k must be 1..16")
    if isinstance(index, (str, Path)):
        index = load_index(index)
    query_shape = obligation_shape(obligation_text)
    q_shingles = shingle_set(query_shape["signature"].split())
    if not q_shingles:
        return []
    ranked = []
    for item in index:
        signature = item.get("shape_signature", "")
        score = jaccard(q_shingles, shingle_set(signature.split()))
        if score > 0:
            ranked.append((score, item))
    ranked.sort(key=lambda pair: pair[0], reverse=True)
    result = []
    for score, item in ranked[:k]:
        # Return only fields intended for prompt construction.  In particular,
        # the opaque id and support count are audit metadata, not proof advice.
        result.append({
            "shape_signature": item["shape_signature"],
            "features": item["features"],
            "backend": item["backend"],
            "theorem_kind": item["theorem_kind"],
            "source_kind": item["source_kind"],
            "support_count": item["support_count"],
            "score": score,
        })
    return result


def render_hits(hits: list[dict]) -> str:
    """Render structural/verifier context; never render a proof or fact name."""
    if not hits:
        return "(no structurally similar proved-obligation profiles)"
    lines = []
    for i, hit in enumerate(hits, 1):
        features = hit["features"]
        compact = ", ".join(
            f"{key}={features[key]}" for key in
            ("length", "quantifiers", "conjunctions", "implications", "membership", "temporal", "primed")
        )
        lines.append(
            f"[{i}] shape={hit['shape_signature'][:240]}\n"
            f"    verifier_backend={hit['backend']}; theorem_kind={hit['theorem_kind']}; "
            f"source_scope={hit['source_kind']}; similarity={hit['score']:.3f}; {compact}")
    return "\n".join(lines)


def build_prompt(prefix: str, theorem_name: str, goal: str, hits: list[dict],
                 verifier_state: dict | None = None) -> str:
    """Build an answer-free, verifier-conditioned proof-hole prompt."""
    if not prefix or not theorem_name or not goal:
        raise ValueError("prefix, theorem name, and goal are required")
    state = verifier_state or {}
    state_line = (
        f"sany={state.get('sany', 'not-run')}; "
        f"failed_obligations={state.get('failed_obligations', 'unknown')}; "
        f"last_backend={state.get('last_backend', 'none')}"
    )
    return "\n".join([
        "Produce one valid next TLAPS proof action for the named theorem.",
        "The source prefix is fixed. Do not change definitions, introduce axioms,",
        "use an answer, or emit a complete replacement module.",
        "Return only a proof action or proof block beginning with a TLAPS keyword.",
        "",
        "===BEGIN FIXED SOURCE PREFIX===",
        prefix,
        "<PROOF_HOLE>",
        "===END FIXED SOURCE PREFIX===",
        "",
        f"theorem={theorem_name}",
        f"goal={goal}",
        f"verifier_state={state_line}",
        "",
        "Verifier-conditioned structural profiles (statements and proof bodies withheld):",
        render_hits(hits),
    ])


def _task_goal(task: dict) -> str:
    goal = task.get("target_goal")
    if goal:
        return goal
    goals = named_goals(task.get("prefix", ""))
    if not goals:
        raise ValueError(f"target statement missing: {task.get('id')}")
    return goals[-1]


def prepare_packet(manifest_path: str | Path, index_path: str | Path,
                   output: str | Path, *, split: str = "train", k: int = DEFAULT_K) -> dict:
    manifest_path = Path(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    tasks = [task for task in manifest.get("tasks", []) if task.get("split") == split]
    if not tasks or len({task["id"] for task in tasks}) != len(tasks):
        raise ValueError("requested split is empty or has duplicate task ids")
    index = load_index(index_path)
    rows = []
    for task in tasks:
        goal = _task_goal(task)
        hits = query(index, goal, k=k)
        prompt = build_prompt(task["prefix"], task["theorem_name"], goal, hits)
        rows.append({
            "id": task["id"],
            "split": split,
            "source_family": task.get("source_family"),
            "theorem_name": task["theorem_name"],
            "goal_shape": obligation_shape(goal),
            "retrieval_hits": hits,
            "prompt": prompt,
            "prompt_sha256": sha(prompt.encode()),
        })
    packet = {
        "schema_version": SCHEMA_VERSION,
        "packet_kind": "answer_free_verifier_conditioned_retrieval",
        "manifest_sha256": sha(manifest_path.read_bytes()),
        "index_sha256": sha(Path(index_path).read_bytes()),
        "index_config_sha256": (
            sha((Path(index_path).with_name("index-config.json")).read_bytes())
            if Path(index_path).with_name("index-config.json").exists() else None
        ),
        "split": split,
        "rows": rows,
        "denominator": len(rows),
        "reference_fragment_used": False,
        "reference_fragment_exported": False,
        "proof_bodies_exported": False,
        "successful_candidates_exported": False,
        "model_executed": False,
        "training_executed": False,
        "parameter_updates": 0,
        "proof_or_quality_claim": False,
        "scope": "CPU-frozen prompt scaffold; no model, training, or proof-gate result",
    }
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_text(json.dumps(packet, indent=2) + "\n")
    (output / "summary.json").write_text(json.dumps({
        "packet_sha256": sha((output / "packet.json").read_bytes()),
        "tasks": len(rows),
        "nonempty_retrieval": sum(bool(row["retrieval_hits"]) for row in rows),
        "reference_fragment_used": False,
        "model_executed": False,
        "training_executed": False,
        "proof_or_quality_claim": False,
    }, indent=2) + "\n")
    return packet


def _check_fresh_controls(manifest_path: Path, controls_dir: Path) -> dict:
    controls = json.loads((controls_dir / "controls.json").read_text())
    identity = json.loads((controls_dir / "verifier_identity.json").read_text())
    expected_manifest = sha(manifest_path.read_bytes())
    train = [task for task in json.loads(manifest_path.read_text())["tasks"] if task.get("split") == "train"]
    expected_ids = {task["id"] for task in train}
    pairs = {(row.get("id"), row.get("control")) for row in controls}
    expected_pairs = {(task_id, control) for task_id in expected_ids for control in ("reference", "omitted")}
    if len(train) != 17 or len(controls) != 34 or pairs != expected_pairs:
        raise ValueError("fresh controls do not cover the exact 17-task denominator")
    if (
        identity.get("complete") is not True
        or identity.get("manifest_sha256") != expected_manifest
        or identity.get("completed_controls") != 34
        or identity.get("controls_sha256") != sha((controls_dir / "controls.json").read_bytes())
        or identity.get("before") != identity.get("after")
    ):
        raise ValueError("fresh verifier identity is incomplete or changed")
    for row in controls:
        if row["control"] == "reference":
            if not (row.get("expected") is True and row.get("certified") is True
                    and row.get("status") == "pass" and row.get("proved", 0) == row.get("total", 0) > 0):
                raise ValueError("positive verifier control failed: " + row["id"])
        elif row["control"] == "omitted":
            if not (row.get("expected") is False and row.get("certified") is False
                    and row.get("status") == "contract_reject"):
                raise ValueError("omitted negative verifier control failed: " + row["id"])
    return {
        "manifest_sha256": expected_manifest,
        "controls_sha256": sha((controls_dir / "controls.json").read_bytes()),
        "verifier_identity_sha256": sha((controls_dir / "verifier_identity.json").read_bytes()),
        "controls": len(controls),
        "train_tasks": len(train),
        "reference_controls_passed": sum(row["control"] == "reference" for row in controls),
        "omitted_controls_rejected": sum(row["control"] == "omitted" for row in controls),
    }


def audit_admission(manifest_path: str | Path, train_packet_path: str | Path,
                    development_packet_path: str | Path, controls_dir: str | Path,
                    output: str | Path) -> dict:
    """Bind safe packets to fresh verifier controls and frozen denominators."""
    manifest_path, controls_dir = Path(manifest_path), Path(controls_dir)
    train_packet = json.loads(Path(train_packet_path).read_text())
    development_packet = json.loads(Path(development_packet_path).read_text())
    expected_manifest = sha(manifest_path.read_bytes())
    for packet, split, denominator in ((train_packet, "train", 17), (development_packet, "development", 4)):
        if (packet.get("manifest_sha256") != expected_manifest or packet.get("split") != split
                or packet.get("denominator") != denominator or len(packet.get("rows", [])) != denominator
                or packet.get("reference_fragment_used") is not False
                or packet.get("reference_fragment_exported") is not False
                or packet.get("proof_bodies_exported") is not False
                or packet.get("successful_candidates_exported") is not False
                or packet.get("model_executed") is not False
                or packet.get("training_executed") is not False
                or packet.get("parameter_updates") != 0
                or packet.get("proof_or_quality_claim") is not False):
            raise ValueError(f"{split} packet is not an answer-free frozen packet")
        for row in packet["rows"]:
            if FORBIDDEN_TRACE_FIELDS & set(row):
                raise ValueError(f"answer-bearing field in {split} packet row")
    manifest = json.loads(manifest_path.read_text())
    by_id = {task["id"]: task for task in manifest["tasks"]}
    for packet in (train_packet, development_packet):
        for row in packet["rows"]:
            fragment = by_id[row["id"]].get("reference_fragment", "")
            if fragment and fragment in row["prompt"]:
                raise ValueError("reference fragment bytes entered a packet prompt: " + row["id"])
    controls = _check_fresh_controls(manifest_path, controls_dir)
    official = json.loads((ROOT / "corpus/lmgpa/manifest.json").read_text())
    secondary = json.loads((ROOT / "corpus/holdout_30.json").read_text())
    official_count = len(official["tasks"] if isinstance(official, dict) and "tasks" in official else official)
    secondary_count = (len(secondary["holdout_specs"])
                       if isinstance(secondary, dict) and "holdout_specs" in secondary else len(secondary))
    if official_count != 119 or secondary_count != 30:
        raise ValueError("protected denominator changed")
    result = {
        "schema_version": SCHEMA_VERSION,
        "kind": "cpu_answer_free_verifier_scaffold_admission",
        "verified_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z"),
        "manifest_sha256": expected_manifest,
        "train_packet_sha256": sha(Path(train_packet_path).read_bytes()),
        "development_packet_sha256": sha(Path(development_packet_path).read_bytes()),
        "index_sha256": train_packet["index_sha256"],
        "controls": controls,
        "protected_denominators": {
            "official119": {"count": official_count, "manifest_sha256": sha((ROOT / "corpus/lmgpa/manifest.json").read_bytes())},
            "official30": {"count": secondary_count, "manifest_sha256": sha((ROOT / "corpus/holdout_30.json").read_bytes())},
        },
        "train_packet": {"tasks": 17, "nonempty_retrieval": sum(bool(row["retrieval_hits"]) for row in train_packet["rows"])},
        "development_packet": {"tasks": 4, "nonempty_retrieval": sum(bool(row["retrieval_hits"]) for row in development_packet["rows"])},
        "admitted": True,
        "model_executed": False,
        "training_executed": False,
        "proof_or_quality_claim": False,
        "scope": "CPU packet integrity and verifier controls only; no model, GPU, proof-gate, or quality claim",
        "implementation_sha256": sha(Path(__file__).read_bytes()),
    }
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + "\n")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build-index")
    build.add_argument("trace_dirs", nargs="+")
    build.add_argument("--out", required=True, type=Path)
    build.add_argument("--exclude-module", action="append", default=[])
    prep = sub.add_parser("prepare")
    prep.add_argument("--manifest", required=True, type=Path)
    prep.add_argument("--index", required=True, type=Path)
    prep.add_argument("--output", required=True, type=Path)
    prep.add_argument("--split", choices=("train", "development"), default="train")
    prep.add_argument("--k", type=int, default=DEFAULT_K)
    audit = sub.add_parser("audit")
    audit.add_argument("--manifest", required=True, type=Path)
    audit.add_argument("--train-packet", required=True, type=Path)
    audit.add_argument("--development-packet", required=True, type=Path)
    audit.add_argument("--controls", required=True, type=Path)
    audit.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    if args.command == "build-index":
        entries = build_index(args.trace_dirs, args.out, excluded_modules=args.exclude_module)
        config = {
            "schema_version": SCHEMA_VERSION,
            "kind": "answer_free_verifier_trace_index",
            "trace_rows": _trace_inventory(args.trace_dirs),
            "excluded_modules": sorted(set(args.exclude_module)),
            "allowed_sources": list(DEFAULT_SOURCES),
            "entries": len(entries),
            "index_sha256": sha(args.out.read_bytes()),
            "safe_fields": ["shape_signature", "features", "backend", "theorem_kind", "source_kind", "support_count"],
            "forbidden_trace_fields": sorted(FORBIDDEN_TRACE_FIELDS),
            "proof_or_quality_claim": False,
        }
        args.out.with_name("index-config.json").write_text(json.dumps(config, indent=2) + "\n")
        print(json.dumps({"entries": len(entries), "output": str(args.out)}))
    elif args.command == "prepare":
        packet = prepare_packet(args.manifest, args.index, args.output, split=args.split, k=args.k)
        print(json.dumps({"tasks": len(packet["rows"]), "nonempty_retrieval": sum(bool(r["retrieval_hits"]) for r in packet["rows"]), "reference_fragment_used": False}))
    else:
        result = audit_admission(args.manifest, args.train_packet, args.development_packet, args.controls, args.output)
        print(json.dumps({"admitted": result["admitted"], "official119": 119, "official30": 30, "proof_or_quality_claim": False}))


if __name__ == "__main__":
    main()
