#!/usr/bin/env python3
"""Freeze human-skeleton, multi-token proof-repair development tasks.

This is not an official benchmark or a generalization evaluation. No model is
called and no training occurs. Official source texts are read for exclusion only.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.corpora import normalize_tla, shingle_set, jaccard
from harness.runner import TLAPM, TLA_LIBRARY, run_cmd

# Inclusive one-based upstream source spans: target declaration, target end,
# replaced proof fragment start/end. Statements and other proof steps are frozen.
SELECTION = [
    ("addtwo-init", "AddTwo", "TypeInvariant", 36, 43, 38, 38),
    ("addtwo-step", "AddTwo", "TypeInvariant", 36, 43, 42, 42),
    ("highest-type-step", "FindHighest", "TypeInvariantHolds", 74, 96, 92, 92),
    ("highest-inductive-step", "FindHighest", "InductiveInvariantHolds", 104, 117, 114, 114),
    ("highest-done-step", "FindHighest", "DoneIndexValueThm", 122, 134, 132, 132),
    ("highest-correctness", "FindHighest", "IsCorrect", 143, 147, 145, 145),
]


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def freeze_fragment_boundaries(prefix, fragment, suffix):
    """Whitespace belongs to scaffold, not a stripped model completion.

    Move only outer whitespace, preserving exact reference assembly including
    any internal indentation/newlines in a multi-line proof fragment.
    """
    content = fragment.strip()
    if not content:
        raise ValueError("empty proof fragment")
    leading = len(fragment) - len(fragment.lstrip())
    trailing_start = len(fragment.rstrip())
    result = (prefix + fragment[:leading], content, fragment[trailing_start:] + suffix)
    assert "".join(result) == prefix + fragment + suffix
    return result


def declarations(text):
    """Conservative textual named-goal spans; source comparisons remain primary."""
    pattern = r"(?m)^\s*(?:THEOREM|LEMMA)\s+([A-Za-z_][A-Za-z_0-9]*)\s*==([^\n]*)"
    return [m.group(0).strip() for m in re.finditer(pattern, text)]


def build_manifest(lmgpa_root, holdout_root):
    official = []
    manifest_path = ROOT / "corpus/lmgpa/manifest.json"
    for entry in json.loads(manifest_path.read_text()):
        path = lmgpa_root / entry["module_file"]
        text = path.read_text()
        if hashlib.sha256(path.read_bytes()).hexdigest() != entry["sha256"]:
            raise ValueError(f"official119 source hash mismatch: {path}")
        official.append(("official119:" + entry["id"], path, text))
    holdout_path = ROOT / "corpus/holdout_30.json"
    for ident in json.loads(holdout_path.read_text())["holdout_specs"]:
        path = holdout_root / f"{ident}.tla"
        official.append((f"official30:{ident}", path, path.read_text()))
    refs = [(ident, shingle_set(normalize_tla(text))) for ident, _, text in official]
    goal_refs = [(ident, shingle_set(normalize_tla(goal)))
                 for ident, _, text in official for goal in declarations(text)]
    examples = ROOT / "tools/tlaplus-examples"
    commit = subprocess.check_output(["git", "-C", str(examples), "rev-parse", "HEAD"], text=True).strip()
    tasks = []
    excluded = []
    for ident, module, theorem, begin, end, lo, hi in SELECTION:
        path = examples / "specifications/LearnProofs" / f"{module}.tla"
        text = path.read_text()
        lines = text.splitlines(keepends=True)
        assert re.search(rf"THEOREM\s+{theorem}\s*==", lines[begin - 1])
        prefix = "".join(lines[:lo - 1])
        fragment = "".join(lines[lo - 1:hi])
        suffix = "".join(lines[hi:end]) + "\n=============================================================================\n"
        assert fragment.strip().startswith("BY ") and len(fragment.split()) >= 4
        prefix, fragment, suffix = freeze_fragment_boundaries(prefix, fragment, suffix)
        assembled = prefix + fragment + suffix
        goals = "".join(lines[begin - 1:lo - 1])
        comparisons = {}
        for label, content, pool in [("source", text, refs), ("assembled", assembled, refs),
                                     ("target_context", goals, refs),
                                     ("named_goal", lines[begin - 1], goal_refs)]:
            query = shingle_set(normalize_tla(content))
            ranked = sorted(((jaccard(query, ref), name) for name, ref in pool), reverse=True)
            comparisons[label] = {"max_jaccard": ranked[0][0], "nearest": ranked[0][1]}
        # Exact normalized full sources plus shingle similarity; goal spans are
        # recorded and conservatively excluded too (short goals can be generic).
        if any(v["max_jaccard"] >= .65 for v in comparisons.values()):
            excluded.append({"id": ident, "comparisons": comparisons})
            continue
        tasks.append({
            "id": ident, "module_name": module, "theorem_name": theorem,
            "prefix": prefix, "suffix": suffix, "reference_fragment": fragment,
            "dependencies": [], "source_path": str(path), "source_sha256": digest(text),
            "assembled_sha256": digest(assembled), "source_commit": commit,
            "source_repository": "https://github.com/tlaplus/Examples",
            "source_dirty": subprocess.check_output(["git", "-C", str(examples), "status", "--porcelain", "--", str(path)], text=True).strip(),
            "source_theorem_lines": [begin, end], "source_fragment_lines": [lo, hi],
            "standard_dependencies": [x.strip() for x in re.search(r"(?m)^EXTENDS (.+)$", text).group(1).split(",")],
            "expected_facts": fragment.strip(), "expected_backend": "SMT/default portfolio; PTL for frozen temporal QED",
            "decontamination": comparisons,
            "task_contract": "Replace one complete multi-token BY proof fragment only; theorem and skeleton immutable. Later unrelated declarations removed; prior human proofs retained.",
        })
    return {"schema_version": 2, "fragment_boundary_contract": "Outer whitespace is immutable scaffold; reference_fragment equals its stripped form.",
            "kind": "human_skeleton_proof_repair_development",
            "not_generalization": True, "official_tasks_evaluated": 0,
            "decontamination_threshold": .65,
            "decontamination_method": "repository normalize_tla + shingle_set + Jaccard; conservative lexical exclusion, not semantic-equivalence certification",
            "official119_manifest_sha256": digest(manifest_path.read_text()),
            "official30_manifest_sha256": digest(holdout_path.read_text()),
            "official_sources": [{"id": ident, "path": str(p), "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for ident, p, t in official],
            "tasks": tasks, "excluded": excluded}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lmgpa-root", type=Path, default=Path("/Users/eric/GitHub/lmgpa"))
    parser.add_argument("--holdout-root", type=Path, default=Path("/Users/eric/GitHub/tla_benchmark/data/tla_files"))
    parser.add_argument("--verify-references", action="store_true")
    parser.add_argument("--timeout", type=int, default=45)
    args = parser.parse_args()
    manifest = build_manifest(args.lmgpa_root, args.holdout_root)
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    if args.verify_references:
        results = []
        for task in manifest["tasks"]:
            work = args.output / task["id"]
            work.mkdir()
            tla = work / (task["module_name"] + ".tla")
            tla.write_text(task["prefix"] + task["reference_fragment"] + task["suffix"])
            flags = [flag for directory in TLA_LIBRARY.split(":") for flag in ("-I", directory)]
            rc, log, seconds, timeout = run_cmd([str(TLAPM), "--strict", "--nofp", "--toolbox", "0", "0", "--printallobs", *flags, tla.name], work, args.timeout)
            (work / "tlapm.log").write_text(log)
            results.append({"id": task["id"], "returncode": rc, "timeout": timeout, "seconds": seconds,
                            "all_proved_summary": re.findall(r"All (\d+) obligations? proved", log),
                            "strict_reference_control_only": True})
            (args.output / "reference_controls.json").write_text(json.dumps(results, indent=2) + "\n")
            print(json.dumps(results[-1]), flush=True)
    print(json.dumps({"tasks": len(manifest["tasks"]), "excluded": manifest["excluded"], "output": str(args.output)}))


if __name__ == "__main__":
    main()
