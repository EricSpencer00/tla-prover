r"""Audit a conservative indentation-aware TLA+ junction guard.

The guard is intentionally narrow: within one contiguous run of same-indent
lines beginning with ``\/`` or ``/\``, reject a disjunction-to-conjunction
switch.  It targets the observed row-47 precedence failure while preserving
ordinary same-line TLA+ expressions and nested, more-indented conjunctions.
This is a decoder-preflight measurement, not a SANY or quality claim.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
JUNCTION = re.compile(r"^(\s*)(/\\|\\/)(?:\s|$)")
MODULE = re.compile(r"^\s*-{4,}\s*MODULE\b", re.M)
END = re.compile(r"^={4,}\s*$", re.M)


def module_region(text):
    match = MODULE.search(text)
    if not match:
        return text
    rest = text[match.start():]
    end = END.search(rest)
    return rest[:end.end()] + "\n" if end else rest


def line_guard(text):
    lines = module_region(text).splitlines()
    hits = []
    index = 0
    while index < len(lines):
        match = JUNCTION.match(lines[index])
        if not match:
            index += 1
            continue
        indent = len(match.group(1))
        run = []
        cursor = index
        while cursor < len(lines):
            current = JUNCTION.match(lines[cursor])
            if not current or len(current.group(1)) != indent:
                break
            run.append((cursor + 1, current.group(2)))
            cursor += 1
        families = {"or" if op == "\\/" else "and" for _, op in run}
        if families == {"or", "and"}:
            hits.append({"start_line": index + 1, "end_line": cursor,
                         "indent": indent, "operators": run})
        index = max(cursor, index + 1)
    return hits


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def known_good():
    paths = sorted((ROOT / "tools/tlaplus-examples").rglob("*.tla"))
    corpus = Path("/Users/eric/GitHub/tla_benchmark/data/tla_files")
    if corpus.is_dir():
        holdout = json.loads((ROOT / "corpus/holdout_30.json").read_text())
        if isinstance(holdout, dict):
            holdout = holdout.get("holdout_specs") or holdout.get("specs") or []
        for number in holdout:
            path = corpus / f"{number}.tla"
            patch = ROOT / "corpus/configs/patches" / f"{number}.tla"
            paths.append(patch if patch.exists() else path)
    return [path for path in paths if path.is_file()]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--candidate", action="append", type=Path, default=[])
    args = parser.parse_args()
    good = []
    for path in known_good():
        text = path.read_text(errors="replace")
        hits = line_guard(text)
        good.append({"path": str(path), "sha256": digest(text), "hits": hits})
    candidates = []
    for path in args.candidate:
        text = path.read_text()
        candidates.append({"path": str(path), "sha256": digest(text),
                           "hits": line_guard(text)})
    result = {
        "kind": "layout_junction_guard_audit_v1",
        "known_good_requested": len(good),
        "known_good_false_rejects": sum(bool(item["hits"]) for item in good),
        "known_good_false_reject_rate": sum(bool(item["hits"]) for item in good) / max(len(good), 1),
        "known_good": good,
        "candidates": candidates,
        "claims": {"sany_claim": False, "model_improvement_claim": False,
                   "gate_claim": False},
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in result if k not in ("known_good", "candidates")}, sort_keys=True))
    if result["known_good_false_rejects"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
