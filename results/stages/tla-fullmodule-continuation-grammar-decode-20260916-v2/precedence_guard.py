"""Audit a narrow decoder guard for observed SANY precedence conflicts.

The guard has no SANY or quality credit.  It only rejects two measured forms:
same-line top-level ``\\lor``/``\\land`` mixing after a non-junction definition
RHS, and line-leading quantified disjunctions whose bodies mix conjunctions
with either a primed assignment or two or more direct same-line conjunctions;
the nested ``\\/ /\\`` form is excluded.  Known-good coverage is mandatory
before use.
"""
import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
OR = "\\/"
AND = "/\\"
MODULE = "MODULE"


def module_region(text):
    start = text.find("---- MODULE")
    if start < 0:
        return text
    rest = text[start:]
    end = rest.find("\n====")
    return rest[: end + 5] if end >= 0 else rest


def operator_positions(line):
    """Return top-level operator positions outside simple delimiters/strings."""
    result = []
    depth = 0
    quote = False
    index = 0
    while index < len(line):
        char = line[index]
        if quote:
            if char == '"' and (index == 0 or line[index - 1] != "\\"):
                quote = False
            index += 1
            continue
        if char == '"':
            quote = True
            index += 1
            continue
        if char in "([{":
            depth += 1
            index += 1
            continue
        if char in ")]}":
            depth = max(0, depth - 1)
            index += 1
            continue
        if line.startswith(OR, index):
            result.append((OR, depth, index))
            index += len(OR)
            continue
        if line.startswith(AND, index):
            result.append((AND, depth, index))
            index += len(AND)
            continue
        index += 1
    return result


def precedence_guard(text):
    hits = []
    for line_number, line in enumerate(module_region(text).splitlines(), 1):
        stripped = line.strip()
        operators = operator_positions(stripped)
        top_or = [item for item in operators if item[0] == OR and item[1] == 0]
        top_and = [item for item in operators if item[0] == AND and item[1] == 0]
        if stripped.startswith(OR) and "\\E" in stripped and "'" in stripped and top_and:
            hits.append({"line": line_number, "kind": "quantified_junction_prime"})
            continue
        if (stripped.startswith(OR) and "\\E" in stripped and len(top_and) >= 2
                and not stripped.startswith(OR + " " + AND)):
            hits.append({"line": line_number, "kind": "quantified_junction_direct_many_and"})
            continue
        if "==" in stripped and top_or and top_and:
            rhs = stripped.split("==", 1)[1].lstrip()
            if not (rhs.startswith(OR) or rhs.startswith(AND)):
                hits.append({"line": line_number, "kind": "mixed_definition_rhs"})
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
        good.append({"path": str(path), "sha256": digest(text),
                     "hits": precedence_guard(text)})
    candidates = []
    for path in args.candidate:
        text = path.read_text()
        candidates.append({"path": str(path), "sha256": digest(text),
                           "hits": precedence_guard(text)})
    false_rejects = sum(bool(item["hits"]) for item in good)
    result = {
        "kind": "precedence_guard_audit_v1",
        "known_good_requested": len(good),
        "known_good_false_rejects": false_rejects,
        "known_good_false_reject_rate": false_rejects / max(len(good), 1),
        "known_good": good,
        "candidates": candidates,
        "claims": {"sany_claim": False, "model_improvement_claim": False,
                   "gate_claim": False},
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in result if k not in ("known_good", "candidates")}, sort_keys=True))
    if false_rejects:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
