"""Audit strict, reference-free guards for the two latest decoder failures.

The guards are decoder constraints only.  They do not repair bytes, run
training, or award SANY/model/gate credit.  Admission requires zero false
rejects over the existing 438-module known-good corpus and explicit synthetic
controls for both observed error families.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MAP_IN_SET = re.compile(r"\{\s*[A-Za-z_][A-Za-z0-9_]*\s*\|->")


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def quantified_junction_hits(text):
    lines = text.splitlines()
    hits = []
    for index, line in enumerate(lines[:-1]):
        stripped = line.strip()
        indent = len(line) - len(line.lstrip())
        following = lines[index + 1]
        following_stripped = following.strip()
        following_indent = len(following) - len(following.lstrip())
        if (indent == 2 and stripped.startswith(r"\/ \E") and
                "(" not in stripped and following_indent > indent and
                following_stripped.startswith("/\\")):
            hits.append(dict(line=index + 1, kind="top_level_quantified_junction"))
    return hits


def map_builder_hits(text):
    return [dict(line=index + 1, kind="set_brace_map_arrow")
            for index, line in enumerate(text.splitlines())
            if MAP_IN_SET.search(line)]


def guard(text):
    return quantified_junction_hits(text) + map_builder_hits(text)


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


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candidate", action="append", type=Path, default=[])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    good = []
    for path in known_good():
        text = path.read_text(errors="replace")
        good.append(dict(path=str(path), sha256=sha(text), hits=guard(text)))
    candidates = []
    for path in args.candidate:
        raw = path.read_text()
        try:
            payload = json.loads(raw)
        except json.JSONDecodeError:
            payload = None
        text = payload.get("repaired_reply", raw) if isinstance(payload, dict) else raw
        candidates.append(dict(path=str(path), sha256=sha(text), hits=guard(text)))
    synthetic = {
        "precedence_reject": bool(guard(
            "---- MODULE StrictControl ----\nNext ==\n  \\/ \\E d \\in D : x = y\n    /\\ x' = x\n====")),
        "map_reject": bool(guard(
            "---- MODULE StrictControl ----\nNext == {d |-> x}\n====")),
        "parenthesized_accept": not bool(guard(
            "---- MODULE StrictControl ----\nNext ==\n  \\/ (\\E d \\in D : x = y\n    /\\ x' = x)\n====")),
        "function_map_accept": not bool(guard(
            "---- MODULE StrictControl ----\nNext == [d |-> x]\n====")),
    }
    false_rejects = sum(bool(item["hits"]) for item in good)
    result = dict(
        schema=1,
        kind="continuation_error_family_guard_audit_v1",
        known_good_requested=len(good),
        known_good_false_rejects=false_rejects,
        known_good_false_reject_rate=false_rejects / max(len(good), 1),
        synthetic=synthetic,
        candidates=candidates,
        guard_vocabulary=["top_level_quantified_junction", "set_brace_map_arrow"],
        complete=(len(good) == 438 and false_rejects == 0 and all(synthetic.values())),
        decoder_constraint_only=True,
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(args.output, result)
    print(json.dumps({k: result[k] for k in result if k not in ("known_good", "candidates")}, sort_keys=True))
    if not result["complete"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
