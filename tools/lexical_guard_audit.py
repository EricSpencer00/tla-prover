"""Audit the v9 observed invalid adjacent relational operator guard."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
GUARD_PATH = ROOT / "results/stages/tla-prefix-repair-layout-aware-20260916-v9/lexical_guard.py"
SPEC = importlib.util.spec_from_file_location("v9_lexical_guard", GUARD_PATH)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

from tools.precedence_guard_audit import known_good


def digest(text):
    return hashlib.sha256(text.encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--candidate", action="append", type=Path, default=[])
    args = parser.parse_args()
    good = []
    for path in known_good():
        text = path.read_text(errors="replace")
        good.append({"path": str(path), "sha256": digest(text),
                     "hits": MODULE.lexical_guard(text)})
    candidates = []
    for path in args.candidate:
        text = path.read_text()
        candidates.append({"path": str(path), "sha256": digest(text),
                           "hits": MODULE.lexical_guard(text)})
    false_rejects = sum(bool(item["hits"]) for item in good)
    invalid = "---- MODULE LexicalControl ----\nA == x #< y\n===="
    valid = "---- MODULE LexicalControl ----\nA == x # y\nB == x < y\n===="
    result = {
        "kind": "lexical_guard_audit_v1",
        "known_good_requested": len(good),
        "known_good_false_rejects": false_rejects,
        "known_good_false_reject_rate": false_rejects / max(len(good), 1),
        "synthetic_invalid_rejected": bool(MODULE.lexical_guard(invalid)),
        "synthetic_valid_accepted": not MODULE.lexical_guard(valid),
        "known_good": good,
        "candidates": candidates,
        "claims": {"sany_claim": False, "model_improvement_claim": False,
                   "gate_claim": False},
    }
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in result
                      if k not in ("known_good", "candidates")}, sort_keys=True))
    if false_rejects or not result["synthetic_invalid_rejected"] or not result["synthetic_valid_accepted"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
