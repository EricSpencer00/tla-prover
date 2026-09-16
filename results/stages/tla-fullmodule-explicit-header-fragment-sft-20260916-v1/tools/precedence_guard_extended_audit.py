"""Audit the v7 precedence guard against the frozen known-good denominator."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
STAGE_GUARD = ROOT / "results/stages/tla-prefix-repair-layout-aware-20260916-v7/precedence_guard.py"
spec = importlib.util.spec_from_file_location("v7_precedence_guard", STAGE_GUARD)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
from tools.precedence_guard_audit import known_good, digest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--candidate", action="append", type=Path, default=[])
    args = parser.parse_args()
    good = [{"path": str(path), "sha256": digest(path.read_text(errors="replace")),
             "hits": module.precedence_guard(path.read_text(errors="replace"))}
            for path in known_good()]
    candidates = [{"path": str(path), "sha256": digest(path.read_text()),
                  "hits": module.precedence_guard(path.read_text())}
                 for path in args.candidate]
    false_rejects = sum(bool(item["hits"]) for item in good)
    result = {
        "kind": "precedence_guard_extended_audit_v1",
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
