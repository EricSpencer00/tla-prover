"""Audit bounded rollback capacity after the v4 decoder closed.

This is a CPU-only policy diagnostic.  It uses only committed receipts and
terminal evidence.  It deliberately does not infer the hidden row-107 token
path, run SANY, or assign model/quality/gate credit.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
WINDOWS = (64, 128, 256)
REPAIR_BUDGET = 512


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bounded_retry_budgets(failed_tokens: int, windows: tuple[int, ...]) -> list[dict]:
    out = []
    for window in windows:
        rollback = max(0, failed_tokens - window)
        if rollback >= failed_tokens:
            continue
        out.append({"window": window, "rollback_tokens": rollback,
                    "remaining_tokens": REPAIR_BUDGET - rollback})
    return out


def synthetic_capacity_controls() -> dict:
    retry_budgets = [item["remaining_tokens"]
                     for item in bounded_retry_budgets(REPAIR_BUDGET, WINDOWS)]
    max_retry = max(retry_budgets)
    # A synthetic branch needing one token more than the largest bounded retry
    # must close.  A branch needing exactly the largest retry must be admitted.
    return {
        "max_retry_tokens": max_retry,
        "exact_capacity": {"required_tokens": max_retry,
                            "status": "terminates" if max_retry >= max_retry else "closed"},
        "over_capacity": {"required_tokens": max_retry + 1,
                          "status": "closed" if max_retry < max_retry + 1 else "terminates"},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--v4-row47", type=Path, required=True)
    parser.add_argument("--v4-terminal", type=Path, required=True)
    parser.add_argument("--v4-log", type=Path, required=True)
    parser.add_argument("--prior-row107", type=Path, required=True)
    args = parser.parse_args()

    row47 = json.loads(args.v4_row47.read_text())
    terminal = json.loads(args.v4_terminal.read_text())
    prior = json.loads(args.prior_row107.read_text())
    if row47.get("row") != 47 or row47.get("repair_tokens") != REPAIR_BUDGET:
        raise ValueError("v4 row47 receipt does not match the bounded budget")
    if terminal.get("job_id") != "7626434.polaris-pbs-01.hsn.cm.polaris.alcf.anl.gov":
        raise ValueError("unexpected v4 terminal job")
    if terminal.get("exit_status") != 1 or terminal.get("failure") != (
            "bounded guard backtracking exhausted without a finite continuation"):
        raise ValueError("v4 terminal evidence is not the expected closed failure")
    if prior.get("row") != 107 or prior.get("repair_tokens") != REPAIR_BUDGET:
        raise ValueError("prior row107 reference diagnostic is not the expected budget")

    retry_budgets = bounded_retry_budgets(REPAIR_BUDGET, WINDOWS)
    result = {
        "kind": "bounded_rollback_policy_audit_v1",
        "inputs": {
            "v4_row47_sha256": sha(args.v4_row47),
            "v4_terminal_sha256": sha(args.v4_terminal),
            "v4_log_sha256": sha(args.v4_log),
            "prior_row107_sha256": sha(args.prior_row107),
        },
        "v4_observation": {
            "row47_complete": True,
            "row107_record_present": False,
            "complete_receipt_present": False,
            "failure_trace_for_row107_present": False,
            "failure": terminal["failure"],
        },
        "policy": {
            "repair_budget": REPAIR_BUDGET,
            "windows": list(WINDOWS),
            "retry_budgets_if_dead_end_after_512": retry_budgets,
            "max_retry_tokens": max(item["remaining_tokens"] for item in retry_budgets),
        },
        "prior_model_shaped_evidence": {
            "source": str(args.prior_row107),
            "repair_tokens": prior["repair_tokens"],
            "grammar_ended": prior["grammar_ended"],
            "interpretation": "A prior independent row107 diagnostic also consumed the full 512-token suffix budget without grammar completion; this is context, not proof of the v4 hidden branch."
        },
        "synthetic_capacity_controls": synthetic_capacity_controls(),
        "conclusion": {
            "measured": "v4 row107 exhausted all bounded rollback attempts and failed closed; its per-attempt token trace was not persisted.",
            "not_inferred": "The hidden row107 continuation length and the exact rollback point are unknown; no SANY or model-quality conclusion follows.",
            "required_before_retry": "Persist each rollback attempt's selected-token count, rollback point, banned token, remaining budget and terminal reason in a partial failure receipt before considering a new stage or GPU run.",
            "replay_v4_unchanged": False,
            "sany_claim": False,
            "model_improvement_claim": False,
            "gate_claim": False,
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({
        "kind": result["kind"],
        "windows": WINDOWS,
        "retry_budgets_if_dead_end_after_512": [item["remaining_tokens"] for item in retry_budgets],
        "row107_trace_present": False,
        "required_before_retry": "persist per-attempt failure trace",
        "claims": result["conclusion"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
