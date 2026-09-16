"""Independently SANY-score the completed row from a partial v7 run.

Row 107 is intentionally not scored: v7 produced only a failure receipt for
that row.  This tool reports row-47 evidence without expanding it into a
two-row protected result or a gate claim.
"""
import argparse
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_ladder_check import classify_sany
from tools import protected_checkpoint_preflight as preflight
from tools.protected_checkpoint_paired_generation import sha
from tools.protected_paired_sany_score import JAR_SHA, module_name
from tools.score_layout_aware_v6_receipt import negative, score


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--failure", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    record = json.loads(args.record.read_bytes())
    failure = json.loads(args.failure.read_bytes())
    selected = preflight.protected_rows(json.loads(args.packet.read_bytes()))[47]
    item, encoding = selected
    reference = item["response"]
    if (record.get("row") != 47 or record.get("prompt_tokens") != encoding["prompt_tokens"] or
            record.get("prompt_tokens_match_frozen") is not True or
            sha(record["baseline_reply"]) != record["baseline_reply_sha256"] or
            sha(record["repaired_reply"]) != record["repaired_reply_sha256"] or
            record.get("protected_reference_conditioning") is not False or
            record.get("training") is not False or record.get("gate_claim") is not False or
            record.get("model_improvement_claim") is not False):
        raise ValueError("row-47 identity or contract mismatch")
    if (failure.get("row") != 107 or failure.get("complete") is not False or
            not isinstance(failure.get("backtrack_attempts"), list)):
        raise ValueError("row-107 failure receipt is not a valid partial receipt")
    java = shutil.which("java")
    jar = ROOT / "tools/tla2tools.jar"
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("pinned SANY runtime unavailable")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "identity.json", {
        "record_sha256": preflight.file_sha(args.record),
        "failure_sha256": preflight.file_sha(args.failure),
        "packet_sha256": preflight.PACKET_SHA,
        "jar_sha256": JAR_SHA,
        "scorer_sha256": preflight.file_sha(__file__),
        "source_scorer_sha256": preflight.file_sha(ROOT / "tools/score_layout_aware_v6_receipt.py"),
        "classifier_sha256": preflight.file_sha(ROOT / "harness/proof_ladder_check.py"),
        "process_runner_sha256": preflight.file_sha(ROOT / "harness/proof_owned_process.py"),
        "java": java,
        "row107_scored": False,
    })
    controls = []
    for label, text in (("reference", reference), ("negative", negative(reference))):
        controls.append(dict(row=47, label=label,
                             **score(text, output / "controls" / f"47-{label}", java, jar)))
    dump(output / "controls.json", controls)
    controls_ok = all(c["status"] == ("pass" if c["label"] == "reference"
                                      else "model_sany_reject") for c in controls)
    outcomes = []
    for arm, field in (("baseline", "baseline_reply"),
                       ("layout_aware_repair", "repaired_reply")):
        outcomes.append(dict(row=47, arm=arm,
                             **score(record[field], output / "candidates" / f"47-{arm}",
                                     java, jar)))
    dump(output / "rows.json", outcomes)
    row47_complete = controls_ok and all(
        item["status"] in ("pass", "model_sany_reject") for item in outcomes)
    summary = {
        "complete": False,
        "row47_raw_sany_audit_complete": row47_complete,
        "row107_scored": False,
        "protected_sany_denominator": {"passed": 0, "requested": 2, "complete": False},
        "controls_ok": controls_ok,
        "observed": len(outcomes),
        "counts": {arm: item["status"] for arm, item in
                   ((x["arm"], x) for x in outcomes)},
        "scope": "row 47 only from a partial two-row diagnostic",
        "input_transform": "none; baseline and repaired bytes scored verbatim",
        "gate_claim": False,
        "model_improvement_claim": False,
    }
    dump(output / "summary.json", summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
