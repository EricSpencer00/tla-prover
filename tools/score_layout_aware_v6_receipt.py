"""Audit a v6 layout-aware receipt and score its bytes verbatim with SANY.

The receipt-kind check is intentionally strict.  A kind mismatch is recorded
as an implementation metadata defect while the frozen controls and candidate
bytes are still scored independently.  Nothing in this tool grants gate or
model-improvement credit.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_ladder_check import classify_sany
from harness.proof_owned_process import run_owned
from tools import protected_checkpoint_preflight as preflight
from tools.protected_checkpoint_paired_generation import sha
from tools.protected_paired_sany_score import JAR_SHA, module_name

ROWS = (47, 107)
EXPECTED_KIND = "protected_layout_aware_repair_v6"
EXPECTED_CORPUS_SHA = "fb76468f6a3217a359d54da92a2e3fa25396aad0547e6b5eb35129193a0e812a"
EXPECTED_GRAMMAR_SHA = "2bcc86946f0a858628f455a3d0648c7117e2b780743e1f25dff82cebd0fb4d67"
EXPECTED_CHILD_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
REQUIRED_TRACE_FIELDS = [
    "attempt", "status", "rollback_tokens", "banned_token",
    "remaining_tokens", "selected_tokens", "failure_steps",
]


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def score(text, output, java, jar):
    output.mkdir(parents=True, exist_ok=False)
    try:
        name = module_name(text)
    except ValueError:
        name = "candidate"
    candidate = output / f"{name}.tla"
    candidate.write_bytes(text.encode())
    process = run_owned([java, "-cp", str(jar), "tla2sany.SANY", candidate.name], output, 30)
    status = classify_sany(process["returncode"], process["output"],
                            process["timed_out"], name)
    if not all(process.get(k) for k in ("execution_complete", "cleanup_complete",
                                        "output_complete")):
        status = "unmeasured_process"
    (output / "sany.log").write_text(process["output"])
    result = dict(status=status, candidate_sha256=sha(text), module_name=name,
                  returncode=process["returncode"], log=str(output / "sany.log"))
    dump(output / "result.json", result)
    return result


def negative(reference):
    value = re.sub(r"(?m)^={4,}\s*$", "SyntaxNegativeControl == )\n====", reference)
    if value == reference:
        raise ValueError("negative control injection failed")
    return value


def validate(receipt, records, selected):
    contract = receipt.get("contract", {})
    expected = {
        "rows": list(ROWS), "max_new_tokens": 2048,
        "repair_max_new_tokens": 512, "selector_audit_steps": 4,
        "backtrack_windows": [64, 128, 256, 512],
        "failure_trace_fields": REQUIRED_TRACE_FIELDS,
        "prefix_preserving": True, "reference_conditioning": False,
        "training": False, "supplied_reference_credit": False,
    }
    mismatches = [key for key, value in expected.items()
                  if contract.get(key) != value]
    if receipt.get("complete") is not True:
        mismatches.append("complete")
    for key, value in (("packet_sha256", preflight.PACKET_SHA),
                       ("corpus_sha256", EXPECTED_CORPUS_SHA),
                       ("grammar_sha256", EXPECTED_GRAMMAR_SHA),
                       ("child_checkpoint_sha256", EXPECTED_CHILD_SHA)):
        if receipt.get(key) != value:
            mismatches.append(key)
    if [r.get("row") for r in receipt.get("records", [])] != list(ROWS):
        mismatches.append("receipt_record_order")
    if sorted(records) != list(ROWS):
        mismatches.append("record_set")
    for row in ROWS:
        record = records[row]
        if record != next(r for r in receipt["records"] if r["row"] == row):
            mismatches.append(f"row_{row}_receipt_identity")
        _, encoding = selected[row]
        if (record["prompt_tokens"] != encoding["prompt_tokens"] or
                record["prompt_tokens_match_frozen"] is not True or
                sha(record["baseline_reply"]) != record["baseline_reply_sha256"] or
                sha(record["repaired_reply"]) != record["repaired_reply_sha256"] or
                record["protected_reference_conditioning"] is not False or
                record["training"] is not False or
                record["gate_claim"] is not False or
                record["model_improvement_claim"] is not False):
            mismatches.append(f"row_{row}_identity_or_contract")
    return {
        "receipt_kind_expected": EXPECTED_KIND,
        "receipt_kind_observed": receipt.get("kind"),
        "receipt_kind_match": receipt.get("kind") == EXPECTED_KIND,
        "receipt_contract_mismatches": mismatches,
        "structural_receipt_valid_except_kind": not mismatches,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--records", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = json.loads(args.receipt.read_bytes())
    selected = preflight.protected_rows(json.loads(args.packet.read_bytes()))
    records = {int(p.stem.split("-")[1]): json.loads(p.read_bytes())
               for p in args.records.glob("row-*.json")}
    admission = validate(receipt, records, selected)
    if admission["receipt_contract_mismatches"]:
        raise ValueError(json.dumps(admission, sort_keys=True))
    java = shutil.which("java")
    jar = ROOT / "tools/tla2tools.jar"
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("pinned SANY runtime unavailable")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "identity.json", {
        **admission,
        "receipt_sha256": preflight.file_sha(args.receipt),
        "record_sha256": {str(row): preflight.file_sha(args.records / f"row-{row}.json")
                          for row in ROWS},
        "packet_sha256": preflight.PACKET_SHA,
        "jar_sha256": JAR_SHA,
        "scorer_sha256": preflight.file_sha(__file__),
        "classifier_sha256": preflight.file_sha(ROOT / "harness/proof_ladder_check.py"),
        "process_runner_sha256": preflight.file_sha(ROOT / "harness/proof_owned_process.py"),
        "java": java,
    })
    controls = []
    for row in ROWS:
        reference = selected[row][0]["response"]
        if sha(reference) != selected[row][0]["response_sha256"]:
            raise ValueError(f"reference control digest mismatch row {row}")
        for label, text in (("reference", reference), ("negative", negative(reference))):
            controls.append(dict(row=row, label=label,
                                 **score(text, output / "controls" / f"{row}-{label}", java, jar)))
    dump(output / "controls.json", controls)
    controls_ok = all(c["status"] == ("pass" if c["label"] == "reference"
                                      else "model_sany_reject") for c in controls)
    outcomes = []
    for row in ROWS:
        for arm, field in (("baseline", "baseline_reply"),
                           ("layout_aware_repair", "repaired_reply")):
            outcomes.append(dict(row=row, arm=arm,
                                 **score(records[row][field],
                                        output / "candidates" / f"{row}-{arm}",
                                        java, jar)))
    dump(output / "rows.json", outcomes)
    raw_sany_complete = controls_ok and all(
        r["status"] in ("pass", "model_sany_reject") for r in outcomes)
    summary = {
        "complete": raw_sany_complete and admission["receipt_kind_match"],
        "raw_sany_audit_complete": raw_sany_complete,
        "controls_ok": controls_ok,
        "requested": 4,
        "observed": len(outcomes),
        "counts": {arm: dict(Counter(r["status"] for r in outcomes if r["arm"] == arm))
                   for arm in ("baseline", "layout_aware_repair")},
        "input_transform": "none; baseline and repaired bytes scored verbatim",
        "scope": "two protected rows; diagnostic only",
        "receipt_kind_mismatch_preserved": not admission["receipt_kind_match"],
        "gate_claim": False,
        "model_improvement_claim": False,
    }
    dump(output / "summary.json", summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
