"""Independently SANY-score a full-module training receipt.

The worker's embedded SANY labels are ignored.  This audit reconstructs the
frozen references and replays SANY on the exact saved parent/child bytes, so a
training receipt or improved teacher-forced margins cannot manufacture a
protected result.
"""

import argparse
import hashlib
import json
import re
import shutil
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import protected_checkpoint_preflight as preflight
from tools.protected_paired_sany_score import JAR_SHA, score


ROWS = (47, 107)


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def negative(reference):
    value = re.sub(r"(?m)^={4,}\s*$", "SyntaxNegativeControl == )\n====", reference)
    if value == reference:
        raise ValueError("negative control did not change reference")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    receipt = json.loads(args.receipt.read_bytes())
    if receipt.get("complete") is not True or receipt.get("reload_tensors_exact") is not True:
        raise ValueError("complete exact-reload receipt required")
    if receipt.get("reload_logits_exact") is not True:
        raise ValueError("exact logit reload required")
    packet = json.loads(args.packet.read_bytes())
    if preflight.file_sha(args.packet) != preflight.PACKET_SHA:
        raise ValueError("frozen packet mismatch")
    selected = preflight.protected_rows(packet)
    record_dir = args.receipt.parent
    phases = {
        "restored_parent": receipt.get("before_protected"),
        "trained_child": receipt.get("after_protected"),
    }
    if any(not isinstance(records, list) or [r.get("row") for r in records] != list(ROWS)
           for records in phases.values()):
        raise ValueError("exact ordered protected parent/child records required")
    for phase, records in phases.items():
        stem = "restored_parent" if phase == "restored_parent" else "trained_child"
        for record in records:
            raw_path = record_dir / f"{stem}-row-{record['row']}.json"
            saved = json.loads(raw_path.read_bytes())
            if saved != record:
                raise ValueError(f"receipt/raw record mismatch: {phase}/{record['row']}")
            if sha(record["raw_reply"]) != record.get("raw_reply_sha256"):
                raise ValueError(f"raw reply digest mismatch: {phase}/{record['row']}")

    java = shutil.which("java")
    jar = ROOT / "tools/tla2tools.jar"
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("pinned SANY runtime unavailable")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "identity.json", dict(
        receipt_sha256=preflight.file_sha(args.receipt),
        packet_sha256=preflight.file_sha(args.packet),
        jar_sha256=JAR_SHA,
        scorer_sha256=preflight.file_sha(ROOT / "tools/protected_paired_sany_score.py"),
        source_sha256=preflight.file_sha(__file__),
        classifier_sha256=preflight.file_sha(ROOT / "harness/proof_ladder_check.py"),
        process_runner_sha256=preflight.file_sha(ROOT / "harness/proof_owned_process.py"),
        embedded_worker_labels_ignored=True,
    ))

    controls = []
    for row in ROWS:
        reference = selected[row][0]["response"]
        if sha(reference) != selected[row][0]["response_sha256"]:
            raise ValueError(f"reference digest mismatch: {row}")
        controls.append(dict(row=row, label="reference",
                             **score(reference, output / "controls" / f"{row}-reference", java, jar)))
        controls.append(dict(row=row, label="negative",
                             **score(negative(reference), output / "controls" / f"{row}-negative", java, jar)))
    dump(output / "controls.json", controls)

    rows = []
    for phase, records in phases.items():
        for record in records:
            row = record["row"]
            result = score(record["raw_reply"], output / "candidates" / f"{phase}-{row}", java, jar)
            rows.append(dict(row=row, phase=phase, **result,
                             finish_reason=record.get("finish_reason"),
                             embedded_worker_status=record.get("sany", {}).get("status")))
    dump(output / "rows.json", rows)
    controls_ok = all(c["status"] == ("pass" if c["label"] == "reference" else "model_sany_reject")
                      for c in controls)
    candidate_measured = all(r["status"] in ("pass", "model_sany_reject") for r in rows)
    summary = dict(
        complete=controls_ok and candidate_measured,
        controls_ok=controls_ok,
        protected_rows=list(ROWS),
        requested_candidates=4,
        measured_candidates=len(rows),
        candidate_sany_pass=sum(r["status"] == "pass" for r in rows),
        candidate_sany_reject=sum(r["status"] == "model_sany_reject" for r in rows),
        candidate_statuses={f"{r['phase']}/{r['row']}": r["status"] for r in rows},
        worker_labels_reproduced=False,
        independent_bytes=True,
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(output / "summary.json", summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
