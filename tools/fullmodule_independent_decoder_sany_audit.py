"""Independently score verifier-constrained decoder outputs with pinned SANY."""

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
    if receipt.get("complete") is not True or receipt.get("kind") != "fullmodule_continuation_grammar_decode_v1":
        raise ValueError("complete decoder receipt required")
    if receipt.get("rows") != list(ROWS) or receipt.get("training") is not False:
        raise ValueError("decoder receipt contract drift")
    packet = json.loads(args.packet.read_bytes())
    if preflight.file_sha(args.packet) != preflight.PACKET_SHA:
        raise ValueError("frozen packet mismatch")
    selected = preflight.protected_rows(packet)
    record_dir = args.receipt.parent
    records = {record["row"]: record for record in receipt.get("records", [])}
    if list(records) != list(ROWS):
        raise ValueError("exact ordered decoder rows required")
    for row in ROWS:
        saved = json.loads((record_dir / f"row-{row}.json").read_bytes())
        if saved != records[row]:
            raise ValueError(f"row {row} receipt/raw mismatch")
        if sha(saved["baseline_reply"]) != saved["baseline_reply_sha256"]:
            raise ValueError(f"row {row} baseline digest mismatch")
        if sha(saved["repaired_reply"]) != saved["repaired_reply_sha256"]:
            raise ValueError(f"row {row} repaired digest mismatch")
    java = shutil.which("java")
    jar = ROOT / "tools/tla2tools.jar"
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("pinned SANY runtime unavailable")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "identity.json", dict(
        schema=1,
        kind="fullmodule_independent_decoder_sany_audit_v1",
        receipt_sha256=preflight.file_sha(args.receipt),
        packet_sha256=preflight.file_sha(args.packet),
        jar_sha256=JAR_SHA,
        source_sha256=preflight.file_sha(Path(__file__)),
        scorer_sha256=preflight.file_sha(ROOT / "tools/protected_paired_sany_score.py"),
        classifier_sha256=preflight.file_sha(ROOT / "harness/proof_ladder_check.py"),
        embedded_decoder_labels_ignored=True,
    ))
    controls = []
    for row in ROWS:
        reference = selected[row][0]["response"]
        if sha(reference) != selected[row][0]["response_sha256"]:
            raise ValueError(f"reference {row} digest mismatch")
        controls.append(dict(row=row, label="reference",
                             **score(reference, output / "controls" / f"{row}-reference", java, jar)))
        controls.append(dict(row=row, label="negative",
                             **score(negative(reference), output / "controls" / f"{row}-negative", java, jar)))
    dump(output / "controls.json", controls)
    rows = []
    for row in ROWS:
        record = records[row]
        for phase, field in (("baseline", "baseline_reply"), ("repaired", "repaired_reply")):
            result = score(record[field], output / "candidates" / f"{phase}-{row}", java, jar)
            rows.append(dict(row=row, phase=phase, grammar_ended=(record["grammar_ended"] if phase == "repaired" else None), **result))
    dump(output / "rows.json", rows)
    controls_ok = all(c["status"] == ("pass" if c["label"] == "reference" else "model_sany_reject")
                      for c in controls)
    measured = all(r["status"] in ("pass", "model_sany_reject") for r in rows)
    repaired = [r for r in rows if r["phase"] == "repaired"]
    summary = dict(
        complete=controls_ok and measured,
        controls_ok=controls_ok,
        protected_rows=list(ROWS),
        requested_candidates=4,
        measured_candidates=len(rows),
        repaired_sany_pass=sum(r["status"] == "pass" for r in repaired),
        repaired_sany_reject=sum(r["status"] == "model_sany_reject" for r in repaired),
        statuses={f"{r['phase']}/{r['row']}": r["status"] for r in rows},
        grammar_ended={str(r): records[r]["grammar_ended"] for r in ROWS},
        independent_bytes=True,
        embedded_decoder_labels_ignored=True,
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
