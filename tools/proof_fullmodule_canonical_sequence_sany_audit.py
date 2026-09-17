"""Independently audit canonical-sequence worker outputs with pinned SANY.

The worker's ``canonical_valid`` fields are deliberately ignored.  This
auditor decodes the saved raw replies itself, runs pinned SANY only on frames
that pass the independent byte contract, and scores protected references as
controls.  It makes no quality, proof, or gate claim.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_canonical_sequence_probe as sequence
from tools import proof_fullmodule_sany_feedback_correction_train as sany


PACKET_SHA = sequence.PACKET_SHA
SANY_JAR_SHA = sequence.SANY_JAR_SHA
ROWS = sequence.PROTECTED
PHASES = ("restored_parent", "trained_child")


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def packet_rows(path):
    raw = Path(path).read_bytes()
    if sha_bytes(raw) != PACKET_SHA:
        raise ValueError("frozen packet mismatch")
    value = json.loads(raw)
    rows = value.get("rows")
    if not isinstance(rows, list) or len(rows) != 169:
        raise ValueError("complete packet required")
    selected = {}
    for row in ROWS:
        item = rows[row]
        response = item.get("response")
        if not isinstance(response, str) or sha_bytes(response.encode()) != item.get("response_sha256"):
            raise ValueError(f"protected reference digest mismatch at row {row}")
        selected[row] = item
    return selected


def candidate_record(run, phase, row):
    path = Path(run) / f"{phase}-row-{row}.json"
    value = json.loads(path.read_bytes())
    generation = value.get("generation")
    if not isinstance(generation, dict) or not isinstance(generation.get("raw_reply"), str):
        raise ValueError(f"raw generation missing at {phase}/{row}")
    raw = generation["raw_reply"]
    if sha_bytes(raw.encode()) != generation.get("raw_reply_sha256"):
        raise ValueError(f"raw generation digest mismatch at {phase}/{row}")
    return value, raw


def audit(packet_path, run, output, jar):
    rows = packet_rows(packet_path)
    if file_sha(jar) != SANY_JAR_SHA:
        raise ValueError("pinned SANY jar mismatch")
    receipt = json.loads((Path(run) / "receipt.json").read_bytes())
    if receipt.get("complete") is not True or receipt.get("updates") != 48:
        raise ValueError("complete 48-update receipt required")
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    references = []
    for row in ROWS:
        result = sany.sany_check(
            rows[row]["response"], output / f"reference/{row}", "java", jar,
            timeout=30)
        references.append(dict(row=row, status=result["status"], passed=result.get("passed")))
    candidates = []
    for phase in PHASES:
        for row in ROWS:
            worker_record, raw = candidate_record(run, phase, row)
            item = dict(row=row, phase=phase, raw_reply_sha256=sha_bytes(raw.encode()),
                        worker_label_ignored=worker_record.get("canonical_valid"),
                        worker_claims_ignored=True)
            try:
                source, structure, parts = sequence.decode_sequence(raw.encode())
            except (UnicodeError, ValueError) as exc:
                item.update(status="frame_reject", passed=False, diagnostic=str(exc),
                            canonical_valid=False, sany=None)
            else:
                result = sany.sany_check(
                    source, output / f"candidate/{phase}/{row}", "java", jar,
                    timeout=30)
                item.update(status=result["status"], passed=result.get("passed"),
                            diagnostic=result.get("diagnostic"), canonical_valid=True,
                            assembled_sha256=sha_bytes(source.encode()),
                            module_name=structure["module_name"], part_count=len(parts),
                            sany=result)
            candidates.append(item)
    summary = dict(
        schema=1,
        kind="fullmodule_canonical_byte_sequence_independent_sany_audit_v1",
        packet_sha256=PACKET_SHA,
        run_receipt_sha256=file_sha(Path(run) / "receipt.json"),
        jar_sha256=SANY_JAR_SHA,
        protected_rows=list(ROWS),
        references=references,
        candidates=candidates,
        reference_sany_pass=sum(item["passed"] is True for item in references),
        candidate_count=len(candidates),
        canonical_candidate_count=sum(item.get("canonical_valid") is True for item in candidates),
        candidate_sany_pass=sum(item.get("passed") is True for item in candidates),
        worker_labels_ignored=True,
        protected_reference_conditioning_for_training=False,
        generated_feedback_loaded=False,
        target_repair=False,
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(output / "summary.json", summary)
    print(json.dumps({key: summary[key] for key in
                      ("reference_sany_pass", "candidate_count",
                       "canonical_candidate_count", "candidate_sany_pass",
                       "worker_labels_ignored")}, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--jar", type=Path, default=ROOT / "tools/tla2tools.jar")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    audit(args.packet, args.run, args.output, args.jar)


if __name__ == "__main__":
    main()
