"""CPU-only failure-family analysis for an explicit-header receipt."""

import argparse
import hashlib
import json
import re
from pathlib import Path

PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
ROWS = (47, 107)
PHASES = ("restored_parent", "trained_child")
FOOTER = re.compile(r"(?m)^=+[ \t]*$")


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def module_header(source, module_name):
    line = source.splitlines(keepends=True)[:1]
    if not line or not re.fullmatch(
            r"-+ MODULE " + re.escape(module_name) + r" -+[ \t]*\r?\n?", line[0]):
        raise ValueError("frozen module header mismatch")
    return line[0]


def raw_body(record):
    parts = record.get("parts")
    if not isinstance(parts, list):
        raise ValueError("parts inventory missing")
    values = []
    for part in parts:
        generation = part.get("generation") or {}
        raw = generation.get("raw_reply", "")
        if sha(raw) != generation.get("raw_reply_sha256"):
            raise ValueError("raw part digest mismatch")
        values.append(raw)
    return "".join(values)


def first_mismatch(left, right):
    limit = min(len(left), len(right))
    for index in range(limit):
        if left[index] != right[index]:
            return index
    return limit if len(left) != len(right) else None


def classify(record, body, sany_status):
    if record.get("stream_reject"):
        if "footer" in record["stream_reject"]:
            return "footer_liveness"
        if "header" in record["stream_reject"]:
            return "header_contract"
        return "stream_contract"
    if "MODULE:" in body or "SEGMENT:" in body:
        return "metadata_leakage"
    if re.search(r"(?m)^-+ MODULE ", body):
        return "duplicate_header"
    if sany_status == "model_sany_reject":
        return "complete_body_sany_reject"
    return "complete_body_other"


def analyze(receipt_path, packet_path, audit_path):
    if file_sha(packet_path) != PACKET_SHA:
        raise ValueError("frozen packet mismatch")
    packet = json.loads(Path(packet_path).read_bytes())
    receipt = json.loads(Path(receipt_path).read_bytes())
    audit = json.loads(Path(audit_path).read_bytes())
    if audit.get("controls_ok") is not True or audit.get("worker_labels_ignored") is not True:
        raise ValueError("complete independent audit required")
    audit_rows = json.loads(Path(audit_path).with_name("rows.json").read_bytes())
    statuses = {(row["phase"], row["row"]): row["status"] for row in audit_rows}
    records = []
    for phase in PHASES:
        for row in ROWS:
            record = receipt["before_protected" if phase == "restored_parent" else "after_protected"][str(row)]
            source = packet["rows"][row]["response"]
            header = module_header(source, record["module_name"])
            body = raw_body(record)
            reference_body = source[len(header):]
            assembled = header + body
            mismatch = first_mismatch(body, reference_body)
            footer_count = len(FOOTER.findall(body))
            values = dict(
                phase=phase, row=row, module_name=record["module_name"],
                status=statuses[(phase, row)],
                failure_family=classify(record, body, statuses[(phase, row)]),
                stream_reject=record.get("stream_reject"),
                finish_reasons=[(part.get("generation") or {}).get("finish_reason")
                                for part in record.get("parts", [])],
                body_char_count=len(body), reference_body_char_count=len(reference_body),
                body_length_delta=len(body) - len(reference_body),
                common_prefix_chars=mismatch if mismatch is not None else len(body),
                first_mismatch_char=mismatch,
                footer_count=footer_count,
                footer_present=footer_count == 1,
                duplicate_header=bool(re.search(r"(?m)^-+ MODULE ", body)),
                metadata_marker=bool("MODULE:" in body or "SEGMENT:" in body),
                markdown_fence="```" in body,
                control_byte="\x00" in body,
                assembled_sha256=sha(assembled),
            )
            records.append(values)
    counts = {}
    for record in records:
        counts[record["failure_family"]] = counts.get(record["failure_family"], 0) + 1
    return dict(
        schema=1,
        kind="fullmodule_explicit_header_failure_family_cpu_audit_v1",
        packet_sha256=file_sha(packet_path),
        receipt_sha256=file_sha(receipt_path),
        independent_audit_sha256=file_sha(audit_path),
        records=records,
        failure_family_counts=counts,
        complete=True,
        model_weights_loaded=False,
        cuda_touched=False,
        optimizer_updates=0,
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = analyze(args.receipt, args.packet, args.audit)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"complete": True, "failure_family_counts": result["failure_family_counts"],
                      "output_sha256": file_sha(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()
