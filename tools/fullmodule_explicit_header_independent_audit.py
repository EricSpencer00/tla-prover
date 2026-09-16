"""Independent audit for explicit-header body-continuation receipts."""

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


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + "\n")


def exact_header(source, module_name):
    line = source.splitlines(keepends=True)[:1]
    if not line or not re.fullmatch(
            r"-+ MODULE " + re.escape(module_name) + r" -+[ \t]*\r?\n?", line[0]):
        raise ValueError(f"frozen canonical header mismatch for {module_name}")
    return line[0]


def verify_record(record, saved, header):
    if saved != record:
        raise ValueError(f"receipt/raw record mismatch for row {record.get('row')}")
    if record.get("runtime_header_sha256") != sha(header):
        raise ValueError(f"runtime header digest mismatch for row {record.get('row')}")
    plan = record.get("plan") or {}
    if sha(plan.get("raw_reply", "")) != plan.get("raw_reply_sha256"):
        raise ValueError(f"plan digest mismatch for row {record.get('row')}")
    parts = record.get("parts")
    if not isinstance(parts, list):
        raise ValueError(f"parts inventory missing for row {record.get('row')}")
    raw_parts = []
    for part in parts:
        generation = part.get("generation") or {}
        raw_reply = generation.get("raw_reply", "")
        if sha(raw_reply) != generation.get("raw_reply_sha256"):
            raise ValueError(f"stream-part digest mismatch for row {record.get('row')}")
        raw_parts.append(raw_reply)

    accepted_prefixes = [header + "".join(raw_parts[:count])
                         for count in range(len(raw_parts) + 1)]
    if record.get("stream_reject"):
        matches = [value for value in accepted_prefixes
                   if record.get("assembled_char_count") == len(value)
                   and record.get("assembled_sha256") == sha(value)]
        if len(matches) != 1:
            raise ValueError(f"rejected-stream prefix mismatch for row {record.get('row')}")
        return ""
    assembled = accepted_prefixes[-1]
    if record.get("assembled_char_count") != len(assembled):
        raise ValueError(f"assembled length mismatch for row {record.get('row')}")
    if record.get("assembled_sha256") != sha(assembled):
        raise ValueError(f"assembled digest mismatch for row {record.get('row')}")
    return assembled


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    receipt = json.loads(args.receipt.read_bytes())
    if any(receipt.get(key) is not True
           for key in ("complete", "reload_tensors_exact", "reload_logits_exact")):
        raise ValueError("complete exact-reload receipt required")
    packet = json.loads(args.packet.read_bytes())
    if preflight.file_sha(args.packet) != preflight.PACKET_SHA:
        raise ValueError("frozen packet mismatch")
    selected = preflight.protected_rows(packet)
    record_dir = args.receipt.parent
    phases = {"restored_parent": receipt.get("before_protected"),
              "trained_child": receipt.get("after_protected")}
    if any(not isinstance(records, dict) or set(records) != {str(row) for row in ROWS}
           for records in phases.values()):
        raise ValueError("exact ordered protected parent/child records required")

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    java = shutil.which("java")
    jar = ROOT / "tools/tla2tools.jar"
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("pinned SANY runtime unavailable")
    dump(output / "identity.json", dict(
        receipt_sha256=file_sha(args.receipt), packet_sha256=file_sha(args.packet),
        jar_sha256=JAR_SHA, scorer_sha256=file_sha(ROOT / "tools/protected_paired_sany_score.py"),
        source_sha256=file_sha(Path(__file__)), runtime_header_from_frozen_packet=True,
        embedded_worker_labels_ignored=True))

    controls = []
    for row in ROWS:
        reference = selected[row][0]["response"]
        if sha(reference) != selected[row][0]["response_sha256"]:
            raise ValueError(f"reference digest mismatch: {row}")
        controls.append(dict(row=row, label="reference",
                             **score(reference, output / "controls" / f"{row}-reference", java, jar)))
        negative = re.sub(r"(?m)^={4,}\s*$", "SyntaxNegativeControl == )\n====", reference)
        if negative == reference:
            raise ValueError("negative control did not change reference")
        controls.append(dict(row=row, label="negative",
                             **score(negative, output / "controls" / f"{row}-negative", java, jar)))

    rows = []
    for phase, records in phases.items():
        stem = phase
        for row in ROWS:
            record = records[str(row)]
            header = exact_header(selected[row][0]["response"], record["module_name"])
            saved = json.loads((record_dir / f"{stem}-row-{row}.json").read_bytes())
            assembled = verify_record(record, saved, header)
            if not assembled:
                rows.append(dict(row=row, phase=phase, status="candidate_unmeasured",
                                 reason=record.get("stream_reject") or "no assembled bytes"))
                continue
            result = score(assembled, output / "candidates" / f"{phase}-{row}", java, jar)
            rows.append(dict(row=row, phase=phase, status=result["status"],
                             independent_result=result))

    dump(output / "controls.json", controls)
    dump(output / "rows.json", rows)
    controls_ok = all(item["status"] == ("pass" if item["label"] == "reference" else "model_sany_reject")
                      for item in controls)
    measured = [item for item in rows if item["status"] != "candidate_unmeasured"]
    summary = dict(
        complete=controls_ok and all(item["status"] in {"pass", "model_sany_reject", "candidate_unmeasured"}
                                     for item in rows),
        controls_ok=controls_ok, protected_rows=list(ROWS), requested_candidates=4,
        measured_candidates=len(measured),
        candidate_unmeasured=sum(item["status"] == "candidate_unmeasured" for item in rows),
        candidate_sany_pass=sum(item["status"] == "pass" for item in measured),
        candidate_sany_reject=sum(item["status"] == "model_sany_reject" for item in measured),
        candidate_statuses={f"{item['phase']}/{item['row']}": item["status"] for item in rows},
        independent_bytes=True, worker_labels_ignored=True,
        model_improvement_claim=False, quality_claim=False, gate_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False, nonvacuity_claim=False)
    dump(output / "summary.json", summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
