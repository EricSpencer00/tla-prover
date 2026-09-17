"""Independent scorer for a typed-slot protected full-module run.

The worker's labels are untrusted.  This scorer reads only its saved raw
generations, independently parses the typed-slot contract, renders canonical
framing, and calls pinned SANY.  Protected references are controls only; they
never enter training or candidate construction.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_sany_feedback_correction_train as sany
from tools import proof_fullmodule_typed_slot_probe as typed


PACKET_SHA = typed.PACKET_SHA
PARENT_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
CHILD_SHA = "86f2104f302fe45fd96fd983e717031a80115f743753b02f3ce60056ff70e002"
PROTECTED = typed.PROTECTED
PHASES = ("restored_parent", "trained_child")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha(path: str | Path) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def dump(path: str | Path, value: dict) -> None:
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def run(*, packet: Path, job: Path, jar: Path, output: Path) -> dict:
    if sha(packet.read_bytes()) != PACKET_SHA:
        raise ValueError("frozen packet hash mismatch")
    receipt = json.loads((job / "receipt.json").read_bytes())
    if (receipt.get("complete") is not True or receipt.get("updates") != 48 or
            receipt.get("checkpoint_sha256") != CHILD_SHA or
            receipt.get("parent_checkpoint_sha256") != PARENT_SHA or
            receipt.get("generated_feedback_used_for_training") is not False or
            receipt.get("protected_targets_never_train") is not True):
        raise ValueError("worker receipt identity or clean-training guard failed")
    if file_sha(jar) != typed.SANY_JAR_SHA:
        raise ValueError("pinned SANY jar mismatch")
    rows = json.loads(packet.read_bytes())["rows"]
    output.mkdir(parents=True, exist_ok=False)
    reference_records = []
    for row in PROTECTED:
        result = sany.sany_check(
            rows[row]["response"], output / f"checks/reference/{row}", "java", jar)
        reference_records.append(dict(row=row, **result))
    candidate_records = []
    for phase in PHASES:
        for row in PROTECTED:
            item = json.loads((job / f"{phase}-row-{row}.json").read_bytes())
            raw = item.get("generation", {}).get("raw_reply")
            if not isinstance(raw, str):
                raise ValueError(f"missing raw worker reply: {phase}/{row}")
            record = dict(
                phase=phase, row=row, raw_reply_sha256=sha(raw.encode()),
                worker_labels_ignored=True, protected_reference_conditioning=False,
                protected_target_loaded=False, generated_feedback_loaded=False,
                typed_valid=False, candidate_sany_pass=None,
            )
            try:
                parsed = typed.parse_slots(raw)
                rendered = typed.render_slots(dict(schema=1, **parsed))
            except (UnicodeError, ValueError) as exc:
                record["reject_reason"] = str(exc)
            else:
                record.update(typed_valid=True, rendered_sha256=sha(rendered.encode()))
                result = sany.sany_check(
                    rendered, output / f"checks/{phase}/{row}", "java", jar)
                record.update(candidate_sany_pass=result.get("passed"),
                              sany_status=result.get("status"))
            candidate_records.append(record)
    summary = dict(
        schema=1, kind="fullmodule_typed_slot_independent_sany_audit_v1",
        packet_sha256=PACKET_SHA, parent_checkpoint_sha256=PARENT_SHA,
        child_checkpoint_sha256=CHILD_SHA, protected_rows=list(PROTECTED),
        phases=list(PHASES), reference_records=reference_records,
        candidate_records=candidate_records,
        reference_sany_pass=sum(x.get("passed") is True for x in reference_records),
        candidate_count=len(candidate_records),
        typed_candidate_count=sum(x["typed_valid"] for x in candidate_records),
        candidate_sany_pass=sum(x.get("candidate_sany_pass") is True
                                for x in candidate_records),
        worker_labels_ignored=True, generated_feedback_used=False,
        protected_reference_conditioning=False, quality_claim=False,
        model_improvement_claim=False, proof_claim=False, gate_claim=False,
        denominator_fixed=True,
        method="independent typed-slot parse, canonical render and pinned SANY; worker labels ignored",
    )
    dump(output / "summary.json", summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--job", type=Path, required=True)
    parser.add_argument("--jar", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(packet=args.packet, job=args.job, jar=args.jar,
                         output=args.output), indent=2))


if __name__ == "__main__":
    main()
