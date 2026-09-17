"""CPU admission for a typed-slot full-module representation.

The model-facing target is a small typed record stream: the module name,
one declaration slot, and the ordered top-level operator slots.  The runtime
owns the canonical module header and footer, validates slot identity and
order, renders the slots without repair or target insertion, and only then
calls pinned SANY.  This is intentionally different from a raw byte frame,
the prior arbitrary stream fragments, and the structure-first planner.

Protected response bodies are never read.  Only non-protected reference
bodies are read; protected rows contribute metadata and remain an independent
holdout for any later worker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_structure_first_probe as structure_probe
from tools import proof_fullmodule_sany_feedback_correction_train as sany


PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
SANY_JAR_SHA = "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88"
W4_ROWS = tuple(range(42, 169))
PROTECTED = (47, 107)
VALIDATION = (59, 60, 61, 62, 63, 64)
CLEAN_ROWS = tuple(row for row in W4_ROWS if row not in PROTECTED)
TRAIN_ROWS = tuple(row for row in CLEAN_ROWS if row not in VALIDATION)

MAGIC = "@TLA_TYPED_SLOT_V1\n"
END = "@TLA_TYPED_END\n"
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
MODULE_RE = re.compile(r"^-+ MODULE ([A-Za-z][A-Za-z0-9_]*) -+$")


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


def _parts(text: str) -> tuple[dict, list[dict]]:
    structure = structure_probe.decompose(text)
    parts = structure["parts"]
    header = text[parts[0]["start_char"]:parts[0]["end_char"]]
    match = MODULE_RE.fullmatch(header.rstrip("\r\n"))
    if not match:
        raise ValueError("canonical module header required")
    slots = []
    for part in parts[1:-1]:
        payload = text[part["start_char"]:part["end_char"]]
        if part["kind"] == "declarations":
            slots.append(dict(kind="declarations", name="-", payload=payload))
        elif part["kind"] == "operator":
            name = part.get("operator_name")
            if not name or not NAME_RE.fullmatch(name):
                raise ValueError("unsafe operator name")
            slots.append(dict(kind="operator", name=name, payload=payload))
        else:
            raise ValueError("unexpected structural part")
    if not slots or slots[0]["kind"] != "declarations":
        raise ValueError("declaration slot must be first")
    return dict(module_name=match.group(1), structure=structure, header=header), slots


def encode_slots(text: str) -> dict:
    """Create a canonical typed slot stream from a complete module."""
    metadata, slots = _parts(text)
    lines = [MAGIC.rstrip("\n"), f"MODULE\t{metadata['module_name']}"]
    for index, slot in enumerate(slots):
        lines.append(f"SLOT\t{index}\t{slot['kind']}\t{slot['name']}")
        lines.extend(slot["payload"].splitlines())
        # splitlines() deliberately omits the final newline; the slot marker
        # is the sole boundary and the payload newline is restored by parser.
        lines.append("END_SLOT")
    lines.append(END.rstrip("\n"))
    return dict(
        schema=1,
        module_name=metadata["module_name"],
        slots=[dict(kind=s["kind"], name=s["name"], payload=s["payload"],
                    payload_sha256=sha(s["payload"].encode())) for s in slots],
        text="\n".join(lines) + "\n",
    )


def _read_slot_payload(lines: list[str], offset: int) -> tuple[str, int]:
    payload = []
    while offset < len(lines) and lines[offset] != "END_SLOT":
        payload.append(lines[offset])
        offset += 1
    if offset >= len(lines):
        raise ValueError("unterminated typed slot")
    # Every original slot is line based, including its final newline.  An
    # empty declaration slot is valid; nonempty slots must retain line ends.
    return ("\n".join(payload) + ("\n" if payload else "")), offset + 1


def parse_slots(text: str) -> dict:
    """Parse a slot stream and reject malformed identity/order without repair."""
    if not isinstance(text, str) or not text.startswith(MAGIC):
        raise ValueError("typed-slot magic required")
    lines = text.splitlines()
    if len(lines) < 4 or lines[0] != MAGIC.rstrip("\n"):
        raise ValueError("typed-slot envelope required")
    if not lines[-1] == END.rstrip("\n"):
        raise ValueError("typed-slot end marker must be final")
    module_fields = lines[1].split("\t")
    if (len(module_fields) != 2 or module_fields[0] != "MODULE" or
            not NAME_RE.fullmatch(module_fields[1])):
        raise ValueError("module record malformed")
    module_name = module_fields[1]
    slots = []
    offset = 2
    while offset < len(lines) - 1:
        fields = lines[offset].split("\t")
        if len(fields) != 4 or fields[0] != "SLOT":
            raise ValueError("slot header malformed")
        try:
            ordinal = int(fields[1])
        except ValueError as exc:
            raise ValueError("slot ordinal malformed") from exc
        kind, name = fields[2], fields[3]
        if (ordinal != len(slots) or kind not in {"declarations", "operator"} or
                (kind == "declarations" and name != "-") or
                (kind == "operator" and not NAME_RE.fullmatch(name))):
            raise ValueError("slot identity or order malformed")
        offset += 1
        payload, offset = _read_slot_payload(lines, offset)
        slots.append(dict(ordinal=ordinal, kind=kind, name=name, payload=payload,
                          payload_sha256=sha(payload.encode())))
    if not slots or slots[0]["kind"] != "declarations":
        raise ValueError("declarations must be the first slot")
    if not any(slot["kind"] == "operator" for slot in slots):
        raise ValueError("at least one operator slot required")
    if len({slot["name"] for slot in slots[1:]}) != len(slots) - 1:
        raise ValueError("operator names must be unique")
    return dict(schema=1, module_name=module_name, slots=slots)


def render_slots(parsed: dict) -> str:
    """Render canonical framing around validated model-emitted slots."""
    if not isinstance(parsed, dict) or parsed.get("schema") != 1:
        raise ValueError("unsupported typed-slot schema")
    name = parsed.get("module_name")
    if not isinstance(name, str) or not NAME_RE.fullmatch(name):
        raise ValueError("unsafe module name")
    slots = parsed.get("slots")
    if not isinstance(slots, list) or not slots or slots[0].get("kind") != "declarations":
        raise ValueError("typed slots missing declarations")
    if any(slot.get("ordinal") != index for index, slot in enumerate(slots)):
        raise ValueError("typed slot ordinals are not contiguous")
    if any(not isinstance(slot.get("payload"), str) for slot in slots):
        raise ValueError("typed slot payload must be text")
    body = "".join(slot["payload"] for slot in slots)
    if not body.endswith("\n"):
        raise ValueError("typed slot body must end at a line boundary")
    return f"---- MODULE {name} ----\n" + body + "====\n"


def _mutate(text: str, label: str) -> str:
    lines = text.splitlines()
    if label == "wrong_ordinal":
        fields = lines[2].split("\t")
        fields[1] = "7"
        lines[2] = "\t".join(fields)
    elif label == "reordered":
        first = next(i for i, line in enumerate(lines) if line.startswith("SLOT\t"))
        second = next(i for i, line in enumerate(lines[first + 1:], first + 1)
                      if line.startswith("SLOT\t"))
        fields = lines[first].split("\t")
        fields[1] = "1"
        lines[first] = "\t".join(fields)
        fields = lines[second].split("\t")
        fields[1] = "0"
        lines[second] = "\t".join(fields)
    elif label == "unknown_kind":
        fields = lines[2].split("\t")
        fields[2] = "answer"
        lines[2] = "\t".join(fields)
    elif label == "trailing":
        lines.append("not permitted")
    else:
        raise ValueError(label)
    return "\n".join(lines) + "\n"


def transport_controls(stream: str) -> list[dict]:
    result = [("exact", stream, True)]
    result.extend((label, _mutate(stream, label), False)
                  for label in ("wrong_ordinal", "reordered", "unknown_kind", "trailing"))
    records = []
    for label, value, expected in result:
        try:
            parse_slots(value)
        except (ValueError, UnicodeError) as exc:
            accepted, reason = False, str(exc)
        else:
            accepted, reason = True, None
        records.append(dict(label=label, accepted=accepted, expected=expected,
                            controls_ok=accepted is expected, reason=reason))
    return records


def load_packet(path: str | Path):
    raw = Path(path).read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError("exact immutable full-module packet required")
    packet = json.loads(raw)
    rows, encodings = packet.get("rows"), packet.get("encodings")
    if not isinstance(rows, list) or not isinstance(encodings, list) or len(rows) != 169:
        raise ValueError("complete 169-row packet required")
    for row in CLEAN_ROWS:
        value, encoding = rows[row], encodings[row]
        if (value.get("split") != "train" or encoding.get("id") != value.get("id") or
                sha(value.get("prompt", "").encode()) != value.get("prompt_sha256") or
                sha(value.get("response", "").encode()) != value.get("response_sha256") or
                value.get("source_sha256") != value.get("response_sha256") or
                encoding.get("prompt_sha256") != value.get("prompt_sha256") or
                encoding.get("response_sha256") != value.get("response_sha256")):
            raise ValueError(f"clean row {row} immutable identity mismatch")
    protected = []
    for row in PROTECTED:
        value = rows[row]
        if (value.get("split") != "train" or
                not value.get("id", "").startswith("w4-fullmodule:") or
                not re.fullmatch(r"[0-9a-f]{64}", value.get("response_sha256", ""))):
            raise ValueError(f"protected row {row} metadata mismatch")
        protected.append(dict(row=row, id=value["id"],
                              prompt_sha256=value["prompt_sha256"],
                              response_sha256=value["response_sha256"],
                              source_sha256=value["source_sha256"]))
    return packet, rows, protected


def run(args) -> dict:
    packet, rows, protected_metadata = load_packet(args.packet)
    if file_sha(args.jar) != SANY_JAR_SHA:
        raise ValueError("pinned SANY jar mismatch")
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=False)
    records, controls = [], []
    for row in CLEAN_ROWS:
        source = rows[row]["response"]
        encoded = encode_slots(source)
        parsed = parse_slots(encoded["text"])
        rendered = render_slots(parsed)
        if not rendered.endswith("====\n"):
            raise AssertionError("canonical footer missing")
        result = sany.sany_check(rendered, output / f"controls/{row}", args.java, args.jar)
        if result.get("passed") is not True:
            raise ValueError(f"rendered typed reference failed SANY at row {row}: {result}")
        records.append(dict(
            row=row, id=rows[row]["id"], split="validation" if row in VALIDATION else "train",
            module_name=encoded["module_name"], slot_count=len(encoded["slots"]),
            source_sha256=sha(source.encode()), typed_stream_sha256=sha(encoded["text"].encode()),
            rendered_sha256=sha(rendered.encode()), rendered_differs_from_source=rendered != source,
            rendered_byte_count=len(rendered.encode()), source_byte_count=len(source.encode()),
            slot_kinds=[slot["kind"] for slot in encoded["slots"]],
            slot_names=[slot["name"] for slot in encoded["slots"]],
            sany_pass=True,
        ))
        if row == CLEAN_ROWS[0]:
            controls = transport_controls(encoded["text"])
    result = dict(
        schema=1, kind="fullmodule_typed_slot_cpu_admission_v1",
        packet_sha256=PACKET_SHA, sany_jar_sha256=SANY_JAR_SHA,
        train_rows=list(TRAIN_ROWS), validation_rows=list(VALIDATION),
        protected_rows=list(PROTECTED), reference_rows=list(CLEAN_ROWS),
        protected_holdout_metadata=protected_metadata, records=records,
        transport_controls=controls,
        all_rendered_sany_pass=bool(records) and all(item["sany_pass"] for item in records),
        all_transport_controls_ok=bool(controls) and all(item["controls_ok"] for item in controls),
        all_clean_slots_typed=all(item["slot_count"] >= 2 for item in records),
        model_weights_loaded=False, cuda_touched=False, optimizer_updates=0,
        protected_response_text_used=False, protected_targets_never_train=True,
        validation_targets_never_train=True, generated_feedback_loaded=False,
        replay_negatives_loaded=False, target_repair=False, target_injection=False,
        quality_claim=False, model_improvement_claim=False, proof_claim=False,
        gate_claim=False, tlc_claim=False, nonvacuity_claim=False,
        training_authorized=False, gpu_request_authorized=False,
        method=("typed declaration/operator slots with renderer-owned canonical "
                "header/footer; independent pinned SANY after reconstruction"),
    )
    result["representation_admitted"] = bool(
        result["all_rendered_sany_pass"] and result["all_transport_controls_ok"] and
        result["all_clean_slots_typed"])
    dump(output / "typed-slot-preflight.json", result)
    print(json.dumps(dict(
        preflight="pass" if result["representation_admitted"] else "reject",
        references=len(CLEAN_ROWS), train=len(TRAIN_ROWS), validation=len(VALIDATION),
        sany_passes=sum(item["sany_pass"] for item in records),
        transport_controls=len(controls),
        output_sha256=file_sha(output / "typed-slot-preflight.json")), indent=2))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--java", required=True)
    parser.add_argument("--jar", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    run(args)


if __name__ == "__main__":
    main()
