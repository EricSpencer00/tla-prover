"""CPU admission for a canonical byte-sequence proof-body representation.

This probe evaluates a representation that is deliberately different from
raw full-module continuation and from the previous fixed stream fragments.
The model-facing target is a deterministic, length-delimited sequence of
complete structural parts.  The decoder accepts no repair, target insertion,
reference lookup, or verifier feedback: it validates the byte lengths and
digests, reassembles the module, and only then calls pinned SANY.

Protected response bodies are never read.  The result is an admission
artifact only; it makes no model, quality, proof, or gate claim.
"""

import argparse
import base64
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
MAGIC = b"@TLA_SEQUENCE_V1\n"
END_PART = b"\n@END_PART\n"
END_SEQUENCE = b"@END_SEQUENCE\n"
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_.-]*$")


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


def load_packet(path):
    raw = Path(path).read_bytes()
    if sha_bytes(raw) != PACKET_SHA:
        raise ValueError("exact immutable full-module packet required")
    packet = json.loads(raw)
    rows = packet.get("rows")
    encodings = packet.get("encodings")
    if not isinstance(rows, list) or not isinstance(encodings, list):
        raise ValueError("complete packet rows and encodings required")
    if len(rows) != 169 or len(encodings) != 169:
        raise ValueError("complete 169-row packet required")
    for row in CLEAN_ROWS:
        value, encoding = rows[row], encodings[row]
        if (value.get("split") != "train" or
                encoding.get("id") != value.get("id") or
                sha_bytes(value.get("prompt", "").encode()) != value.get("prompt_sha256") or
                sha_bytes(value.get("response", "").encode()) != value.get("response_sha256") or
                value.get("source_sha256") != value.get("response_sha256") or
                encoding.get("prompt_sha256") != value.get("prompt_sha256") or
                encoding.get("response_sha256") != value.get("response_sha256")):
            raise ValueError(f"clean row {row} immutable identity mismatch")
    protected_metadata = []
    for row in PROTECTED:
        value = rows[row]
        if (value.get("split") != "train" or
                not value.get("id", "").startswith("w4-fullmodule:") or
                not re.fullmatch(r"[0-9a-f]{64}", value.get("response_sha256", ""))):
            raise ValueError(f"protected row {row} metadata mismatch")
        protected_metadata.append(dict(
            row=row, id=value["id"], prompt_sha256=value["prompt_sha256"],
            response_sha256=value["response_sha256"],
            source_sha256=value["source_sha256"]))
    return packet, rows, protected_metadata


def _byte_starts(text):
    starts = []
    offset = 0
    for line in text.splitlines(keepends=True):
        starts.append(offset)
        offset += len(line.encode())
    return starts


def _parts(text):
    structure = structure_probe.decompose(text)
    starts = _byte_starts(text)
    lines = text.splitlines(keepends=True)
    line_starts = []
    offset = 0
    for line in lines:
        line_starts.append(offset)
        offset += len(line.encode())
    result = []
    for index, part in enumerate(structure["parts"]):
        value = text[part["start_char"]:part["end_char"]]
        raw = value.encode()
        start_byte = len(text[:part["start_char"]].encode())
        result.append(dict(
            ordinal=index,
            kind=part["kind"],
            name=part.get("operator_name") or part["id"],
            start_byte=start_byte,
            byte_count=len(raw),
            sha256=sha_bytes(raw),
            text=value,
        ))
    if b"".join(item["text"].encode() for item in result) != text.encode():
        raise AssertionError("structural parts are not byte-lossless")
    if result[0]["start_byte"] != 0 or any(
            left["start_byte"] + left["byte_count"] != right["start_byte"]
            for left, right in zip(result, result[1:])):
        raise AssertionError("structural parts have a byte gap or overlap")
    return structure, result


def encode_sequence(text):
    """Encode exact source bytes as a canonical, length-delimited sequence."""
    structure, parts = _parts(text)
    output = bytearray(MAGIC)
    for item in parts:
        if not NAME_RE.fullmatch(item["name"]):
            raise ValueError("unsafe structural part name")
        header = "@PART\t{ordinal}\t{kind}\t{name}\t{start}\t{count}\t{sha}\n".format(
            ordinal=item["ordinal"], kind=item["kind"], name=item["name"],
            start=item["start_byte"], count=item["byte_count"], sha=item["sha256"])
        output.extend(header.encode("ascii"))
        output.extend(item["text"].encode())
        output.extend(END_PART)
    output.extend(END_SEQUENCE)
    return bytes(output), structure, parts


def _readline(raw, offset):
    end = raw.find(b"\n", offset)
    if end < 0:
        raise ValueError("unterminated sequence control line")
    return raw[offset:end].decode("ascii"), end + 1


def decode_sequence(raw):
    """Decode and validate a frame without repairing any byte."""
    if not isinstance(raw, bytes) or not raw.startswith(MAGIC):
        raise ValueError("canonical sequence magic required")
    offset = len(MAGIC)
    parts = []
    expected_start = 0
    while True:
        line, offset = _readline(raw, offset)
        if line == "@END_SEQUENCE":
            if offset != len(raw):
                raise ValueError("bytes after sequence terminator")
            break
        fields = line.split("\t")
        if len(fields) != 7 or fields[0] != "@PART":
            raise ValueError("canonical part header required")
        _, ordinal, kind, name, start, count, digest = fields
        try:
            ordinal, start, count = int(ordinal), int(start), int(count)
        except ValueError as exc:
            raise ValueError("numeric part fields required") from exc
        if (ordinal != len(parts) or start != expected_start or count < 0 or
                kind not in {"header", "declarations", "operator", "footer"} or
                not NAME_RE.fullmatch(name) or not re.fullmatch(r"[0-9a-f]{64}", digest)):
            raise ValueError("part identity or order mismatch")
        end = offset + count
        if end > len(raw):
            raise ValueError("part exceeds sequence bytes")
        payload = raw[offset:end]
        offset = end
        if not raw.startswith(END_PART, offset):
            raise ValueError("part byte count does not reach exact terminator")
        offset += len(END_PART)
        if sha_bytes(payload) != digest:
            raise ValueError("part digest mismatch")
        payload.decode("utf-8")
        parts.append(dict(ordinal=ordinal, kind=kind, name=name,
                          start_byte=start, byte_count=count, sha256=digest,
                          payload=payload))
        expected_start += count
    if not parts or parts[0]["kind"] != "header" or parts[-1]["kind"] != "footer":
        raise ValueError("complete header-to-footer sequence required")
    source_bytes = b"".join(item["payload"] for item in parts)
    source = source_bytes.decode("utf-8")
    structure, expected = _parts(source)
    if len(expected) != len(parts):
        raise ValueError("decoded part count differs from source structure")
    for actual, wanted in zip(parts, expected):
        if any(actual[key] != wanted[key] for key in
               ("ordinal", "kind", "name", "start_byte", "byte_count", "sha256")):
            raise ValueError("decoded part metadata is not canonical")
    return source, structure, parts


def _mutate(raw, label):
    value = bytearray(raw)
    if label == "wrong_length":
        line_end = value.find(b"\n", len(MAGIC))
        fields = value[len(MAGIC):line_end].split(b"\t")
        if len(fields) != 7:
            raise AssertionError("part header fields missing")
        fields[5] = str(int(fields[5]) + 1).encode()
        replacement = b"\t".join(fields)
        value[len(MAGIC):line_end] = replacement
    elif label == "wrong_digest":
        position = value.find(b"\t" + b"0" * 64)
        if position >= 0:
            value[position + 1] = ord("1")
        else:
            line_end = value.find(b"\n", len(MAGIC))
            digest_start = value.find(b"\t", line_end - 1) + 1
            value[digest_start] = ord("0") if value[digest_start] != ord("0") else ord("1")
    elif label == "trailing":
        value.extend(b"x")
    elif label == "reordered":
        first = value.find(b"@PART\t")
        second = value.find(b"@PART\t", first + 1)
        if first < 0 or second < 0:
            raise AssertionError("two parts required")
        line_end = value.find(b"\n", first)
        value[first + 6] = ord("1")
        value[second + 6] = ord("0")
    else:
        raise ValueError(label)
    return bytes(value)


def transport_controls(reference_frame):
    cases = [("exact", reference_frame, True)]
    for label in ("wrong_length", "wrong_digest", "reordered", "trailing"):
        cases.append((label, _mutate(reference_frame, label), False))
    result = []
    for label, raw, expected in cases:
        try:
            decode_sequence(raw)
        except (ValueError, UnicodeDecodeError) as exc:
            accepted, reason = False, str(exc)
        else:
            accepted, reason = True, None
        result.append(dict(label=label, accepted=accepted, expected=expected,
                           controls_ok=accepted is expected, reason=reason))
    return result


def run(args):
    packet, rows, protected_metadata = load_packet(args.packet)
    if file_sha(args.jar) != SANY_JAR_SHA:
        raise ValueError("pinned SANY jar mismatch")
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=False)
    structures = []
    sany_controls = []
    validation_records = []
    for row in CLEAN_ROWS:
        source = rows[row]["response"]
        frame, structure, parts = encode_sequence(source)
        reconstructed, decoded_structure, decoded_parts = decode_sequence(frame)
        if reconstructed != source:
            raise ValueError(f"canonical sequence reconstruction failed at row {row}")
        record = dict(
            row=row, id=rows[row]["id"], module_name=structure["module_name"],
            part_count=len(parts), full_byte_count=len(source.encode()),
            frame_byte_count=len(frame), source_sha256=sha_bytes(source.encode()),
            frame_sha256=sha_bytes(frame), reconstructed_sha256=sha_bytes(reconstructed.encode()),
            reconstruction_exact=True,
            part_kinds=[part["kind"] for part in parts],
            parts=[{key: item[key] for key in
                    ("ordinal", "kind", "name", "start_byte", "byte_count", "sha256")}
                   for item in parts],
        )
        structures.append(record)
        result = sany.sany_check(source, output / f"sany/{row}", args.java, args.jar)
        if result.get("passed") is not True:
            raise ValueError(f"clean reference SANY control failed at row {row}: {result}")
        sany_controls.append(dict(row=row, status=result["status"], passed=True,
                                  result_sha256=file_sha(output / f"sany/{row}/result.json")))
        if row in VALIDATION:
            validation_records.append(dict(row=row, source_sha256=record["source_sha256"],
                                           frame_sha256=record["frame_sha256"], sany=result))

    control_results = transport_controls(encode_sequence(rows[VALIDATION[0]]["response"])[0])
    if not all(item["controls_ok"] for item in control_results):
        raise ValueError("canonical sequence negative controls failed")
    if len(validation_records) != len(VALIDATION) or not all(
            item["sany"].get("passed") is True for item in validation_records):
        raise ValueError("validation holdout contract failed")

    result = dict(
        schema=1,
        kind="fullmodule_canonical_byte_sequence_cpu_admission_v1",
        packet_sha256=PACKET_SHA,
        sany_jar_sha256=SANY_JAR_SHA,
        source_sha256=file_sha(Path(__file__)),
        clean_rows=list(CLEAN_ROWS),
        validation_rows=list(VALIDATION),
        protected_rows=list(PROTECTED),
        protected_holdout_metadata=protected_metadata,
        reference_count=len(structures),
        structures=structures,
        sany_controls=sany_controls,
        validation_holdout=validation_records,
        controls=control_results,
        controls_ok=True,
        all_reconstructions_exact=True,
        all_clean_sany_pass=True,
        validation_holdout_contract=True,
        byte_exact=True,
        length_delimited=True,
        target_repair=False,
        target_injection=False,
        reference_conditioning=False,
        generated_feedback_loaded=False,
        replay_negatives_loaded=False,
        model_weights_loaded=False,
        cuda_touched=False,
        optimizer_updates=0,
        training_authorized=False,
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(output / "admission.json", result)
    print(json.dumps(dict(admission="pass", clean_rows=len(structures),
                          validation_rows=len(validation_records),
                          output_sha256=file_sha(output / "admission.json")), sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--jar", type=Path, default=ROOT / "tools/tla2tools.jar")
    parser.add_argument("--java", default="java")
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args())


if __name__ == "__main__":
    main()
