"""CPU-only admission for an explicit-header continuation contract.

The v6 stream diagnostic showed that the model did not reliably emit the
canonical first module header.  This probe makes that boundary explicit: the
runtime supplies the exact header, while the model is responsible only for
the body bytes through the unique footer.  It is a contract measurement, not
text repair or target injection; the output deliberately carries no model,
quality, or gate claim.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path


PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
PARENT_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
PROTECTED = (47, 107)
W4_ROWS = tuple(range(42, 169))
HEADER = re.compile(
    r"^(?P<dashes>-+) MODULE (?P<name>[A-Za-z_][A-Za-z0-9_]*) "
    r"-+[ \t]*$"
)
FOOTER = re.compile(r"^=+[ \t]*$")


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def file_sha(path):
    return sha_bytes(Path(path).read_bytes())


def module_header(source):
    """Return the exact first header line and declared module name."""
    first = source.splitlines(keepends=True)[:1]
    if not first:
        raise ValueError("empty module source")
    line = first[0].rstrip("\r\n")
    match = HEADER.fullmatch(line)
    if not match:
        raise ValueError("canonical module header required")
    return first[0], match.group("name")


def split_source(source):
    """Split a complete reference into fixed header and generated body."""
    header, name = module_header(source)
    body = source[len(header):]
    lines = source.splitlines()
    footer_positions = [index for index, line in enumerate(lines)
                        if FOOTER.fullmatch(line)]
    if len(footer_positions) != 1 or footer_positions[0] == 0:
        raise ValueError("complete source must contain one non-leading footer")
    if not body or HEADER.search(body.splitlines()[0] if body.splitlines() else ""):
        raise ValueError("body must not repeat the module header")
    return dict(header=header, body=body, module_name=name,
                header_sha256=sha_bytes(header.encode()),
                body_sha256=sha_bytes(body.encode()),
                source_sha256=sha_bytes(source.encode()),
                header_char_count=len(header), body_char_count=len(body),
                footer_line_index=footer_positions[0])


def validate_fragment(header, body, module_name):
    """Validate only the observable byte contract; never repair a fragment."""
    errors = []
    try:
        parsed_header, parsed_name = module_header(header)
    except ValueError as exc:
        errors.append(str(exc))
    else:
        if parsed_header != header:
            errors.append("header must be exactly one line")
        if parsed_name != module_name:
            errors.append("header module name mismatch")
    if body.startswith("---- MODULE ") or re.match(r"^-+ MODULE ", body):
        errors.append("body repeats canonical module header")
    if "MODULE:" in body or "SEGMENT:" in body:
        errors.append("assistant-facing stream metadata is forbidden")
    if "```" in body or "\x00" in body:
        errors.append("markdown fence or binary byte in body")
    lines = body.splitlines()
    footer_positions = [index for index, line in enumerate(lines)
                        if FOOTER.fullmatch(line)]
    if len(footer_positions) != 1:
        errors.append("body must contain exactly one module footer")
    elif any(line.strip() for line in lines[footer_positions[0] + 1:]):
        errors.append("bytes after module footer")
    return dict(accepted=not errors, errors=errors)


def _row_entry(row, value, split):
    header, body = split["header"], split["body"]
    verdict = validate_fragment(header, body, split["module_name"])
    assembled = header + body
    return dict(
        row=row,
        split=value.get("split"),
        module_name=split["module_name"],
        header_sha256=split["header_sha256"],
        body_sha256=split["body_sha256"],
        source_sha256=split["source_sha256"],
        header_char_count=split["header_char_count"],
        body_char_count=split["body_char_count"],
        assembled_sha256=sha_bytes(assembled.encode()),
        assembly_exact=assembled == value["response"],
        contract=verdict,
    )


def probe(packet_path):
    packet_path = Path(packet_path)
    if file_sha(packet_path) != PACKET_SHA:
        raise ValueError("exact immutable full-module packet required")
    packet = json.loads(packet_path.read_bytes())
    rows = packet.get("rows")
    if not isinstance(rows, list) or len(rows) != 169:
        raise ValueError("complete 169-row packet required")

    entries = []
    for row in W4_ROWS:
        value = rows[row]
        source = value.get("response")
        if not isinstance(source, str):
            raise ValueError(f"row {row} has no response text")
        split = split_source(source)
        entry = _row_entry(row, value, split)
        if not entry["assembly_exact"] or not entry["contract"]["accepted"]:
            raise ValueError(f"exact reference fragment contract failed at row {row}")
        entries.append(entry)

    controls = []
    exact = next(item for item in entries if item["row"] == PROTECTED[0])
    sample = rows[PROTECTED[0]]["response"]
    header, body = module_header(sample)[0], sample[len(module_header(sample)[0]):]
    cases = (
        ("exact", header, body, True),
        ("synthetic_header", "MODULE W4Od2m7p4t2\n", body, False),
        ("repeated_header", header, header + body, False),
        ("metadata_marker", header, "SEGMENT: 0\n" + body, False),
        ("trailing_bytes", header, body + "EXTRA\n", False),
    )
    for label, case_header, case_body, expected in cases:
        verdict = validate_fragment(case_header, case_body, exact["module_name"])
        controls.append(dict(label=label, accepted=verdict["accepted"],
                             expected=expected, verdict=verdict,
                             controls_ok=verdict["accepted"] is expected))
    if not all(item["controls_ok"] for item in controls):
        raise ValueError("fragment contract controls failed")

    protected = [entry for entry in entries if entry["row"] in PROTECTED]
    clean = [entry for entry in entries if entry["row"] not in PROTECTED]
    return dict(
        schema=1,
        kind="fullmodule_explicit_header_fragment_contract_cpu_probe_v1",
        packet_sha256=file_sha(packet_path),
        parent_checkpoint_sha256=PARENT_SHA,
        row_count=len(entries),
        protected_rows=list(PROTECTED),
        clean_rows=len(clean),
        protected_fragment_contracts=protected,
        clean_fragment_contracts=clean,
        exact_assembly_count=sum(item["assembly_exact"] for item in entries),
        exact_assembly_required=len(entries),
        controls=controls,
        header_externalized=True,
        reference_conditioning=False,
        text_repair=False,
        target_injection=False,
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = probe(args.packet)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(admission="pass", rows=result["row_count"],
                          output_sha256=file_sha(args.output)), sort_keys=True))


if __name__ == "__main__":
    main()
