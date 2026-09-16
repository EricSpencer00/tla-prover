"""Bounded CPU-only verifier-guided repair search over saved model bytes.

This is an inference artifact diagnostic.  It never loads model weights, uses
reference text to construct a candidate, or awards model/gate credit.  The
repair vocabulary is fixed in this file and every proposed string is checked
by the pinned local SANY process.  A passing transformed string only identifies
an error family that a future constrained decoder or training objective might
need to learn.
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
REQUIRED_FILES = {
    47: "trained_child-row-47.json",
    107: "trained_child-row-107.json",
}


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def normalize_known_identifier_typos(text):
    """Repair only an identifier spelling when its canonical spelling exists."""
    replacements = (
        ("Dispatchors", "Dispatchers"),
        ("readsnapshots", "readSnapshots"),
    )
    changed = False
    value = text
    for wrong, right in replacements:
        if wrong in value and re.search(rf"\b{re.escape(right)}\b", value):
            value = value.replace(wrong, right)
            changed = True
    return value, changed


def normalize_escaped_identifiers(text):
    """Remove an accidental backslash only from known identifier spellings."""
    names = ("snapshot", "vars", "Lock", "Ledger", "Banks", "Dispatchers",
             "readSnapshots", "active")
    value = text
    for name in names:
        value = value.replace("\\" + name, name)
    return value, value != text


def repair_map_rhs_domain(text):
    """Replace the observed malformed map RHS with a bounded scalar domain."""
    old = r"|-> \in 0..Cap"
    new = r"|-> 0..Cap"
    value = text.replace(old, new)
    return value, value != text


def repair_nested_map_builder(text):
    """Canonicalize the one malformed nested map builder shape."""
    old = r"[d \in Dispatchers |->[d \in Dispatchers |-> \in 0..Cap]]"
    new = r"[d \in Dispatchers |-> [e \in Dispatchers |-> 0..Cap]]"
    value = text.replace(old, new)
    return value, value != text


def repair_trailing_map_bar(text):
    """Give a truncated map-builder bar a finite scalar RHS."""
    value = re.sub(
        r"(?m)^(\s*[^\n]*\[d \\in Dispatchers \|)\s*$",
        r"\1-> 0..Cap",
        text,
    )
    return value, value != text


def drop_post_spec_definitions(text):
    """Remove definitions after Spec while retaining the canonical footer."""
    match = re.search(r"(?ms)^Spec ==.*?\n\n", text)
    if not match:
        return text, False
    footer = re.search(r"(?m)^====\s*$", text)
    if not footer or footer.start() <= match.end():
        return text, False
    value = text[:match.end()] + text[footer.start():]
    return value, value != text


OPERATIONS = (
    ("normalize_known_identifier_typos", normalize_known_identifier_typos),
    ("normalize_escaped_identifiers", normalize_escaped_identifiers),
    ("repair_map_rhs_domain", repair_map_rhs_domain),
    ("repair_nested_map_builder", repair_nested_map_builder),
    ("repair_trailing_map_bar", repair_trailing_map_bar),
    ("drop_post_spec_definitions", drop_post_spec_definitions),
)


def candidate_record(path, row):
    record = json.loads(path.read_bytes())
    if record.get("row") != row or record.get("finish_reason") != "eos":
        raise ValueError(f"row {row} is not a complete saved candidate")
    raw = record.get("raw_reply")
    if not isinstance(raw, str) or sha(raw) != record.get("raw_reply_sha256"):
        raise ValueError(f"row {row} candidate digest mismatch")
    return record


def run(a):
    packet = json.loads(a.packet.read_bytes())
    if preflight.file_sha(a.packet) != preflight.PACKET_SHA:
        raise ValueError("frozen packet mismatch")
    selected = preflight.protected_rows(packet)
    receipt = json.loads(a.receipt.read_bytes())
    if receipt.get("complete") is not True or receipt.get("reload_tensors_exact") is not True:
        raise ValueError("complete exact-reload receipt required")
    records = {row: candidate_record(a.receipt.parent / REQUIRED_FILES[row], row) for row in ROWS}
    java = shutil.which("java")
    jar = ROOT / "tools/tla2tools.jar"
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("pinned SANY runtime unavailable")
    out = a.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    identity = dict(
        schema=1,
        kind="verifier_guided_repair_search_v1",
        receipt_sha256=preflight.file_sha(a.receipt),
        packet_sha256=preflight.file_sha(a.packet),
        jar_sha256=JAR_SHA,
        source_sha256=preflight.file_sha(Path(__file__)),
        scorer_sha256=preflight.file_sha(ROOT / "tools/protected_paired_sany_score.py"),
        classifier_sha256=preflight.file_sha(ROOT / "harness/proof_ladder_check.py"),
        rows=list(ROWS),
        max_depth=2,
        reference_text_used_for_transform=False,
        transformed_strings_diagnostic_only=True,
    )
    dump(out / "identity.json", identity)

    controls = []
    for row in ROWS:
        reference = selected[row][0]["response"]
        if sha(reference) != selected[row][0]["response_sha256"]:
            raise ValueError(f"reference {row} digest mismatch")
        negative = re.sub(r"(?m)^={4,}\s*$", "SyntaxNegativeControl == )\n====", reference)
        for label, value in (("reference", reference), ("negative", negative)):
            result = score(value, out / "controls" / f"{row}-{label}", java, jar)
            controls.append(dict(row=row, label=label, **result))
    dump(out / "controls.json", controls)
    controls_ok = all(c["status"] == ("pass" if c["label"] == "reference" else "model_sany_reject")
                      for c in controls)

    all_results = []
    passes = []
    for row in ROWS:
        raw = records[row]["raw_reply"]
        states = [(raw, [])]
        seen = {sha(raw)}
        for depth in range(1, 3):
            next_states = []
            for value, applied in states:
                for name, operation in OPERATIONS:
                    if name in applied:
                        continue
                    transformed, changed = operation(value)
                    if not changed or sha(transformed) in seen:
                        continue
                    seen.add(sha(transformed))
                    next_states.append((transformed, applied + [name]))
            states.extend(next_states)
        for index, (value, applied) in enumerate(states):
            label = "original" if not applied else "__".join(applied)
            result = score(value, out / "candidates" / str(row) / f"{index:03d}-{label}", java, jar)
            scored_hash = result.pop("candidate_sha256")
            item = dict(row=row, depth=len(applied), operations=applied,
                        original_sha256=sha(raw), candidate_sha256=scored_hash, **result)
            all_results.append(item)
            if result["status"] == "pass":
                passes.append(item)
    dump(out / "rows.json", all_results)
    summary = dict(
        complete=controls_ok and all(r["status"] in ("pass", "model_sany_reject") for r in all_results),
        controls_ok=controls_ok,
        candidate_count=len(all_results),
        pass_count=len(passes),
        passes=passes,
        protected_rows=list(ROWS),
        search_depth=2,
        operation_vocabulary=[name for name, _ in OPERATIONS],
        interpretation=(
            "A passing transformed string is a reference-free SANY diagnostic only; "
            "it is not a model output and earns no protected, quality, gate, proof, "
            "generalization, TLC or promotion credit."
        ),
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(out / "summary.json", summary)
    print(json.dumps(summary, sort_keys=True))
    return summary


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    run(parser.parse_args())
