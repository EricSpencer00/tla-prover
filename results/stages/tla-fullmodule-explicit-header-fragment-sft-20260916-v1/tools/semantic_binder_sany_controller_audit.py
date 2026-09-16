"""CPU-only SANY-in-the-loop audit for a bounded semantic repair frontier.

This is a controller discriminator, not a model or acceptance run.  It takes
one completed diagnostic row-47 candidate, proposes only the mechanically
scoped binder repairs already justified by its SANY error shape, and measures
the cumulative frontier with the pinned SANY runtime.  The controller is
allowed to select a candidate only when SANY passes it; transformed bytes are
diagnostic evidence and never receive model, quality, or gate credit.

Row 107 is deliberately not inferred from row 47 and remains unmeasured when
no complete candidate exists.  This preserves the protected denominator.
"""

import argparse
import hashlib
import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from harness.proof_ladder_check import classify_sany
from harness.proof_owned_process import run_owned
from tools import protected_checkpoint_preflight as preflight
from tools.protected_paired_sany_score import JAR_SHA, module_name


ROW = 47
MODULE_BINDER = re.compile(r"\\[EA] d \\in Dispatchers")
IDENTIFIER = re.compile(r"(?<![A-Za-z0-9_])d(?![A-Za-z0-9_])")


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def rename_prefix(text, changed_count):
    """Rename the first N observed same-line binders, refusing other shapes."""
    lines = text.splitlines(keepends=True)
    locations = [
        index for index, line in enumerate(lines)
        if MODULE_BINDER.search(line)
    ]
    if len(locations) != 8:
        raise ValueError(f"expected eight observed binders, found {len(locations)}")
    if not 0 <= changed_count <= len(locations):
        raise ValueError("invalid cumulative repair count")
    for ordinal, index in enumerate(locations[:changed_count]):
        line = lines[index]
        updated = IDENTIFIER.sub(f"d{ordinal}", line)
        if updated == line or f"d{ordinal}" not in updated:
            raise ValueError("scoped binder rename did not change its line")
        lines[index] = updated
    return "".join(lines)


def score(text, output, java, jar):
    output.mkdir(parents=True, exist_ok=False)
    name = module_name(text)
    candidate = output / f"{name}.tla"
    candidate.write_text(text)
    process = run_owned(
        [java, "-cp", str(jar), "tla2sany.SANY", candidate.name], output, 30
    )
    status = classify_sany(
        process["returncode"], process["output"], process["timed_out"], name
    )
    if not all(process.get(key) for key in
               ("execution_complete", "cleanup_complete", "output_complete")):
        status = "unmeasured_process"
    (output / "sany.log").write_text(process["output"])
    result = dict(
        status=status,
        passed=status == "pass",
        candidate_sha256=sha(text),
        module_name=name,
        returncode=process["returncode"],
        log=str(output / "sany.log"),
    )
    dump(output / "process.json", process)
    dump(output / "result.json", result)
    return result


def negative(reference):
    value = re.sub(r"(?m)^={4,}\s*$", "SyntaxNegativeControl == )\n====", reference)
    if value == reference:
        raise ValueError("negative control injection failed")
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    record = json.loads(args.record.read_bytes())
    if record.get("row") != ROW or record.get("grammar_ended") is not True:
        raise ValueError("a completed row-47 diagnostic candidate is required")
    if record.get("training") is not False or record.get("gate_claim") is not False:
        raise ValueError("record must be inference-only and diagnostic-only")
    candidate = record.get("repaired_reply")
    if not isinstance(candidate, str) or sha(candidate) != record.get("repaired_reply_sha256"):
        raise ValueError("candidate digest mismatch")

    packet = json.loads(args.packet.read_bytes())
    selected = preflight.protected_rows(packet)
    reference = selected[ROW][0]["response"]
    if sha(reference) != selected[ROW][0]["response_sha256"]:
        raise ValueError("reference digest mismatch")

    java = shutil.which("java")
    jar = ROOT / "tools/tla2tools.jar"
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError("pinned SANY runtime unavailable")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / "identity.json", dict(
        record_sha256=preflight.file_sha(args.record),
        packet_sha256=preflight.file_sha(args.packet),
        jar_sha256=JAR_SHA,
        source_sha256=preflight.file_sha(__file__),
        classifier_sha256=preflight.file_sha(ROOT / "harness/proof_ladder_check.py"),
        process_runner_sha256=preflight.file_sha(ROOT / "harness/proof_owned_process.py"),
        java=java,
        scope="row47 cumulative same-line binder repair frontier",
        transformed_candidate_is_diagnostic_only=True,
    ))

    controls = [
        dict(label="reference", **score(reference, output / "controls" / "reference", java, jar)),
        dict(label="negative", **score(negative(reference), output / "controls" / "negative", java, jar)),
    ]
    observed = score(candidate, output / "candidates" / "observed", java, jar)
    frontier = []
    for count in range(1, 9):
        frontier.append(dict(
            changed_binders=count,
            **score(rename_prefix(candidate, count),
                   output / "frontier" / f"binders-{count}", java, jar),
        ))

    passing = [row["changed_binders"] for row in frontier if row["status"] == "pass"]
    first_passing = min(passing) if passing else None
    monotonic = (
        first_passing is not None and
        all(row["status"] == "model_sany_reject"
            for row in frontier[:first_passing - 1]) and
        all(row["status"] == "pass"
            for row in frontier[first_passing - 1:])
    )
    controls_ok = (
        controls[0]["status"] == "pass" and
        controls[1]["status"] == "model_sany_reject" and
        observed["status"] == "model_sany_reject"
    )
    summary = dict(
        complete=controls_ok and monotonic,
        controls_ok=controls_ok,
        protected_rows=[47, 107],
        measured_rows=[47],
        unmeasured_rows=[107],
        binder_count=8,
        first_sany_passing_repair=first_passing,
        cumulative_frontier_monotonic=monotonic,
        rejected_before_first_pass=all(
            row["status"] == "model_sany_reject"
            for row in frontier[:(first_passing or 1) - 1]
        ),
        all_repairs_at_or_after_first_pass=all(
            row["status"] == "pass"
            for row in frontier[(first_passing or 9) - 1:]
        ) if first_passing is not None else False,
        controller_policy=(
            "select only the first SANY-passing scoped repair; reject all earlier frontier states"
            if monotonic else
            "do not select a semantic repair controller from this frontier"
        ),
        controls=controls,
        observed=observed,
        frontier=frontier,
        transformed_candidate_is_diagnostic_only=True,
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
