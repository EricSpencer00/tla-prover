"""CPU-only semantic-recoverability probe for a completed protected candidate.

This is deliberately narrower than a TLA+ parser and is not a decoder guard.
It tests one falsifiable hypothesis raised by an actual SANY diagnostic: the
row-47 candidate may be structurally complete but have repeated quantifier
binder names.  The probe makes a mechanically scoped, line-local rename only
for the observed candidate shape, then scores the resulting bytes with the
pinned SANY runtime.  The transformed bytes are diagnostic evidence only;
they cannot earn model, quality, gate, proof, or generalization credit.
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


EXPECTED_ROW = 47
QUANTIFIER = re.compile(r"\\[EA] d \\in Dispatchers")
IDENTIFIER = re.compile(r"(?<![A-Za-z0-9_])d(?![A-Za-z0-9_])")


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def unique_binder_variant(text):
    """Rename only same-line observed quantifier binders.

    The v9 candidate has each binder and every use of that binder on one
    source line.  Refuse any other shape rather than silently applying a
    scope-incorrect textual rewrite.
    """
    lines = text.splitlines(keepends=True)
    changed = 0
    rewritten = []
    for line in lines:
        match = QUANTIFIER.search(line)
        if not match:
            rewritten.append(line)
            continue
        if len(QUANTIFIER.findall(line)) != 1:
            raise ValueError("unsupported multiple-quantifier line")
        name = f"d{changed}"
        updated = IDENTIFIER.sub(name, line)
        if updated == line or name not in updated:
            raise ValueError("binder rewrite did not change source line")
        rewritten.append(updated)
        changed += 1
    if changed != 8:
        raise ValueError(f"expected eight observed binders, found {changed}")
    if QUANTIFIER.search("".join(rewritten)):
        raise ValueError("unrewritten observed binder remains")
    return "".join(rewritten), changed


def score(text, output, java, jar):
    output.mkdir(parents=True, exist_ok=False)
    name = module_name(text)
    candidate = output / f"{name}.tla"
    candidate.write_text(text)
    process = run_owned([java, "-cp", str(jar), "tla2sany.SANY", candidate.name], output, 30)
    status = classify_sany(process["returncode"], process["output"],
                            process["timed_out"], name)
    if not all(process.get(key) for key in
               ("execution_complete", "cleanup_complete", "output_complete")):
        status = "unmeasured_process"
    (output / "sany.log").write_text(process["output"])
    result = dict(status=status, candidate_sha256=sha(text), module_name=name,
                  returncode=process["returncode"],
                  log=str(output / "sany.log"))
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
    if record.get("row") != EXPECTED_ROW:
        raise ValueError("row-47 record required")
    if record.get("grammar_ended") is not True:
        raise ValueError("completed grammar candidate required")
    if record.get("training") is not False or record.get("gate_claim") is not False:
        raise ValueError("record is not a diagnostic-only candidate")
    candidate = record.get("repaired_reply")
    if not isinstance(candidate, str) or sha(candidate) != record.get("repaired_reply_sha256"):
        raise ValueError("candidate digest mismatch")

    packet = json.loads(args.packet.read_bytes())
    selected = preflight.protected_rows(packet)
    reference = selected[EXPECTED_ROW][0]["response"]
    if sha(reference) != selected[EXPECTED_ROW][0]["response_sha256"]:
        raise ValueError("reference digest mismatch")
    variant, binders = unique_binder_variant(candidate)
    if sha(variant) == sha(candidate):
        raise ValueError("semantic variant did not change bytes")

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
        transformed_candidate_is_diagnostic_only=True,
    ))

    controls = [
        dict(label="reference", **score(reference, output / "controls" / "reference", java, jar)),
        dict(label="negative", **score(negative(reference), output / "controls" / "negative", java, jar)),
    ]
    dump(output / "controls.json", controls)
    outcomes = [
        dict(arm="observed_candidate", **score(candidate, output / "candidates" / "observed", java, jar)),
        dict(arm="unique_binder_variant", binder_count=binders,
             **score(variant, output / "candidates" / "unique_binders", java, jar)),
    ]
    dump(output / "rows.json", outcomes)
    controls_ok = (controls[0]["status"] == "pass" and
                   controls[1]["status"] == "model_sany_reject")
    variant_status = outcomes[1]["status"]
    summary = dict(
        complete=controls_ok and variant_status in ("pass", "model_sany_reject"),
        controls_ok=controls_ok,
        observed=2,
        binder_count=binders,
        variant_status=variant_status,
        discriminator=(
            "candidate-level binder repair is SANY-sufficient; pursue verifier-in-loop semantic repair"
            if variant_status == "pass" else
            "binder-only repair is insufficient; pursue broader semantic representation/training probe"
            if variant_status == "model_sany_reject" else
            "semantic discriminator is unmeasured"
        ),
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
