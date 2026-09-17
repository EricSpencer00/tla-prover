"""Bounded SFT diagnostic for typed declaration/operator slot generation.

This module specializes the existing checked training loop to a different
target contract: the model emits a typed declaration/operator record stream;
the runtime validates it and owns canonical module framing before independent
SANY scoring.  No protected response, verifier feedback, repair, or replay
negative enters training.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_streaming_sft_train as base
from tools import proof_fullmodule_typed_slot_probe as typed


PACKET_SHA = typed.PACKET_SHA
PARENT_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
PROBE_SHA = "d9716570080f92c2faf8afb0ca6210201e4a53c92696aa867410060c0245d880"
TRAIN = typed.TRAIN_ROWS
VALID = typed.VALIDATION
PROTECTED = typed.PROTECTED
MODULE_NAMES = {47: "W4Od2m7p4t2", 107: "W4Od3m0p0t0"}
EXPERIMENT_KIND = "fullmodule_typed_slot_sft_v1"
ALGORITHM = "typed declaration/operator slot response-only SFT; fresh AdamW"
BUDGET = dict(
    steps=48, accumulation=1, lr=2e-6, rank=4, alpha=8, seed=20260917,
    training_seconds=600, max_new_tokens=2048, generation_seconds=20,
    sany_seconds=30, stream_segments=1, adapter_layers=[28, 29, 30, 31],
    adapter_targets=["q_proj", "k_proj", "v_proj", "o_proj",
                     "gate_proj", "up_proj", "down_proj"],
    objective="typed_declaration_operator_slot_response_sft",
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def file_sha(path: str | Path) -> str:
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def source_pins():
    names = (
        "tools/proof_fullmodule_typed_slot_sft_train.py",
        "tools/proof_fullmodule_typed_slot_probe.py",
        "tools/proof_fullmodule_streaming_sft_train.py",
        "tools/proof_fullmodule_multiexample_probe.py",
        "tools/proof_fullmodule_sany_feedback_correction_train.py",
        "tools/proof_fullmodule_learning_train.py",
        "tools/proof_cuda_train.py",
    )
    return {name: file_sha(ROOT / name) for name in names}


def load_packet(path):
    packet, rows, protected = typed.load_packet(path)
    return packet, rows


def load_probe(path):
    if file_sha(path) != PROBE_SHA:
        raise ValueError("exact typed-slot CPU admission required")
    value = json.loads(Path(path).read_bytes())
    required = {
        "packet_sha256": PACKET_SHA,
        "representation_admitted": True,
        "all_rendered_sany_pass": True,
        "all_transport_controls_ok": True,
        "model_weights_loaded": False,
        "cuda_touched": False,
        "optimizer_updates": 0,
    }
    if any(value.get(key) != wanted for key, wanted in required.items()):
        raise ValueError("typed-slot CPU admission guards failed")
    structures = {}
    for item in value.get("records", []):
        if item["row"] in PROTECTED:
            raise ValueError("protected typed-slot record present")
        # The generic loop uses only a nonempty parts list to build a schedule;
        # target/prefix construction below is independent of this placeholder.
        structures[item["row"]] = dict(
            module_name=item["module_name"],
            parts=[dict(id="typed-slot-stream", kind="typed-slot")],
        )
    if set(structures) != set(typed.CLEAN_ROWS):
        raise ValueError("complete clean typed-slot inventory required")
    return value, structures


def stream_segments(response, structure, count=1):
    if int(count) != 1:
        raise ValueError("typed-slot contract has one record stream")
    return [typed.encode_slots(response)["text"]]


def stream_prompt(source_prompt, module_name, segment, prefix=""):
    if int(segment) != 0 or prefix:
        raise ValueError("typed-slot generation has no continuation prefix")
    return source_prompt + (
        "\n\n=== TYPED TLA SLOT CONTRACT ===\n"
        f"MODULE: {module_name}\n"
        "Emit exactly one typed slot stream. Emit the declaration slot first, "
        "then each top-level operator slot in order, with no markdown or "
        "explanation. The runtime owns the canonical module header and footer; "
        "it rejects unknown slots, reordered slots, missing boundaries, and "
        "trailing text. Do not repair or insert target text.\n")


def target_for(row, segment, rows, structures):
    if int(segment) != 0:
        raise ValueError("typed-slot stream has one segment")
    return typed.encode_slots(rows[row]["response"])["text"]


def prefix_for(row, segment, rows, structures):
    if int(segment) != 0:
        raise ValueError("typed-slot prefix must be empty")
    return ""


def schedule(structures):
    selected = [TRAIN[index * len(TRAIN) // BUDGET["steps"]]
                for index in range(BUDGET["steps"])]
    return [dict(step=step, row=row, segment=0, segment_count=1)
            for step, row in enumerate(selected, 1)]


def manifest_value(rows, structures, probe):
    entries = schedule(structures)
    for entry in entries:
        target = target_for(entry["row"], 0, rows, structures)
        prompt = stream_prompt(rows[entry["row"]]["prompt"],
                               structures[entry["row"]]["module_name"], 0)
        entry.update(target_sha256=sha(target.encode()),
                     target_char_count=len(target), prefix_char_count=0,
                     prefix_sha256=sha(b""), prompt_sha256=sha(prompt.encode()))
    return dict(
        schema=1, kind=EXPERIMENT_KIND, packet_sha256=PACKET_SHA,
        structure_probe_sha256=PROBE_SHA, parent_checkpoint_sha256=PARENT_SHA,
        train_rows=list(TRAIN), validation_rows=list(VALID),
        protected_rows=list(PROTECTED), budget=BUDGET, schedule=entries,
        schedule_sha256=sha(json.dumps(entries, separators=(",", ":")).encode()),
        source_sha256=source_pins(), clean_reference_targets_only=True,
        typed_slot_schema=True, renderer_owned_framing=True,
        generated_feedback_loaded=False, replay_negatives_loaded=False,
        protected_targets_never_train=True, validation_targets_never_train=True,
        model_weights_loaded=False, cuda_touched=False, optimizer_updates=0,
        training_authorized=True, quality_claim=False, model_improvement_claim=False,
        gate_claim=False, proof_claim=False, generalization_claim=False,
        tlc_claim=False, nonvacuity_claim=False,
    )


def make_eval_tasks(packet, rows, output):
    from tools import proof_fullmodule_multiexample_probe as multi
    tasks = {row: multi.stage_task(
        multi.checker_task(packet, rows[row]), output, f"reference/{row}")
        for row in PROTECTED}
    return tasks, multi.sany.identity(list(tasks.values()))


def evaluate_protected(net, tokenizer, rows, output, phase, tasks, sany_identity):
    from tools import proof_fullmodule_multiexample_probe as multi
    results = {}
    for row in PROTECTED:
        module = MODULE_NAMES[row]
        prompt = stream_prompt(rows[row]["prompt"], module, 0)
        generated = multi.decode(net, tokenizer, base.prompt_only(tokenizer, prompt))
        item = dict(row=row, phase=phase, module_name=module,
                    representation="typed_declaration_operator_slot_v1",
                    generation=generated, protected_reference_conditioning=False,
                    protected_target_loaded=False, generated_feedback_loaded=False,
                    training=False, supplied_reference_credit=False,
                    model_improvement_claim=False, quality_claim=False,
                    gate_claim=False)
        try:
            parsed = typed.parse_slots(generated["raw_reply"])
            rendered = typed.render_slots(dict(schema=1, **parsed))
        except (UnicodeError, ValueError) as exc:
            item.update(typed_valid=False, reject_reason=str(exc))
        else:
            item.update(typed_valid=True, rendered=rendered,
                        rendered_sha256=sha(rendered.encode()),
                        rendered_byte_count=len(rendered.encode()))
            item["sany"] = multi.sany.check(
                tasks[row], rendered, output / f"sany_candidate/{phase}/{row}",
                sany_identity, timeout=BUDGET["sany_seconds"])
        base.dump(output / f"{phase}-row-{row}.json", item)
        results[str(row)] = item
    return results


def configure():
    base.PACKET_SHA = PACKET_SHA
    base.PARENT_SHA = PARENT_SHA
    base.PROBE_SHA = PROBE_SHA
    base.TRAIN = TRAIN
    base.VALID = VALID
    base.PROTECTED = PROTECTED
    base.MODULE_NAMES = MODULE_NAMES
    base.EXPERIMENT_KIND = EXPERIMENT_KIND
    base.ALGORITHM = ALGORITHM
    base.BUDGET = dict(base.BUDGET, **BUDGET)
    base.load_packet = load_packet
    base.load_probe = load_probe
    base.stream_segments = stream_segments
    base.stream_prompt = stream_prompt
    base.target_for = target_for
    base.prefix_for = prefix_for
    base.schedule = schedule
    base.manifest_value = manifest_value
    base.source_pins = source_pins
    base.make_eval_tasks = make_eval_tasks
    base.evaluate_protected = evaluate_protected


def main():
    configure()
    base.main()


if __name__ == "__main__":
    main()
