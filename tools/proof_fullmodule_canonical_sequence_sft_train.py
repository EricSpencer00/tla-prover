"""Bounded SFT diagnostic for canonical byte-sequence proof generation.

The model target is one deterministic length-delimited sequence of complete
TLA+ structural parts.  The worker never trains on protected response text,
never consumes generated verifier feedback, and never repairs or appends a
candidate.  Protected evaluation records only whether the model emitted a
decodable frame; independent pinned-SANY scoring happens outside this worker.
"""

import hashlib
import importlib.util
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_canonical_sequence_probe as sequence
from tools import proof_fullmodule_streaming_sft_train as base


PACKET_SHA = sequence.PACKET_SHA
PARENT_SHA = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
PROBE_SHA = "47467b2c66df004be21c9d1e49037bf5aee3124fc2f3efef74f21846cfd23c2b"
TRAIN = tuple(row for row in range(42, 59) if row != 47)
VALID = sequence.VALIDATION
PROTECTED = sequence.PROTECTED
EXPERIMENT_KIND = "fullmodule_canonical_byte_sequence_sft_v1"
BUDGET = dict(
    steps=48, accumulation=1, lr=2e-6, rank=4, alpha=8, seed=20260917,
    training_seconds=600, max_new_tokens=2048, generation_seconds=20,
    sany_seconds=30, stream_segments=1, adapter_layers=[28, 29, 30, 31],
    adapter_targets=["q_proj", "k_proj", "v_proj", "o_proj",
                     "gate_proj", "up_proj", "down_proj"],
    objective="canonical_byte_sequence_response_only_sft",
)


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _configure():
    base.PACKET_SHA = PACKET_SHA
    base.PARENT_SHA = PARENT_SHA
    base.PROBE_SHA = PROBE_SHA
    base.TRAIN = TRAIN
    base.VALID = VALID
    base.PROTECTED = PROTECTED
    base.EXPERIMENT_KIND = EXPERIMENT_KIND
    base.ALGORITHM = (
        "canonical UTF-8 byte-sequence frame response-only SFT; fresh AdamW")
    base.BUDGET = dict(base.BUDGET, **BUDGET)
    base.load_packet = load_packet
    base.load_probe = load_probe
    base.stream_segments = stream_segments
    base.stream_prompt = stream_prompt
    base.target_for = target_for
    base.prefix_for = prefix_for
    base.manifest_value = manifest_value
    base.source_pins = source_pins
    base.make_eval_tasks = make_eval_tasks
    base.evaluate_protected = evaluate_protected

    from tools import proof_fullmodule_multiexample_probe as multi
    multi.BUDGET.update(
        max_new_tokens=BUDGET["max_new_tokens"],
        item_seconds=BUDGET["generation_seconds"],
        sany_seconds=BUDGET["sany_seconds"], train_only=False,
        eval_rows=list(PROTECTED), gate_claim=False, quality_claim=False,
        generalization_claim=False, proof_claim=False, tlc_claim=False,
        nonvacuity_claim=False)


def load_packet(path):
    packet, rows, _ = sequence.load_packet(path)
    return packet, rows


def load_probe(path):
    if file_sha(path) != PROBE_SHA:
        raise ValueError("exact canonical byte-sequence admission required")
    value = json.loads(Path(path).read_bytes())
    required = {
        "packet_sha256": PACKET_SHA,
        "validation_holdout_contract": True,
        "all_clean_sany_pass": True,
        "all_reconstructions_exact": True,
        "controls_ok": True,
        "model_weights_loaded": False,
        "cuda_touched": False,
        "optimizer_updates": 0,
    }
    if any(value.get(key) != wanted for key, wanted in required.items()):
        raise ValueError("canonical sequence admission guards failed")
    structures = {item["row"]: item for item in value.get("structures", [])}
    if set(structures) != set(sequence.CLEAN_ROWS):
        raise ValueError("complete clean canonical structure inventory required")
    return value, structures


def _frame(response):
    raw, _, _ = sequence.encode_sequence(response)
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("canonical training frame is not UTF-8 decodable") from exc


def stream_segments(response, structure, count=1):
    if int(count) != 1:
        raise ValueError("canonical sequence has exactly one frame target")
    return [_frame(response)]


def stream_prompt(source_prompt, module_name, segment, prefix=""):
    if prefix:
        raise ValueError("canonical sequence target has no raw prefix")
    if int(segment) != 0:
        raise ValueError("canonical sequence has one target segment")
    return source_prompt + (
        "\n\n=== CANONICAL TLA BYTE-SEQUENCE CONTRACT ===\n"
        "Emit exactly one UTF-8 canonical sequence frame. It contains the "
        "complete module as ordered, length-delimited structural parts. "
        "Preserve every payload byte exactly; do not explain, repair, "
        "insert targets, add markdown, or emit bytes after the sequence "
        "terminator. The runtime rejects any frame whose byte lengths, "
        "part order, or SHA-256 digests are not canonical.\n")


def target_for(row, segment, rows, structures):
    if int(segment) != 0:
        raise ValueError("canonical sequence has one target segment")
    return _frame(rows[row]["response"])


def prefix_for(row, segment, rows, structures):
    if int(segment) != 0:
        raise ValueError("canonical sequence prefix must be empty")
    return ""


def manifest_value(rows, structures, probe):
    selected = [TRAIN[index * len(TRAIN) // BUDGET["steps"]]
                for index in range(BUDGET["steps"])]
    entries = []
    for step, row in enumerate(selected, 1):
        target = target_for(row, 0, rows, structures)
        prompt = stream_prompt(rows[row]["prompt"], structures[row]["module_name"], 0)
        entries.append(dict(
            step=step, row=row, segment=0, segment_count=1,
            target_sha256=base.sha(target.encode()),
            target_char_count=len(target), target_byte_count=len(target.encode()),
            prefix_char_count=0, prefix_sha256=base.sha(b""),
            prompt_sha256=base.sha(prompt.encode()),
            frame_sha256=base.sha(target.encode())))
    return dict(
        schema=1, kind=EXPERIMENT_KIND,
        packet_sha256=PACKET_SHA, structure_probe_sha256=PROBE_SHA,
        parent_checkpoint_sha256=PARENT_SHA, train_rows=list(TRAIN),
        validation_rows=list(VALID), protected_rows=list(PROTECTED),
        budget=BUDGET, schedule=entries,
        schedule_sha256=base.sha(json.dumps(entries, separators=(",", ":")).encode()),
        source_sha256=source_pins(), clean_reference_targets_only=True,
        canonical_byte_sequence=True, length_delimited_frame=True,
        target_repair=False, target_injection=False,
        generated_feedback_loaded=False, replay_negatives_loaded=False,
        protected_targets_never_train=True, validation_targets_never_train=True,
        model_weights_loaded=False, cuda_touched=False, optimizer_updates=0,
        training_authorized=True, quality_claim=False, model_improvement_claim=False,
        gate_claim=False, proof_claim=False, generalization_claim=False,
        tlc_claim=False, nonvacuity_claim=False)


def source_pins():
    names = (
        "tools/proof_fullmodule_canonical_sequence_sft_train.py",
        "tools/proof_fullmodule_canonical_sequence_probe.py",
        "tools/proof_fullmodule_streaming_sft_train.py",
        "tools/proof_fullmodule_learning_train.py",
        "tools/proof_cuda_train.py",
    )
    return {name: file_sha(ROOT / name) for name in names}


def make_eval_tasks(packet, rows, output):
    # Protected rows are prompt-only; Independent scoring owns the reference.
    return {}, None


def evaluate_protected(net, tokenizer, rows, output, phase, tasks, sany_identity):
    from tools import proof_fullmodule_multiexample_probe as multi

    results = {}
    for row in PROTECTED:
        prompt = stream_prompt(rows[row]["prompt"], "unknown", 0)
        generated = multi.decode(net, tokenizer, base.prompt_only(tokenizer, prompt))
        item = dict(
            row=row, phase=phase, representation="canonical_byte_sequence_v1",
            generation=generated, protected_reference_conditioning=False,
            protected_target_loaded=False, generated_feedback_loaded=False,
            training=False, supplied_reference_credit=False,
            model_improvement_claim=False, quality_claim=False, gate_claim=False)
        try:
            source, structure, parts = sequence.decode_sequence(
                generated["raw_reply"].encode("utf-8"))
        except (UnicodeError, ValueError) as exc:
            item["canonical_valid"] = False
            item["reject_reason"] = str(exc)
        else:
            item.update(canonical_valid=True,
                        assembled_sha256=base.sha(source.encode()),
                        assembled_byte_count=len(source.encode()),
                        assembled_part_count=len(parts),
                        assembled_module_name=structure["module_name"])
        base.dump(output / f"{phase}-row-{row}.json", item)
        results[str(row)] = item
    return results


def main():
    _configure()
    base.main()


if __name__ == "__main__":
    main()
