"""Build a CPU-only sequence preference packet from frozen TRAIN20 rollouts."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_syntax_preference_train as checker
from tools import protected_sequence_objective_contract as contract

RUN = ROOT / "results/runs/proof-fullmodule-train-probe-eval-20260906-v1"
ACCOUNTING = RUN / "accounting.json"
ADMISSION = RUN / "admission.json"
TARGETS = ROOT / "results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json"
JAR = ROOT / "tools/tla2tools.jar"
PINS = {
    "accounting": "2da1cb237f0a9e47c4220b12237c67988f76991d22ce15234ed72c422e3cb5a4",
    "admission": "bff3ad820aab10dedb461fe7256977546210ed0ba747c2b882368d0ab70746a2",
    "targets": "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c",
    "jar": "936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88",
}


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024**2), b""):
            h.update(chunk)
    return h.hexdigest()


def row_sha(value):
    return contract.digest(value)


def compose(accounting, admission, targets, score):
    task_ids = admission["task_ids"]
    if len(task_ids) != 20 or len(set(task_ids)) != 20:
        raise ValueError("exact TRAIN20 admission required")
    target_map = {row["id"]: (row, enc) for row, enc in zip(targets["rows"], targets["encodings"])}
    generated = [row for row in accounting if row.get("arm") == "child"]
    if len(generated) != 20 or {row["id"] for row in generated} != set(task_ids):
        raise ValueError("complete child TRAIN20 accounting required")
    pairs = []
    dispositions = []
    for rollout in generated:
        source_id = rollout["id"]
        target, encoding = target_map[source_id]
        if (target["split"] != "train" or rollout["split"] != "train" or
                target["prompt_sha256"] != rollout["prompt_sha256"] or
                hashlib.sha256(rollout["raw_reply"].encode()).hexdigest() != rollout["raw_reply_sha256"] or
                contract.digest(rollout["token_ids"]) != rollout["token_ids_sha256"]):
            raise ValueError("rollout/target identity mismatch")
        positive = score(target["response"], source_id, "positive")
        negative = score(rollout["raw_reply"], source_id, "rollout")
        admitted = positive is True and negative is False
        dispositions.append({"source_id": source_id, "positive_sany": positive,
                             "negative_sany": negative, "admitted": admitted})
        if not admitted:
            continue
        positive_tokens = encoding["input_ids"][encoding["prompt_tokens"]:]
        pair = {
            "source_id": source_id,
            "protected_row": None,
            "negative_origin": "actual_model_rollout",
            "positive_sany": True,
            "negative_sany": False,
            "prompt_tokens": encoding["input_ids"][:encoding["prompt_tokens"]],
            "positive_tokens": positive_tokens,
            "negative_tokens": rollout["token_ids"],
            "eos_token_id": targets["eos_token_id"],
            "rollout_receipt_sha256": row_sha(rollout),
        }
        pairs.append(pair)
    value = {
        "kind": contract.KIND,
        "algorithm": contract.ALGORITHM,
        "protected_rows": list(contract.PROTECTED),
        "protected_training": False,
        "gate_claim": False,
        "retention": {"rows": list(contract.PROTECTED), "mode": "supplied_prefix_parent_replay",
                      "required_sany_passes": 2, "credit": "zero"},
        "evaluation": {"rows": list(contract.PROTECTED), "mode": "unchanged_unsupplied_frozen_prompts",
                       "denominator": 2, "required_sany_passes": 2},
        "pairs": pairs,
        "provenance": {"pins": PINS, "task_ids": task_ids, "dispositions": dispositions,
                       "requested": 20, "admitted": len(pairs), "training_authorized": False},
    }
    value["objective_sha256"] = contract.digest({"kind": contract.KIND,
                                                  "algorithm": contract.ALGORITHM, "pairs": pairs})
    return contract.validate(value)


def build(output, java):
    paths = {"accounting": ACCOUNTING, "admission": ADMISSION, "targets": TARGETS, "jar": JAR}
    if {name: file_sha(path) for name, path in paths.items()} != PINS:
        raise ValueError("frozen packet inputs changed")
    output.mkdir(parents=True, exist_ok=False)
    def score(text, source_id, label):
        result = checker.sany(text, output / "sany" / source_id.replace(":", "_") / label, java, JAR)
        return result["passed"]
    value = compose(json.loads(ACCOUNTING.read_text()), json.loads(ADMISSION.read_text()),
                    json.loads(TARGETS.read_text()), score)
    (output / "packet.json").write_text(json.dumps(value, indent=2) + "\n")
    lengths = [(len(pair["prompt_tokens"]), len(pair["positive_tokens"]), len(pair["negative_tokens"]))
               for pair in value["pairs"]]
    summary = {"complete": True, "requested": 20, "admitted": len(value["pairs"]),
               "rejected_or_unknown": 20 - len(value["pairs"]), "packet_sha256": file_sha(output / "packet.json"),
               "max_prompt_tokens": max(x[0] for x in lengths),
               "max_positive_full_tokens": max(x[0] + x[1] for x in lengths),
               "max_negative_full_tokens": max(x[0] + x[2] for x in lengths),
               "min_positive_response_tokens": min(x[1] for x in lengths),
               "min_negative_response_tokens": min(x[2] for x in lengths),
               "training_authorized": False, "gate_claim": False}
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--java", default="/usr/bin/java")
    args = parser.parse_args()
    print(json.dumps(build(args.output.resolve(), args.java)))


if __name__ == "__main__":
    main()
