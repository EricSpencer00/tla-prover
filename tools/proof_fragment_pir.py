#!/usr/bin/env python3
"""Prepare a lossless typed proof-intermediate-representation packet.

The proposed trainable target is a typed lexical stream rather than raw proof
bytes.  TRAIN fragments are encoded losslessly; DEVELOPMENT rows carry only
the immutable prompt scaffold.  This module performs packet admission only:
it does not load a model, run CUDA, call a verifier for candidate selection,
or export development answers.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
import sys
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools.proof_repair_pilot import prompt_for
MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}
DEV_IDS = {"crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof", "crdt-sum-zero-proof"}
ANSWER_KEYS = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "successful_candidate", "reward", "feedback", "repair", "target", "pir_target",
}
TOKEN_RE = re.compile(r"\s+|[A-Za-z_][A-Za-z0-9_]*|\d+|[^A-Za-z0-9_\s]", re.S)
KEYWORDS = {
    "BY", "DEF", "DEFS", "SMT", "OBVIOUS", "QED", "ASSUME", "PROVE", "CASE",
    "TAKE", "USE", "SUFFICES", "PICK", "HIDE", "DEFINE", "IN", "THEN", "ELSE",
    "NEW", "TRUE", "FALSE", "UNCHANGED", "PTL", "ZF", "ISABELLE", "ZENON",
}


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def reject_answer_fields(value, path="document"):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in ANSWER_KEYS:
                raise ValueError(f"answer-bearing field reached: {path}.{key}")
            reject_answer_fields(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_answer_fields(child, f"{path}[{index}]")


def typed_tokens(fragment: str) -> list[dict[str, str]]:
    """Tokenize while retaining every byte of whitespace and punctuation."""
    tokens = []
    position = 0
    for match in TOKEN_RE.finditer(fragment):
        if match.start() != position:
            raise ValueError("proof fragment contains an un-tokenized gap")
        text = match.group(0)
        if text.isspace():
            kind = "whitespace"
        elif text.isdigit():
            kind = "number"
        elif re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", text):
            kind = "keyword" if text in KEYWORDS else "identifier"
        else:
            kind = "symbol"
        tokens.append({"kind": kind, "text": text})
        position = match.end()
    if position != len(fragment):
        raise ValueError("proof fragment tokenization did not cover the input")
    return tokens


def decode_tokens(tokens: list[dict[str, str]]) -> str:
    if not isinstance(tokens, list):
        raise ValueError("typed target must be a list")
    result = []
    for token in tokens:
        if not isinstance(token, dict) or set(token) != {"kind", "text"}:
            raise ValueError("malformed typed token")
        if token["kind"] not in {"whitespace", "number", "keyword", "identifier", "symbol"}:
            raise ValueError("unknown typed token kind")
        if not isinstance(token["text"], str) or not token["text"]:
            raise ValueError("empty typed token")
        result.append(token["text"])
    return "".join(result)


def target_text(fragment: str) -> str:
    return json.dumps(typed_tokens(fragment), separators=(",", ":"), ensure_ascii=False)


def load_manifest(path: Path) -> tuple[bytes, list[dict], list[dict]]:
    raw = path.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("exact frozen multistep manifest required")
    manifest = json.loads(raw)
    train = [dict(task) for task in manifest["tasks"] if task.get("split") == "train"]
    dev = [dict(task) for task in manifest["tasks"] if task.get("split") == "development"]
    if {task["id"] for task in train} != TRAIN_IDS or {task["id"] for task in dev} != DEV_IDS:
        raise ValueError("unexpected train/development population")
    return raw, train, dev


def check_controls(controls_path: Path, summary_path: Path) -> dict:
    summary = json.loads(summary_path.read_text())
    controls = json.loads(controls_path.read_text())
    if (summary.get("manifest_sha256") != MANIFEST_SHA256 or
            summary.get("requested_controls") != 34 or summary.get("completed_controls") != 34 or
            summary.get("complete") is not True or len(controls) != 34):
        raise ValueError("complete strict TRAIN control receipt required")
    pairs = {(row.get("id"), row.get("control")): row for row in controls}
    if len(pairs) != 34:
        raise ValueError("duplicate or missing strict control rows")
    for task_id in TRAIN_IDS:
        positive = pairs.get((task_id, "reference")); negative = pairs.get((task_id, "omitted"))
        if (not positive or positive.get("certified") is not True or
                positive.get("proved") != positive.get("total") or positive.get("total", 0) <= 0 or
                not {"--strict", "--nofp"}.issubset(positive.get("command", []))):
            raise ValueError(f"strict positive control missing: {task_id}")
        if negative.get("certified") is not False or negative.get("status") != "contract_reject":
            raise ValueError(f"strict omitted control missing: {task_id}")
    return {
        "summary_sha256": sha(summary_path.read_bytes()),
        "controls_sha256": sha(controls_path.read_bytes()),
        "verifier_identity_sha256": sha((summary_path.parent / "verifier_identity.json").read_bytes()),
        "positive_controls": 17,
        "omitted_controls": 17,
    }


def build(manifest_path: Path, controls_path: Path, summary_path: Path, output: Path) -> dict:
    raw, train, dev = load_manifest(manifest_path)
    control_identity = check_controls(controls_path, summary_path)
    train_rows = []
    for task in train:
        fragment = task["reference_fragment"]
        encoded = typed_tokens(fragment)
        if decode_tokens(encoded) != fragment:
            raise ValueError(f"lossless TRAIN reconstruction failed: {task['id']}")
        if sha((task["prefix"] + fragment + task["suffix"]).encode()) != task["assembled_sha256"]:
            raise ValueError(f"TRAIN scaffold identity changed: {task['id']}")
        train_rows.append({
            "id": task["id"], "split": "train", "source_family": task["source_family"],
            "source_sha256": task["source_sha256"], "assembled_sha256": task["assembled_sha256"],
            "prompt": prompt_for(task),
            "prompt_sha256": sha(prompt_for(task).encode()),
            "pir_target": encoded, "pir_target_sha256": sha(target_text(fragment).encode()),
            "target_tokens": len(encoded),
        })
    dev_rows = []
    for task in dev:
        clean = {key: task[key] for key in ("id", "split", "source_family", "source_sha256",
                                             "prefix", "suffix", "theorem_name", "dependencies")}
        reject_answer_fields(clean, task["id"])
        clean["prompt_sha256"] = sha((task["prefix"] + task["suffix"]).encode())
        clean["prompt"] = prompt_for(task)
        clean["prompt_sha256"] = sha(clean["prompt"].encode())
        dev_rows.append(clean)
    packet = {
        "schema": 1,
        "packet_kind": "frozen17_typed_proof_fragment_pir",
        "manifest_sha256": sha(raw),
        "train_rows": train_rows,
        "development_rows": dev_rows,
        "train_target": "lossless typed lexical stream; model must emit JSON token events",
        "development_targets_exported": False,
        "reference_fragments_exported_for_development": False,
        "verifier_feedback_used": False,
        "repair_used": False,
        "reward_used": False,
        "official_rows_used": False,
        "controls": control_identity,
        "gpu_or_model_loaded": False,
        "optimizer_updates": 0,
        "gate_claim": False,
    }
    if len(train_rows) != 17 or len(dev_rows) != 4:
        raise ValueError("exact17/4 packet shape required")
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha((output / "packet.json").read_bytes()),
        "manifest_sha256": MANIFEST_SHA256,
        "train_rows": len(train_rows), "development_rows": len(dev_rows),
        "lossless_train_reconstructions": len(train_rows),
        "development_targets_exported": False,
        "strict_control_positive": 17, "strict_control_omitted": 17,
        "model_loaded": False, "cuda_touched": False, "optimizer_updates": 0,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--controls", type=Path, required=True)
    parser.add_argument("--controls-summary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(build(args.manifest, args.controls, args.controls_summary, args.output), indent=2))


if __name__ == "__main__":
    main()
