#!/usr/bin/env python3
"""Admit a compact length-framed proof-token sequence packet.

This is a new sequence representation after the JSON typed-token PIR negative.
Each lexical event is one tab-separated ``kind, byte_length, base64(text)``
record.  The framing is deterministic and lossless, while DEVELOPMENT rows
remain answer-free.  This module only prepares/admissions the packet; it does
not load a model, touch CUDA, call TLAPS for candidate selection, or compute a
reward.
"""
from __future__ import annotations

import argparse
import base64
import binascii
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_fragment_pir import (
    DEV_IDS,
    MANIFEST_SHA256,
    TRAIN_IDS,
    check_controls,
    decode_tokens,
    load_manifest,
    prompt_for,
    reject_answer_fields,
    sha,
    typed_tokens,
)

PACKET_KIND = "frozen17_delimited_proof_fragment_pir"
ALLOWED_KINDS = {"whitespace", "number", "keyword", "identifier", "symbol"}


def encode_stream(fragment: str) -> str:
    lines = []
    for token in typed_tokens(fragment):
        raw = token["text"].encode("utf-8")
        payload = base64.urlsafe_b64encode(raw).decode("ascii")
        lines.append(f"{token['kind']}\t{len(raw)}\t{payload}")
    return "\n".join(lines)


def decode_stream(stream: str) -> str:
    if not isinstance(stream, str) or not stream:
        raise ValueError("empty delimited stream")
    tokens = []
    for line in stream.split("\n"):
        parts = line.split("\t")
        if len(parts) != 3 or parts[0] not in ALLOWED_KINDS or not parts[1].isdigit():
            raise ValueError("malformed delimited record")
        try:
            raw = base64.b64decode(parts[2].encode("ascii"), altchars=b"-_", validate=True)
            text = raw.decode("utf-8")
        except (ValueError, UnicodeDecodeError, binascii.Error) as exc:
            raise ValueError("invalid base64 token payload") from exc
        if int(parts[1]) != len(raw) or not text:
            raise ValueError("length or empty-token mismatch")
        tokens.append({"kind": parts[0], "text": text})
    return decode_tokens(tokens)


def target_text(fragment: str) -> str:
    return encode_stream(fragment)


def build(manifest_path: Path, controls_path: Path, controls_summary_path: Path, output: Path) -> dict:
    raw, train, dev = load_manifest(manifest_path)
    control_identity = check_controls(controls_path, controls_summary_path)
    train_rows = []
    for task in train:
        target = encode_stream(task["reference_fragment"])
        if decode_stream(target) != task["reference_fragment"]:
            raise ValueError(f"lossless TRAIN reconstruction failed: {task['id']}")
        if sha((task["prefix"] + task["reference_fragment"] + task["suffix"]).encode()) != task["assembled_sha256"]:
            raise ValueError(f"TRAIN scaffold identity changed: {task['id']}")
        train_rows.append({
            "id": task["id"], "split": "train", "source_family": task["source_family"],
            "source_sha256": task["source_sha256"], "assembled_sha256": task["assembled_sha256"],
            "prompt": prompt_for(task) + "\nReturn only tab-separated lexical records: kind<TAB>UTF8_BYTE_LENGTH<TAB>URLSAFE_BASE64_TEXT.",
            "target_stream": target, "target_sha256": sha(target.encode()),
            "target_records": target.count("\n") + 1,
        })
    dev_rows = []
    for task in dev:
        clean = {key: task[key] for key in ("id", "split", "source_family", "source_sha256",
                                             "prefix", "suffix", "theorem_name", "dependencies")}
        reject_answer_fields(clean, task["id"])
        clean["prompt"] = prompt_for(task) + "\nReturn only tab-separated lexical records: kind<TAB>UTF8_BYTE_LENGTH<TAB>URLSAFE_BASE64_TEXT."
        clean["prompt_sha256"] = sha(clean["prompt"].encode())
        dev_rows.append(clean)
    packet = {
        "schema": 1, "packet_kind": PACKET_KIND, "manifest_sha256": sha(raw),
        "train_rows": train_rows, "development_rows": dev_rows,
        "train_target": "lossless length-framed typed lexical stream; no JSON punctuation",
        "development_targets_exported": False, "reference_fragments_exported_for_development": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "official_rows_used": False, "controls": control_identity,
        "gpu_or_model_loaded": False, "optimizer_updates": 0, "gate_claim": False,
    }
    if len(train_rows) != 17 or len(dev_rows) != 4:
        raise ValueError("exact17/4 packet shape required")
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha((output / "packet.json").read_bytes()), "manifest_sha256": MANIFEST_SHA256,
        "train_rows": 17, "development_rows": 4, "lossless_train_reconstructions": 17,
        "development_targets_exported": False, "strict_control_positive": 17,
        "strict_control_omitted": 17, "model_loaded": False, "cuda_touched": False,
        "optimizer_updates": 0, "quality_claim": False, "proof_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest", type=Path, required=True)
    p.add_argument("--controls", type=Path, required=True)
    p.add_argument("--controls-summary", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    print(json.dumps(build(args.manifest, args.controls, args.controls_summary, args.output), indent=2))


if __name__ == "__main__":
    main()
