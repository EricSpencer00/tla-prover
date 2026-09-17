#!/usr/bin/env python3
"""Admit a structured full-proof line-event packet.

The model-facing target is a sequence of line events rather than raw proof
bytes or an unstructured token stream.  Canonical module framing remains in
the immutable scaffold.  Only TRAIN reference fragments are encoded; the four
DEVELOPMENT rows retain prompt/scaffold metadata and no target-bearing field.
This module performs CPU admission only and never loads a model or calls a
verifier.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
TRAIN_IDS = {
    "addtwo-init", "addtwo-step", "highest-type-step", "highest-inductive-step",
    "highest-done-step", "highest-correctness", "even-intro", "even-case-tail",
    "odd-case-tail", "simple-full", "simple-preservation", "simple-case-a",
    "simple-case-b", "simple-preservation-tail", "simple-conclusion",
    "simple-short-full", "simple-short-preservation",
}
DEV_IDS = {"crdt-type-step", "crdt-safety-step", "crdt-sum-type-proof", "crdt-sum-zero-proof"}
FORBIDDEN = {
    "reference_fragment", "response", "answer", "proof_body", "proof_module",
    "target", "target_events", "pir_target", "reward", "feedback", "repair",
}
TOKEN_RE = re.compile(r"\s+|[A-Za-z_][A-Za-z0-9_]*|\d+|[^A-Za-z0-9_\s]", re.S)
LEVEL_RE = re.compile(r"<\d+(?:\.\d+)*>")


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def digest(value) -> str:
    return sha(json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode())


def reject(value, path="document") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key in FORBIDDEN:
                raise ValueError(f"answer-bearing field: {path}.{key}")
            reject(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject(child, f"{path}[{index}]")


def token_events(body: str) -> list[dict[str, str]]:
    events = []
    offset = 0
    for match in TOKEN_RE.finditer(body):
        if match.start() != offset:
            raise ValueError("line contains an un-tokenized gap")
        text = match.group(0)
        if text.isspace():
            kind = "whitespace"
        elif text.isdigit():
            kind = "number"
        elif re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", text):
            kind = "identifier"
        else:
            kind = "symbol"
        events.append({"kind": kind, "text": text})
        offset = match.end()
    if offset != len(body):
        raise ValueError("line tokenization did not cover the input")
    return events


def line_kind(body: str) -> str:
    visible = LEVEL_RE.sub("", body.lstrip()).lstrip()
    upper = visible.upper()
    if not visible:
        return "blank"
    if upper.startswith("OBVIOUS"):
        return "obvious"
    if upper.startswith("BY ") or upper == "BY":
        return "by"
    for prefix, name in (("QED", "qed"), ("ASSUME", "assume"), ("PROVE", "prove"),
                         ("SUFFICES", "suffices"), ("CASE", "case"), ("USE", "use"),
                         ("TAKE", "take"), ("PICK", "pick"), ("HIDE", "hide")):
        if upper.startswith(prefix):
            return name
    return "text"


def encode_fragment(fragment: str) -> list[dict]:
    if not isinstance(fragment, str) or not fragment:
        raise ValueError("nonempty proof fragment required")
    result = []
    for line in fragment.splitlines(keepends=True):
        newline = line.endswith("\n")
        content = line[:-1] if newline else line
        indent = len(content) - len(content.lstrip(" "))
        body = content[indent:]
        levels = LEVEL_RE.findall(body)
        result.append({"indent": indent, "levels": levels, "kind": line_kind(body),
                       "tokens": token_events(body), "newline": newline})
    if not result:
        raise ValueError("empty line-event sequence")
    return result


def decode_fragment(events: list[dict]) -> str:
    if not isinstance(events, list) or not events:
        raise ValueError("line-event sequence required")
    lines = []
    for event in events:
        if (not isinstance(event, dict) or set(event) != {"indent", "levels", "kind", "tokens", "newline"}
                or not isinstance(event["indent"], int) or event["indent"] < 0
                or not isinstance(event["levels"], list) or not isinstance(event["kind"], str)
                or not isinstance(event["newline"], bool)):
            raise ValueError("malformed line event")
        if any(not isinstance(level, str) or not LEVEL_RE.fullmatch(level)
               for level in event["levels"]):
            raise ValueError("malformed proof level")
        tokens = event["tokens"]
        if not isinstance(tokens, list):
            raise ValueError("line tokens must be a list")
        body = "".join(token["text"] for token in tokens)
        if not isinstance(event["kind"], str) or event["kind"] not in {
                "blank", "obvious", "by", "qed", "assume", "prove", "suffices",
                "case", "use", "take", "pick", "hide", "text"}:
            raise ValueError("unknown line kind")
        if len(body) < 0:
            raise ValueError("invalid line body")
        lines.append(" " * event["indent"] + body + ("\n" if event["newline"] else ""))
    return "".join(lines)


def load_manifest(path: Path) -> tuple[list[dict], list[dict]]:
    raw = path.read_bytes()
    if sha(raw) != MANIFEST_SHA256:
        raise ValueError("exact frozen multistep manifest required")
    manifest = json.loads(raw)
    train = [dict(task) for task in manifest.get("tasks", []) if task.get("split") == "train"]
    dev = [dict(task) for task in manifest.get("tasks", []) if task.get("split") == "development"]
    if {task["id"] for task in train} != TRAIN_IDS or {task["id"] for task in dev} != DEV_IDS:
        raise ValueError("frozen17/4 population mismatch")
    return train, dev


def build(manifest_path: Path, output: Path) -> dict:
    train, dev = load_manifest(manifest_path)
    train_rows = []
    for task in train:
        events = encode_fragment(task["reference_fragment"])
        if decode_fragment(events) != task["reference_fragment"]:
            raise ValueError(f"lossless line-event reconstruction failed: {task['id']}")
        assembled = task["prefix"] + task["reference_fragment"] + task["suffix"]
        if sha(assembled.encode()) != task["assembled_sha256"]:
            raise ValueError(f"assembled identity changed: {task['id']}")
        train_rows.append({
            "id": task["id"], "split": "train", "module_name": task["module_name"],
            "theorem_name": task["theorem_name"], "source_family": task["source_family"],
            "prompt": task["prefix"], "prompt_sha256": sha(task["prefix"].encode()),
            "target_events": events, "target_events_sha256": digest(events),
            "target_lines": len(events), "assembled_sha256": task["assembled_sha256"],
        })
    dev_rows = []
    for task in dev:
        row = {key: task[key] for key in (
            "id", "split", "module_name", "theorem_name", "prefix", "suffix",
            "dependencies", "dependency_sha256", "source_family", "source_sha256",
            "assembled_sha256")}
        row["prompt_sha256"] = sha(task["prefix"].encode())
        reject(row)
        dev_rows.append(row)
    packet = {
        "schema": 1, "packet_kind": "frozen17_structured_fullproof_line_events",
        "manifest_sha256": MANIFEST_SHA256, "train_rows": train_rows,
        "development_rows": dev_rows, "development_targets_exported": False,
        "reference_fragments_exported_for_development": False,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "official_rows_used": False, "model_loaded": False, "cuda_touched": False,
        "optimizer_updates": 0, "gate_claim": False,
    }
    output.mkdir(parents=True, exist_ok=False)
    packet_path = output / "packet.json"
    packet_path.write_text(json.dumps(packet, indent=2, ensure_ascii=False) + "\n")
    summary = {
        "packet_sha256": sha(packet_path.read_bytes()), "manifest_sha256": MANIFEST_SHA256,
        "packet_kind": packet["packet_kind"], "train_rows": len(train_rows),
        "development_rows": len(dev_rows), "lossless_train_reconstructions": len(train_rows),
        "target_representation": "line depth/kind plus typed lexical events",
        "development_targets_exported": False, "model_loaded": False,
        "cuda_touched": False, "optimizer_updates": 0,
        "verifier_feedback_used": False, "repair_used": False, "reward_used": False,
        "quality_claim": False, "proof_claim": False, "gate_claim": False,
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(build(args.manifest, args.output), indent=2))


if __name__ == "__main__":
    main()
