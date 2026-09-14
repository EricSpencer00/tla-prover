"""Local diagnostic for multi-token structural supervision.

This does not alter the frozen experiment.  It identifies complete structural
lines/spans in reference modules and verifies that each span is anchored at a
response-only token boundary, so a future runner can prefer coherent spans
instead of only one positive token against one corrupted token.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


BOUNDARY = re.compile(
    r"(?m)^(?:EXTENDS|CONSTANTS|ASSUME|VARIABLES?|[A-Za-z_]\w*\s*==|"
    r"INSTANCE|THEOREM|LEMMA|PROPOSITION|====)(?:\b|\s|$)"
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def structural_spans(text):
    """Return non-empty top-level structural spans, preserving exact text."""
    matches = list(BOUNDARY.finditer(text))
    spans = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        value = text[match.start():end]
        if value.strip():
            spans.append({"kind": match.group(0).split()[0], "text": value})
    return spans


def response_only_targets(prompt_tokens, input_ids, spans, tokenizer):
    """Map exact structural spans to token ranges after the prompt."""
    targets = []
    cursor = prompt_tokens
    for span in spans:
        ids = tokenizer.encode(span["text"], add_special_tokens=False)
        if not ids:
            continue
        if input_ids[cursor:cursor + len(ids)] != ids:
            raise ValueError("structural span is not contiguous at response boundary")
        finish = cursor + len(ids)
        if finish > len(input_ids):
            raise ValueError("structural span exceeds encoded response")
        targets.append({"kind": span["kind"], "start": cursor,
                        "end": finish, "token_ids": ids,
                        "text_sha256": sha(span["text"].encode())})
        cursor = finish
    return targets


def structured_preference_pairs(packet, tokenizer, selected_rows=None):
    """Build response-only positive span vs corrupted-span token pairs.

    The returned prefixes end immediately before each complete structural span;
    no prompt token can enter the objective.  SANY screening belongs to
    ``build_span_manifest`` and is intentionally kept separate from tokenization.
    """
    pairs = []
    selected = set(selected_rows) if selected_rows is not None else None
    for row_index, row in enumerate(packet["rows"]):
        if selected is not None and row_index not in selected:
            continue
        encoding = packet["encodings"][row_index]
        spans = structural_spans(row["response"])
        targets = response_only_targets(encoding["prompt_tokens"], encoding["input_ids"], spans, tokenizer)
        for target in targets:
            bad_text = row["response"][:row["response"].find(next(s["text"] for s in spans if sha(s["text"].encode()) == target["text_sha256"]))]
            # Corrupt only the first non-whitespace character of this span.
            span_text = next(s["text"] for s in spans if sha(s["text"].encode()) == target["text_sha256"])
            first = next(i for i, c in enumerate(span_text) if not c.isspace())
            bad_span = span_text[:first] + "@" + span_text[first + 1:]
            suffix_start = row["response"].find(span_text, len(bad_text))
            bad = row["response"][:suffix_start] + bad_span + row["response"][suffix_start + len(span_text):]
            bad_ids = tokenizer.encode(
                tokenizer.apply_chat_template([
                    {"role": "user", "content": row["prompt"]},
                    {"role": "assistant", "content": bad}],
                    tokenize=False, add_generation_prompt=False), add_special_tokens=False)
            positive = encoding["input_ids"][target["start"]:target["end"]]
            divergence = next((i for i, (good, corrupt) in enumerate(zip(positive, bad_ids[target["start"]:] if len(bad_ids) > target["start"] else [])) if good != corrupt), None)
            if divergence is None:
                raise ValueError("corruption did not change span tokenization")
            pairs.append({"row": row_index, "kind": target["kind"],
                          "prefix": encoding["input_ids"][:target["start"] + divergence],
                          "positive": positive[divergence], "negative": bad_ids[target["start"] + divergence],
                          "positive_span_sha256": target["text_sha256"], "negative_sha256": sha(bad.encode())})
    return pairs


def diagnose(packet):
    rows = []
    for index, row in enumerate(packet["rows"]):
        text = row["response"]
        spans = structural_spans(text)
        rows.append({"index": index, "id": row["id"],
                     "response_sha256": sha(text.encode()),
                     "span_count": len(spans),
                     "span_kinds": [span["kind"] for span in spans],
                     "response_chars": len(text)})
    return rows


def span_corruptions(text):
    """Return bounded whole-span corruptions that must fail SANY."""
    spans = structural_spans(text)
    result = []
    for i, span in enumerate(spans):
        value = span["text"]
        start = text.find(value)
        if start < 0:
            raise ValueError("span not found in source")
        # An illegal leading character is deliberately unambiguous for SANY,
        # including the module terminator (where config text could be ignored).
        first = next((j for j, char in enumerate(value) if not char.isspace()), None)
        if first is None:
            continue
        bad_value = value[:first] + "@" + value[first + 1:]
        bad = text[:start] + bad_value + text[start + len(value):]
        result.append({"span_index": i, "kind": span["kind"], "text": bad})
    return result


def sany_screen(text, output, java, jar):
    """Run pinned SANY and classify parser/semantic results conservatively."""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    module = module_name(text)
    (output / (module + ".tla")).write_text(text)
    proc = subprocess.run([java, "-cp", str(Path(jar).resolve()), "tla2sany.SANY", module + ".tla"],
                          cwd=output, capture_output=True, text=True, timeout=30)
    log = proc.stdout + proc.stderr
    (output / "sany.log").write_text(log)
    passed = proc.returncode == 0 and "Semantic processing of module " + module in log and not re.search(
        r"\*\*\*\s*(?:Parse|Semantic)|Fatal errors|Parse Error|Semantic errors|Exception", log, re.I)
    return {"passed": bool(passed), "returncode": proc.returncode}


def build_span_manifest(packet, output, java, jar, selected_rows=None):
    """SANY-screen structural spans and emit immutable positive/negative pairs."""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    pairs = []
    for row_index, row in enumerate(packet["rows"]):
        if selected_rows is not None and row_index not in selected_rows:
            continue
        text = row["response"]
        if not re.search(r"^-+\s*MODULE\s+\w+\s*-+\s*$", text, re.M):
            continue
        positive = sany_screen(text, output / f"controls/{row_index}/positive", java, jar)
        if not positive["passed"]:
            raise ValueError(f"positive SANY control failed for row {row_index}")
        for corruption in span_corruptions(text):
            negative = sany_screen(corruption["text"], output / f"controls/{row_index}/negative-{corruption['span_index']}", java, jar)
            if negative["passed"]:
                raise ValueError(f"corruption unexpectedly passed SANY: row {row_index}, span {corruption['span_index']}")
            pairs.append({"row": row_index, "span_index": corruption["span_index"],
                          "kind": corruption["kind"], "positive_sha256": sha(text.encode()),
                          "negative_sha256": sha(corruption["text"].encode())})
    result = {"kind": "syntax_structured_span_preference_v1", "pairs": pairs,
              "rows": diagnose(packet), "gate_claim": False}
    dump(output / "manifest.json", result)
    return result


def module_name(text):
    match = re.search(r"^-+\s*MODULE\s+(\w+)\s*-+\s*$", text, re.M)
    if not match:
        raise ValueError("canonical module header required")
    return match.group(1)


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("packet", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--jar", type=Path)
    parser.add_argument("--java", default="java")
    parser.add_argument("--rows", nargs="*", type=int)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    packet = json.loads(args.packet.read_text())
    result = {"kind": "syntax_structure_diagnostic_v1",
              "packet_sha256": sha(args.packet.read_bytes()),
              "rows": diagnose(packet)}
    if args.jar:
        result["structured_span_manifest"] = build_span_manifest(packet, args.output / "screened", args.java, args.jar,
                                                                  set(args.rows) if args.rows else None)
    (args.output / "diagnostic.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"rows": len(result["rows"]), "output": str(args.output)}))


if __name__ == "__main__":
    main()
