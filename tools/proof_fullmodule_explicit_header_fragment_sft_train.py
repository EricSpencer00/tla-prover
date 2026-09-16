"""Bounded SFT diagnostic for explicit-header body continuation.

This worker reuses the audited optimizer/checkpoint path but changes the
stream contract materially: the runtime supplies the exact canonical module
header and the model emits only the remaining body bytes.  There is no
header insertion into a model response, repair, verifier feedback, or replay
negative.  A generated body is assembled behind the supplied header and sent
to the same independent SANY path.
"""

from pathlib import Path
import hashlib
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_streaming_sft_train as base
from tools import proof_fullmodule_streaming_parser_admission as parser


EXPERIMENT_KIND = "fullmodule_explicit_header_fragment_sft_v1"
_HEADERS = {}
_BASE_SOURCE_PINS = base.source_pins
_BASE_LOAD_PACKET = base.load_packet


def _header_for(module_name):
    try:
        return _HEADERS[module_name]
    except KeyError as exc:
        raise ValueError(f"exact canonical header unavailable for {module_name}") from exc


def _split_header(source):
    first = source.splitlines(keepends=True)[:1]
    if not first:
        raise ValueError("empty module source")
    return first[0]


def _header_name(header):
    match = re.match(r"^-+ MODULE ([A-Za-z_][A-Za-z0-9_]*) -+", header.rstrip("\r\n"))
    if not match:
        raise ValueError("canonical module header required")
    return match.group(1)


def load_packet(path):
    packet, rows = _BASE_LOAD_PACKET(path)
    _HEADERS.clear()
    for row in base.W4_ROWS:
        header = _split_header(rows[row]["response"])
        _HEADERS[_header_name(header)] = header
    for row in base.PROTECTED:
        header = _split_header(rows[row]["response"])
        _HEADERS[base.MODULE_NAMES[row]] = header
    return packet, rows


def stream_segments(response, structure, count=4):
    """Partition only body bytes into fixed nonempty continuation fragments."""
    header = _split_header(response)
    body = response[len(header):]
    count = min(int(count), len(body))
    if count <= 0:
        raise ValueError("body has no continuation bytes")
    result = []
    for index in range(count):
        start = index * len(body) // count
        end = (index + 1) * len(body) // count
        result.append(body[start:end])
    if any(not item for item in result) or "".join(result) != body:
        raise AssertionError("body segmentation is not nonempty and lossless")
    return result


def stream_prompt(source_prompt, module_name, segment, prefix=""):
    header = _header_for(module_name)
    body_prefix = prefix
    if body_prefix.startswith(header):
        body_prefix = body_prefix[len(header):]
    text = (
        "\n\n=== EXPLICIT HEADER BODY CONTRACT ===\n"
        "The runtime supplies the exact canonical module header below. Emit "
        "only the exact body bytes after it; never emit the header, MODULE: or "
        "SEGMENT: metadata, markdown, or explanations. The body must end with "
        "the complete module footer.\n"
        "RUNTIME-SUPPLIED EXACT HEADER:\n" + header +
        "If a body prefix is shown, continue immediately after it.\n")
    if body_prefix:
        text += "CURRENT EXACT BODY PREFIX:\n" + body_prefix + "\n"
    else:
        text += "Begin with the first exact byte after the supplied header.\n"
    return source_prompt + text


def source_pins():
    result = _BASE_SOURCE_PINS()
    result["tools/proof_fullmodule_explicit_header_fragment_sft_train.py"] = file_sha(Path(__file__))
    result["tools/proof_fullmodule_fragment_contract_probe.py"] = file_sha(
        Path(__file__).with_name("proof_fullmodule_fragment_contract_probe.py"))
    return result


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def evaluate_protected(net, tokenizer, rows, output, phase, tasks, sany_identity):
    from tools import proof_fullmodule_multiexample_probe as multi

    results = {}
    for row in base.PROTECTED:
        source, module = rows[row], base.MODULE_NAMES[row]
        header = _header_for(module)
        stream = parser.ModuleStream()
        stream.feed(header)
        assembled, parts = header, []
        plan = dict(raw_reply="", raw_reply_sha256=base.sha(b""), output_tokens=0,
                    finish_reason="not_used", deadline_exceeded=False, elapsed_seconds=0.)
        item = dict(row=row, phase=phase, module_name=module,
                    stream_contract="explicit_header_body_v1", runtime_header_sha256=base.sha(header.encode()), plan=plan)
        for segment in range(base.BUDGET["stream_segments"]):
            prompt = stream_prompt(source["prompt"], module, segment, assembled)
            generated = multi.decode(net, tokenizer, base.prompt_only(tokenizer, prompt))
            parts.append(dict(segment=segment, generation=generated))
            try:
                stream.feed(generated["raw_reply"])
            except ValueError as exc:
                item["stream_reject"] = str(exc)
                break
            assembled = stream.text
            if generated["finish_reason"] == "eos":
                try:
                    stream.finish()
                except ValueError as exc:
                    item["stream_reject"] = str(exc)
                break
        item["parts"] = parts
        item["assembled_sha256"] = base.sha(assembled.encode()) if assembled else None
        item["assembled_char_count"] = len(assembled)
        complete = False
        if "stream_reject" not in item:
            try:
                stream.finish()
                complete = True
            except ValueError as exc:
                item["stream_reject"] = str(exc)
        if complete:
            item["sany"] = multi.sany.check(
                tasks[row], assembled, output / f"sany_candidate/{phase}/{row}",
                sany_identity, timeout=base.BUDGET["sany_seconds"])
        else:
            item["sany"] = None
        base.dump(output / f"{phase}-row-{row}.json", item)
        results[str(row)] = item
    return results


def main():
    base.EXPERIMENT_KIND = EXPERIMENT_KIND
    base.BUDGET = dict(
        base.BUDGET,
        seed=20260919,
        objective="explicit_header_body_fragment_sft",
    )
    base.load_packet = load_packet
    base.stream_segments = stream_segments
    base.stream_prompt = stream_prompt
    base.source_pins = source_pins
    base.evaluate_protected = evaluate_protected
    base.main()


if __name__ == "__main__":
    main()
