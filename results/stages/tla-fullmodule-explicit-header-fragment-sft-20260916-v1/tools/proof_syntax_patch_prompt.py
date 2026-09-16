"""Frozen patch-only prompt scaffold and parser for syntax repair diagnostics.

This module is intentionally narrow: it emits a stable patch-only contract,
parses one JSON candidate, and can apply that candidate through the shared
patch assembler. It does not change any existing training/evaluation pipeline.
"""

import hashlib
import json
import re
import sys
from pathlib import Path

if __package__ in (None, ""):
    # The isolated PBS stage invokes this file directly.  Resolve the sibling
    # modules from the repository root in that mode instead of requiring an
    # ambient ``tools`` package on the worker.
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from tools.proof_syntax_patch_assembler import apply_patch
    from tools import proof_syntax_preference_train as syntax_train
else:
    from .proof_syntax_patch_assembler import apply_patch
    from . import proof_syntax_preference_train as syntax_train

CONTRACT = "proof_syntax_patch_prompt_v1"

_ANCHOR = re.compile(r"^-{4,}\s*MODULE\s+(\w+)\s*-{4,}\s*$", re.M)
_PATCH_RE = re.compile(r"```(?:json)?\s*(\{.*?\})\s*```", re.S | re.I)
_PROMPT_TEMPLATE = """You are repairing one frozen TLA+ spec fragment.

Contract: {contract}

Keep the module frame and identifier fixed: {module}
Return exactly one JSON object, nothing else:
  {{\"op\":\"replace\",\"anchor\":\"...\",\"replacement\":\"...\"}}

Rules:
1) ``anchor`` must be an exact unique substring of the frozen source.
2) ``replacement`` must not include module framing tokens.
3) The output must change only one anchored segment by replacement.

Frozen source SHA256: {source_sha256}

Frozen source:
{source}
"""


def module_name(source):
    m = _ANCHOR.search(source)
    if not m:
        raise ValueError("source must contain canonical module header")
    return m[1]


def source_signature(source):
    return hashlib.sha256(source.encode()).hexdigest()


def build_prompt(source, row_id):
    """Build the immutable anchored-patch contract prompt for one row."""
    mod = module_name(source)
    return _PROMPT_TEMPLATE.format(
        contract=CONTRACT,
        module=mod,
        source_sha256=source_signature(source),
        source=source,
        )


def _candidate_payload(raw):
    text = (raw or "").strip()
    if not text:
        raise ValueError("empty model reply")
    if text.startswith("```"):
        m = _PATCH_RE.search(text)
        if not m:
            raise ValueError("model reply did not contain a JSON patch object")
        text = m.group(1).strip()
    try:
        candidate = json.loads(text)
    except json.JSONDecodeError as exc:
        raise ValueError("model reply is not valid JSON") from exc
    if not isinstance(candidate, dict):
        raise ValueError("model reply must be a JSON object")
    return candidate


def parse_patch_candidate(raw):
    """Validate and normalize exactly one replace candidate."""
    candidate = _candidate_payload(raw)
    required = {"op", "anchor", "replacement"}
    if set(candidate) != required or candidate["op"] != "replace":
        raise ValueError("candidate must be one anchored replace operation")
    anchor = candidate["anchor"]
    replacement = candidate["replacement"]
    if not isinstance(anchor, str) or not isinstance(replacement, str):
        raise ValueError("anchor/replacement must be strings")
    if not anchor.strip():
        raise ValueError("anchor must be non-empty")
    if not replacement.strip():
        raise ValueError("replacement must be non-empty")
    # A doubly escaped JSON newline survives decoding as the two literal
    # characters ``\\n``.  TLA+ then sees the backslash as source text rather
    # than a line break, producing a misleading SANY parse rejection.  Reject
    # that transport error before it reaches the checker; real JSON newlines
    # have already decoded to ``\n`` here.
    if r"\n" in replacement or r"\r" in replacement:
        raise ValueError("replacement must use decoded line breaks, not literal escape text")
    if "---- MODULE " in replacement:
        raise ValueError("replacement must not include module header")
    if replacement.count("====") != 0:
        raise ValueError("replacement must not include module terminator")
    return candidate


def apply_candidate(source, raw):
    """Assemble a single model proposal against the frozen source."""
    candidate = parse_patch_candidate(raw)
    return apply_patch(source, candidate), candidate


def preflight_sany(source, raw, output, *, java="java", jar):
    """Optional SANY preflight for the assembled patch."""
    assembled, candidate = apply_candidate(source, raw)
    result = syntax_train.sany(
        assembled,
        output,
        java,
        jar,
    )
    return {
        "candidate": candidate,
        "candidate_sha256": source_signature(json.dumps(candidate, sort_keys=True)),
        "assembled_sha256": source_signature(assembled),
        "sany": result,
    }
