"""Safely assemble a single model-proposed patch into a frozen TLA+ module."""

import hashlib
import json


def _nonblank_lines(text):
    return [line.strip() for line in text.splitlines() if line.strip()]


def _module_frame(text):
    lines = text.splitlines()
    headers = [line for line in lines if line.lstrip().startswith('---- MODULE ')]
    if len(headers) != 1 or text.count('====') != 1:
        raise ValueError('source must have exactly one module frame')
    return headers[0], '===='


def apply_patch(source, candidate):
    """Apply one anchored replacement while preserving the original module frame."""
    header, terminator = _module_frame(source)
    if isinstance(candidate, str):
        candidate = json.loads(candidate)
    if set(candidate) != {'op', 'anchor', 'replacement'} or candidate['op'] != 'replace':
        raise ValueError('candidate must be one replace operation')
    anchor, replacement = candidate['anchor'], candidate['replacement']
    if not isinstance(anchor, str) or not isinstance(replacement, str) or not anchor or not replacement:
        raise ValueError('anchor and replacement must be nonempty strings')
    if '---- MODULE ' in replacement or '====' in replacement:
        raise ValueError('replacement must not contain module framing')
    nonblank = _nonblank_lines(replacement)
    if len(nonblank) != len(set(nonblank)):
        raise ValueError('replacement repeats a nonblank line')
    if source.count(anchor) != 1:
        raise ValueError('anchor must occur exactly once in source')
    assembled = source.replace(anchor, replacement, 1)
    if _module_frame(assembled) != (header, terminator):
        raise ValueError('assembled module framing changed')
    return assembled


def receipt(source, candidate):
    assembled = apply_patch(source, candidate)
    return {
        'candidate_sha256': hashlib.sha256(json.dumps(candidate, sort_keys=True).encode()).hexdigest(),
        'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'assembled_sha256': hashlib.sha256(assembled.encode()).hexdigest(),
        'gate_claim': False,
    }
