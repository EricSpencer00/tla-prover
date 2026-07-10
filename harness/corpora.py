"""W2.1 funnel primitives: exact-dup removal + near-dup decontamination.

Method (deterministic, documented per PLAN.md W2.1 / Rule 4):

1. Normalization: TLA+ comments removed — nested block comments ``(* ... *)``
   and line comments ``\\* ...`` — then the text is split on whitespace and
   punctuation boundaries into tokens. No identifier renaming/abstraction:
   we bias toward *removal* (a rename lowers similarity, so the threshold is
   set low to compensate).
2. Exact duplicates: sha256 of the normalized token stream (whitespace- and
   comment-insensitive). First occurrence kept, later ones removed as ``dup``.
3. Near-dup decontamination: 5-token shingles (k=5), hashed; Jaccard
   similarity against every canonical shingle set (206 tla_benchmark specs +
   every .tla in tlaplus/examples). Verdict ``contaminated`` iff
   Jaccard >= 0.65 against any canonical file. 0.65 errs toward removal:
   published near-dup work commonly uses 0.7-0.85 for "same document".
   Files shorter than k tokens contribute one whole-sequence shingle so they
   are never exempt.

All functions are pure; the sweep script (results/runs/w21-funnel-*) wires
them to disk.
"""
from __future__ import annotations

import hashlib
import re
from pathlib import Path

NEAR_DUP_THRESHOLD = 0.65
SHINGLE_K = 5

_TOKEN_RE = re.compile(r"[A-Za-z0-9_]+|[^A-Za-z0-9_\s]+")


def _strip_comments(text: str) -> str:
    """Remove nested (* *) block comments and \\* line comments."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if two == "(*":
            depth += 1
            i += 2
        elif two == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            i += 1
        elif two == "\\*":
            j = text.find("\n", i)
            i = n if j == -1 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def normalize_tla(text: str) -> list[str]:
    """Comment-stripped, whitespace-insensitive token list."""
    return _TOKEN_RE.findall(_strip_comments(text))


def normalized_hash(text: str) -> str:
    """sha256 over the normalized token stream (exact-dup key)."""
    return hashlib.sha256("\x00".join(normalize_tla(text)).encode()).hexdigest()


def content_sha256(path: Path) -> str:
    """sha256 of raw file bytes (identity in manifests)."""
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _stable_hash(tokens: tuple[str, ...]) -> int:
    """Process-independent shingle hash (PYTHONHASHSEED-proof: Rule-8 reproducibility)."""
    return int.from_bytes(hashlib.blake2b("\x00".join(tokens).encode(), digest_size=8).digest(), "big")


def shingle_set(tokens: list[str], k: int = SHINGLE_K) -> set[int]:
    """Hashed k-token shingles; whole sequence if shorter than k."""
    if not tokens:
        return set()
    if len(tokens) < k:
        return {_stable_hash(tuple(tokens))}
    return {_stable_hash(tuple(tokens[i : i + k])) for i in range(len(tokens) - k + 1)}


def jaccard(a: set[int], b: set[int]) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    return inter / (len(a) + len(b) - inter)


def nearest_similarity(query: set[int], canonical: dict[str, set[int]]) -> tuple[str, float]:
    """(name, score) of the most similar canonical shingle set."""
    best_name, best = "", -1.0
    for name, s in canonical.items():
        j = jaccard(query, s)
        if j > best:
            best_name, best = name, j
    return best_name, best
