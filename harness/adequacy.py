"""W1 adequacy battery -- deterministic, TLC-free structural signals over a spec.

These features are the complexity backbone of the quality corpus: they feed
`quality_gold` and serve as the complexity weights for the RFT reward (review
fix #2 -- reward structurally-rich survivors, not merely valid ones, so RFT does
not collapse toward trivial specs). Everything here is pure text analysis (no
SANY/TLC), so it is cheap and reproducible.
"""
import re

_EXTENDS_RE = re.compile(r"^\s*EXTENDS\b(.*)$", re.M)
_VARS_RE = re.compile(r"^\s*VARIABLES?\b(.*)$", re.M)
_DEF_RE = re.compile(r"^[A-Za-z_]\w*(?:\([^)]*\))?\s*==", re.M)
_IDENT_RE = re.compile(r"[A-Za-z_]\w*")
_TEMPORAL_RE = re.compile(r"\[\]|<>|WF_|SF_")
_COMMENT_LINE_RE = re.compile(r"^\s*\\\*")


def structural_features(tla_text: str) -> dict:
    """Return a dict of structural-complexity features for a TLA+ module.

    Keys: num_variables, num_definitions, extends_depth, num_disjuncts,
    num_conjuncts, temporal_op_count, noncomment_loc, comment_ratio.
    Deterministic; robust to empty input (all-zero, no crash)."""
    text = tla_text or ""

    num_variables = 0
    for m in _VARS_RE.finditer(text):
        num_variables += len(_IDENT_RE.findall(m.group(1)))

    extends_depth = 0
    m = _EXTENDS_RE.search(text)
    if m:
        extends_depth = len(_IDENT_RE.findall(m.group(1)))

    num_definitions = len(_DEF_RE.findall(text))
    num_disjuncts = len(re.findall(r"\\/", text))
    num_conjuncts = len(re.findall(r"/\\", text))
    temporal_op_count = len(_TEMPORAL_RE.findall(text))

    nonblank = [ln for ln in text.splitlines() if ln.strip()]
    comment_lines = [ln for ln in nonblank if _COMMENT_LINE_RE.match(ln)]
    noncomment_loc = len(nonblank) - len(comment_lines)
    comment_ratio = (len(comment_lines) / len(nonblank)) if nonblank else 0.0

    return {
        "num_variables": num_variables,
        "num_definitions": num_definitions,
        "extends_depth": extends_depth,
        "num_disjuncts": num_disjuncts,
        "num_conjuncts": num_conjuncts,
        "temporal_op_count": temporal_op_count,
        "noncomment_loc": noncomment_loc,
        "comment_ratio": round(comment_ratio, 3),
    }
