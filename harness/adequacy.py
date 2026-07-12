"""W1 adequacy battery -- deterministic, TLC-free structural signals over a spec.

These features are the complexity backbone of the quality corpus: they feed
`quality_gold` and serve as the complexity weights for the RFT reward (review
fix #2 -- reward structurally-rich survivors, not merely valid ones, so RFT does
not collapse toward trivial specs). Everything here is pure text analysis (no
SANY/TLC), so it is cheap and reproducible.
"""
import re

# quality_gold thresholds (design defaults; revisit before freeze).
MIN_INTERESTING_STATES = 3   # thin-model floor
T_MUT = 0.5                  # safety_catch_rate floor


def quality_label(vacuity_reasons, distinct_states, safety_catch_rate,
                  min_states=MIN_INTERESTING_STATES, t_mut=T_MUT):
    """W1 quality_gold gate. gold = non-vacuous ∧ not-thin ∧ strong-mutation.

    - vacuity_reasons: runner.vacuity_flags() output ([] = non-vacuous; bundles
      no-invariant, trivial-invariant, ≤1-state).
    - distinct_states: TLC distinct-states count (None if unknown); < min_states
      is a thin model.
    - safety_catch_rate: mutation.summarize_mutants()['safety_catch_rate']
      (None or < t_mut is a weak spec -- #4: NON-TypeOK catches only).
    Returns {"quality_gold": bool, "fail_reasons": [...]}. """
    fail = []
    if vacuity_reasons:
        fail.append("vacuous")
    if distinct_states is not None and distinct_states < min_states:
        fail.append("thin_model")
    if safety_catch_rate is None or safety_catch_rate < t_mut:
        fail.append("weak_mutation")
    return {"quality_gold": len(fail) == 0, "fail_reasons": fail}


# First-pass weights for the RFT reward (review fix #2). All non-negative so the
# score is monotonic in every structural feature (richer spec -> higher weight),
# and 0 for an empty/degenerate spec. Magnitudes are a heuristic -- revisit
# before freeze once we see the RFT-vs-holdout complexity distributions.
_COMPLEXITY_WEIGHTS = {
    "num_variables": 2.0,
    "num_definitions": 1.5,
    "num_disjuncts": 1.0,
    "num_conjuncts": 1.0,
    "temporal_op_count": 2.0,
    "extends_depth": 0.5,
    "noncomment_loc": 0.1,
}


def complexity_score(features: dict) -> float:
    """Scalar structural-complexity weight for the RFT reward (#2): reward
    survival weighted by complexity so RFT does not collapse toward trivial
    valid specs. Monotonic in each feature; 0.0 for an empty spec."""
    return round(sum(w * features.get(k, 0) for k, w in _COMPLEXITY_WEIGHTS.items()), 3)


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
