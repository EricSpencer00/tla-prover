"""Decoder provenance: seeds that are derived rather than stored, and a hash of
the request body actually sent (docs/designs/2026-08-08-decode-provenance-design.md).

Why this exists: no `seed` was sent on any model request, so the 5-passes->1-pass
swing on spec 30 between gate2-w4dg-120b-A and -A3 (tools/rowlevel_power.py:8-11,
byte-identical prompt_sha256) could not be attributed or replayed. Model.generate's
docstring already claimed reproducibility "from (model id, prompt hash, seed
semantics of the provider)" -- this module makes the third term real.

Two design points worth keeping:

  * Seeds are DERIVED from run identity, not stored and hoped for. A truncated or
    lost rows.jsonl line does not make a sample unreproducible: replay recomputes
    the same seed from (run_id, spec, framing, sample_id).

  * The params hash is taken over the POST-MERGE body. OPENAI_EXTRA_BODY is applied
    after the base body in OpenAICompatModel._one, so a stale extra body can
    silently override the harness's seed; hashing what was actually sent is the
    only way that shows up in the ledger.

This module is pure: no network, no environment reads, no I/O.
"""
import hashlib
import inspect
import json

# vLLM, the OpenAI API, and the ALCF router all accept a signed-32-bit-positive
# seed; some reject values outside it. This mask is the intersection.
SEED_MASK = 0x7FFFFFFF

# Excluded from the params hash: prompt_sha256 already covers the prompt, and
# including it would make the params hash useless for grouping rows by budget.
_PARAMS_HASH_EXCLUDE = frozenset({"messages", "prompt"})


def derive_seed(run_id: str, spec, framing: str, sample_id) -> int:
    """Deterministic per-sample decoder seed.

    Stable across processes and Python versions (sha256 of a NUL-joined string,
    not hash()). Distinct in each of the four inputs, so the greedy and sampled
    arms of one spec do not collide, and two runs of the same spec do not either.
    """
    key = "\x00".join([str(run_id), str(spec), str(framing), str(sample_id)])
    digest = hashlib.sha256(key.encode()).digest()
    return int.from_bytes(digest[:4], "big") & SEED_MASK


def effective_params_sha256(body: dict) -> str:
    """Hash the request body actually sent, minus the prompt.

    Two runs that believe they share Amendment 12's frozen budget but differ in
    reasoning_effort, top_p, or an OPENAI_EXTRA_BODY-injected seed will show
    different hashes here. Key order is normalized so dict construction order
    cannot change the hash.
    """
    trimmed = {k: v for k, v in body.items() if k not in _PARAMS_HASH_EXCLUDE}
    canonical = json.dumps(trimmed, sort_keys=True, default=str)
    return hashlib.sha256(canonical.encode()).hexdigest()


def url_sha256(url: str) -> str:
    """Hash an endpoint URL for the ledger.

    OPENAI_BASE_URL can carry routing detail and, on some deployments, a token in
    the path. Rows record this hash so two runs can be compared for
    same-vs-different backend without the URL or any credential entering the
    append-only ledger.
    """
    return hashlib.sha256((url or "").encode()).hexdigest()


def generate_traced_compat(model, prompt, n, temperature, max_tokens, seed=None):
    """Call a model's traced path, tolerating implementations that predate it.

    The harness has eleven duck-typed model stand-ins that do not subclass
    harness.repair.Model and expose only the original four-argument
    `generate(prompt, n, temperature, max_tokens)` -- five of them in production
    code (w2_loop._Fixed, w4_verify_cell._OneShot, w4_difficulty._OneShot,
    gen_eval's local-stub, smoke_e2e's), the rest in tests. Requiring them all to
    grow a method would be a wide, mechanical edit to code this change has no
    other reason to touch, and would silently break any external caller passing
    its own stub.

    So the ladder is: generate_traced if present; else generate with a seed if it
    accepts one; else the original four-argument call. Anything below the first
    rung returns empty provenance, which rows record as nulls -- honestly
    reporting "this call carried no seed" rather than inventing one.
    """
    traced = getattr(model, "generate_traced", None)
    if traced is not None:
        return traced(prompt, n, temperature, max_tokens, seed)
    try:
        accepts_seed = "seed" in inspect.signature(model.generate).parameters
    except (TypeError, ValueError):  # C-implemented or otherwise unintrospectable
        accepts_seed = False
    if accepts_seed:
        return [(t, {}) for t in
                model.generate(prompt, n, temperature, max_tokens, seed)]
    return [(t, {}) for t in model.generate(prompt, n, temperature, max_tokens)]


def extraction_divergence(reply: str):
    """Compare the two module extractors on one raw reply.

    harness.gen_eval.extract_module and harness.repair.extract_candidate are two
    different functions, not one function called two ways -- they differ in the
    regex (module name and trailing dashes required or not, line-anchored or not)
    as well as in which match is taken (first vs last). Unifying them would change
    extraction for already-scored rows and retroactively invalidate every ledger in
    results/runs/, so both are frozen and the disagreement is measured instead.

    Returns (divergent, first_text, last_text). Divergent is True when the two
    disagree OR exactly one returns None -- a reply only one extractor can parse is
    the most interesting case, not an exclusion from it. Both None is not
    divergent; that row's verdict is already no_module_extracted.

    Pure string work on an in-memory reply: no API call, no SANY, no TLC.
    """
    from .gen_eval import extract_module
    from .repair import extract_candidate

    first = extract_module(reply)
    last = extract_candidate(reply)
    if first is None and last is None:
        return False, None, None
    if first is None or last is None:
        return True, first, last
    return first.rstrip() != last.rstrip(), first, last
