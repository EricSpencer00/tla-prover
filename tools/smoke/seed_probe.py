#!/usr/bin/env python3
"""Preflight: does this endpoint actually honor `seed`?

Run BEFORE any sweep that relies on decoder provenance. Recording seeds an
endpoint ignores is false provenance -- it makes irreproducible rows look
reproducible, which is worse than recording nothing.

    OPENAI_BASE_URL=... OPENAI_API_KEY_CMD=... \
        python3 tools/smoke/seed_probe.py --model openai/gpt-oss-120b

Three requests, same prompt, temperature 0.8:
    A, B  same seed   -- must match if the seed is honored
    C     other seed  -- must DIFFER, or the endpoint is not sampling at all

That third request is the negative control and is the reason this is not just
"call it twice". Without it, an endpoint silently pinned to greedy would report
a perfect seed implementation.

Verdicts:
  HONORED     A == B and C differs. Seeds work; provenance is real.
  IGNORED     A != B. The seed is not being applied. Do not trust decode_seed.
  DEGENERATE  A == B == C. Temperature appears to be dropped; the match is
              meaningless. Investigate before reading anything into pass@k.
  PARTIAL     A and B share a prefix then diverge. Expected on a shared vLLM:
              continuous batching changes float reduction order, so a seed pins
              the sampling RNG but not the numerics. Provenance is still useful
              and the divergence envelope is narrow -- this is an acceptable
              outcome, not a failure.

Exit status is 0 for HONORED and PARTIAL, 1 for IGNORED and DEGENERATE.
"""
import argparse
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", ".."))

from harness.repair import make_model  # noqa: E402

PROMPT = ("Write a short TLA+ module named Counter with a single variable x, "
          "an Init that sets it to 0, and a Next that increments it. "
          "Then briefly explain your choice of invariant.")

# Below this, two replies that diverge are treated as sharing a prefix only by
# coincidence rather than by the continuous-batching signature.
_PARTIAL_PREFIX_MIN = 40


def _common_prefix(a: str, b: str) -> int:
    n = 0
    for ca, cb in zip(a, b):
        if ca != cb:
            break
        n += 1
    return n


def probe(model_name: str, seed: int = 12345, other_seed: int = 67890,
          temperature: float = 0.8, max_tokens: int = 512):
    model = make_model(model_name)
    a, _ = model.generate_traced(PROMPT, 1, temperature, max_tokens, seed)[0]
    b, meta_b = model.generate_traced(PROMPT, 1, temperature, max_tokens, seed)[0]
    c, _ = model.generate_traced(PROMPT, 1, temperature, max_tokens, other_seed)[0]

    for label, text in (("A", a), ("B", b), ("C", c)):
        if text.startswith("[api_error"):
            return {"verdict": "ERROR", "detail": f"request {label}: {text[:300]}"}

    same_seed_match = a == b
    other_seed_match = a == c
    prefix = _common_prefix(a, b)

    if same_seed_match and other_seed_match:
        verdict = "DEGENERATE"
    elif same_seed_match:
        verdict = "HONORED"
    elif prefix >= _PARTIAL_PREFIX_MIN:
        verdict = "PARTIAL"
    else:
        verdict = "IGNORED"

    return {"verdict": verdict, "model": model.id, "seed": seed,
            "other_seed": other_seed, "temperature": temperature,
            "same_seed_identical": same_seed_match,
            "other_seed_identical": other_seed_match,
            "same_seed_common_prefix_chars": prefix,
            "same_seed_lengths": [len(a), len(b)],
            "provider_seed_echo": meta_b.get("provider_seed_echo"),
            "decode_params_sha256": meta_b.get("decode_params_sha256")}


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--model", required=True,
                    help="openai:<id> | anthropic[:<id>] | stub")
    ap.add_argument("--seed", type=int, default=12345)
    ap.add_argument("--other-seed", type=int, default=67890)
    ap.add_argument("--temperature", type=float, default=0.8)
    ap.add_argument("--max-tokens", type=int, default=512)
    a = ap.parse_args()

    name = a.model if (":" in a.model or a.model == "stub") else f"openai:{a.model}"
    report = probe(name, a.seed, a.other_seed, a.temperature, a.max_tokens)

    import json
    print(json.dumps(report, indent=2))
    verdict = report["verdict"]
    if verdict in ("HONORED", "PARTIAL"):
        return 0
    print(f"\nseed_probe: {verdict} -- do not run a provenance sweep against "
          "this endpoint until resolved", file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
