"""Toy end-to-end pipeline smoke: stages A (generation loop) and B (corpus ->
harmony SFT file), driven by a deterministic scripted model so the run is
zero-spend and reproducible, while every VERIFICATION gate (SANY, TLC,
mutation battery, vacuity, fidelity contract) runs for real.

The remaining stages (tiny train, merge, serve, gen-eval, gate-check) are
orchestrated by tools/smoke/run_e2e.sh; this module is the pure-harness half.

Usage: python3 -m harness.smoke_e2e <run_dir>
Exit nonzero on any assertion failure.
"""
import json
import sys
from pathlib import Path

from . import w2_loop as wl
from .corpus_prep import build_sft_file

# Tiny known-good spec (same fixture family as test_w2_loop): passes SANY,
# TLC (non-vacuous), and the mutation battery, so the FULL gate stack runs.
GOOD_SPEC = """---- MODULE Counter ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Dec == x > 0 /\\ x' = x - 1
Inc == x < 3 /\\ x' = x + 1
Next == Dec \\/ Inc
Spec == Init /\\ [][Next]_x
NonNegative == x >= 0
====
"""
GOOD_CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"
GOOD_REPLY = f"```tla\n{GOOD_SPEC}\n```\n```cfg\n{GOOD_CFG}\n```\nPROPERTY_INVARIANT: NonNegative\n"

# First sample deliberately fails SANY so the repair-context iteration path
# is exercised too, not just the happy path.
BAD_SANY_SPEC = GOOD_SPEC.replace("Next == Dec \\/ Inc", "Next == Dec \\/")
BAD_REPLY = f"```tla\n{BAD_SANY_SPEC}\n```\n```cfg\n{GOOD_CFG}\n```\nPROPERTY_INVARIANT: NonNegative\n"

NL = ("A simple bounded counter system. The variable x starts at 0 and each "
      "step either increments or decrements it, guarded so it never goes "
      "below zero.\n\nSAFETY PROPERTY: the counter value x is always greater "
      "than or equal to zero.")


class ScriptedModel:
    id = "smoke-scripted-v1"

    def __init__(self, script):
        self.script = list(script)

    def generate(self, prompt, n, temperature, max_tokens):
        if not self.script:
            raise AssertionError("ScriptedModel script exhausted")
        r = self.script.pop(0)
        return r if isinstance(r, list) else [r] * n


def stage_gen(run_dir: Path) -> Path:
    """Run the real W2 loop gates on scripted replies; write a w2_survivors.jsonl
    ledger in the exact format run_w2 produces."""
    print("== stage A: generation loop (real SANY/TLC/mutation gates) ==")
    model = ScriptedModel([[BAD_REPLY], [GOOD_REPLY]])
    work = run_dir / "work"
    work.mkdir(parents=True, exist_ok=True)
    result = wl.run_loop_for_seed(model, NL, "Counter", work, timeout=60, max_iters=4)
    assert result["survived"] is True, f"loop did not survive: {result['rejection_reason']}"
    assert result["iters"] == 2, f"expected SANY-repair iteration, got iters={result['iters']}"
    row = {"seed_key": "smoke::k0", "source": "smoke", "k": 0, "nl": NL, **result}
    ledger = run_dir / "w2_survivors.jsonl"
    ledger.write_text(json.dumps(row) + "\n")
    print(f"survivor written: iters={result['iters']} states={result['distinct_states']} "
          f"kill_rate={result['kill_rate']}")
    return ledger


def stage_corpus(run_dir: Path) -> Path:
    print("== stage B: corpus -> harmony SFT file ==")
    out = run_dir / "sft_smoke.jsonl"
    n = build_sft_file([str(run_dir)], out)
    assert n >= 1, "no SFT rows written"
    for line in out.read_text().splitlines():
        text = json.loads(line)["text"]
        assert "<|channel|>final" in text, "harmony final-channel marker missing"
        assert "```tla" in text, "target spec block missing"
    print(f"{n} harmony rows -> {out}")
    return out


def main():
    run_dir = Path(sys.argv[1] if len(sys.argv) > 1 else "results/runs/smoke-e2e")
    run_dir.mkdir(parents=True, exist_ok=True)
    stage_gen(run_dir)
    stage_corpus(run_dir)
    print("SMOKE STAGES A+B: OK")


if __name__ == "__main__":
    main()
