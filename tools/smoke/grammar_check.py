"""Validate harness/grammars/*.ebnf: compiles under xgrammar (what vLLM's
guided_grammar uses) and accepts/rejects the expected strings.

Usage: tools/smoke/e2e/.venv/bin/python tools/smoke/grammar_check.py
Exit nonzero on any failure. Run this BEFORE shipping a grammar to a serve job.
"""
import sys
from pathlib import Path

import xgrammar as xgr
from transformers import AutoTokenizer

REPO = Path(__file__).resolve().parents[2]
GRAMMAR = REPO / "harness" / "grammars" / "tla_module_v0.ebnf"

GOOD = """---- MODULE Counter ----
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

BAD = [
    ("unbalanced paren", GOOD.replace("x' = x - 1", "x' = (x - 1")),
    ("no module header", GOOD.replace("---- MODULE Counter ----\n", "")),
    ("unterminated module", GOOD.replace("====\n", "")),
    ("prose preamble", "Sure! Here is the module:\n" + GOOD),
]


def main():
    ebnf = GRAMMAR.read_text()
    grammar = xgr.Grammar.from_ebnf(ebnf)  # raises on syntax error
    print(f"grammar compiles: {GRAMMAR.name}")

    tok = AutoTokenizer.from_pretrained("HuggingFaceTB/SmolLM2-135M")
    info = xgr.TokenizerInfo.from_huggingface(tok)
    compiler = xgr.GrammarCompiler(info)
    compiled = compiler.compile_grammar(ebnf)

    def fresh():
        return xgr.GrammarMatcher(compiled)

    eos = tok.eos_token_id

    def full_accept(text):
        m = fresh()
        # end-of-generation = EOS admissible after the whole string
        return m.accept_string(text) and m.accept_token(eos)

    ok = True
    if full_accept(GOOD):
        print("PASS good spec accepted")
    else:
        print("FAIL good spec rejected")
        ok = False
    for name, text in BAD:
        rejected = not full_accept(text)
        print(("PASS" if rejected else "FAIL") + f" bad case rejected: {name}")
        ok = ok and rejected
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
