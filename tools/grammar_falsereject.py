"""Measure a candidate TLA+ grammar the only way that matters: against real specs.

A constrained-decoding grammar that REJECTS valid TLA+ is worse than no grammar
at all -- it makes correct output unreachable. So the gate is not "does it look
right", it is:

  false-reject rate on KNOWN-GOOD specs must be 0%
  true-reject rate on the MEASURED bad candidates is the payoff

Known-good = tools/tlaplus-examples (the official examples repo) + the 30 gold
holdout specs. Bad = candidates from the framing-A/L ledgers whose SANY log says
"Could not parse module", i.e. the 1,494 well-framed, balanced modules that fail
on real expression syntax.

Usage:
  tools/smoke/e2e/.venv/bin/python tools/grammar_falsereject.py \
      harness/grammars/tla_module_v1.ebnf [--limit N] [--show N]
"""
import argparse
import json
import re
import sys
from pathlib import Path

import xgrammar as xgr

MODULE_RE = re.compile(r"^\s*-{4,}\s*MODULE\b", re.M)
END_RE = re.compile(r"^={4,}\s*$", re.M)


def module_region(text):
    """The module only: from the first `---- MODULE` header through the first
    closing `====` line. Real .tla files carry prose before and after it (file
    banners, `Created by Leslie Lamport on ...`), and so do model replies. The
    harness's own extractor does the same, so validating the region -- not the
    whole file -- is what matches how the grammar would actually be used."""
    m = MODULE_RE.search(text)
    if not m:
        return text
    rest = text[m.start():]
    e = END_RE.search(rest)
    return rest[:e.end()] + "\n" if e else rest

REPO = Path(__file__).resolve().parents[1]
LEDGER_RUNS = ["loop-base-120b", "loop-base-120b-seed2", "loop-base-120b-seed3",
               "open-base-120b-samesession", "open-base-120b-seed3"]


def good_cfgs(limit=None):
    """Every .cfg the harness can actually hand to TLC: the committed overrides
    and drafts, plus the corpus originals."""
    out = []
    for d in [REPO / "corpus" / "configs" / "overrides",
              REPO / "corpus" / "configs" / "drafts",
              Path("/Users/eric/GitHub/tla_benchmark/data/cfg")]:
        if d.is_dir():
            out += sorted(p for p in d.glob("*.cfg") if p.stat().st_size > 0)
    return out[:limit] if limit else out


def good_specs(limit=None):
    """Official examples + the gold holdout. Modules only -- no .cfg, no PlusCal-
    only files without a MODULE header."""
    out = []
    for p in sorted((REPO / "tools" / "tlaplus-examples").rglob("*.tla")):
        out.append(p)
    corpus = Path("/Users/eric/GitHub/tla_benchmark/data/tla_files")
    if corpus.is_dir():
        holdout = json.loads((REPO / "corpus" / "holdout_30.json").read_text())
        nums = (holdout if isinstance(holdout, list)
                else holdout.get("holdout_specs") or holdout.get("specs") or [])
        for n in nums:
            p = corpus / f"{n}.tla"
            patch = REPO / "corpus" / "configs" / "patches" / f"{n}.tla"
            out.append(patch if patch.exists() else p)
    out = [p for p in out if p.is_file()]
    return out[:limit] if limit else out


def bad_candidates(limit=None):
    out = []
    for r in LEDGER_RUNS:
        run = REPO / "results" / "runs" / r
        rows = run / "rows.jsonl"
        if not rows.is_file():
            continue
        seen = set()
        for line in rows.read_text().splitlines():
            if not line.strip():
                continue
            x = json.loads(line)
            key = (x.get("spec"), str(x.get("sample")))
            if key in seen:
                continue
            seen.add(key)
            if x.get("sany") != "fail" or not x.get("candidate_path"):
                continue
            lp = Path(x.get("log_path", ""))
            if not lp.is_file() or "Could not parse module" not in lp.read_text(errors="replace"):
                continue
            p = run / x["candidate_path"]
            if p.is_file():
                out.append(p)
    return out[:limit] if limit else out


def make_checker(ebnf):
    grammar = xgr.Grammar.from_ebnf(ebnf)          # raises on EBNF syntax error
    info = xgr.TokenizerInfo([], vocab_size=0)
    compiler = xgr.GrammarCompiler(info)
    compiled = compiler.compile_grammar(grammar)

    def accepts(text):
        m = xgr.GrammarMatcher(compiled)
        try:
            if not m.accept_string(text):
                return False
        except Exception:
            return False
        return m.is_terminated() or True

    def first_reject(text):
        """Character index the grammar first refuses (None if it accepts all).
        Fed one character at a time -- slow, only used for diagnosis."""
        m = xgr.GrammarMatcher(compiled)
        for i, ch in enumerate(text):
            try:
                if not m.accept_string(ch):
                    return i
            except Exception:
                return i
        return None

    accepts.first_reject = first_reject
    return accepts


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("grammar")
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--show", type=int, default=5, help="print this many rejects")
    ap.add_argument("--cfg", action="store_true",
                    help="validate a TLC .cfg grammar against every .cfg in the "
                         "corpus instead of the module grammar against .tla")
    ap.add_argument("--skip-bad", action="store_true")
    ap.add_argument("--exclude-proofs", action="store_true",
                    help="drop TLAPS-proof-bearing specs from the good set. The "
                         "generator emits ~0 proof modules, so this is the "
                         "population a decode-time grammar would actually "
                         "constrain -- but report BOTH numbers, never only this one.")
    ap.add_argument("--diagnose", type=int, default=0,
                    help="for this many rejected good specs, print the first "
                         "character position the grammar refuses and its context")
    a = ap.parse_args()

    ebnf = Path(a.grammar).read_text()
    accepts = make_checker(ebnf)
    print(f"grammar compiles: {Path(a.grammar).name}\n")

    good = good_cfgs(a.limit) if a.cfg else good_specs(a.limit)
    if a.exclude_proofs and not a.cfg:
        pf = re.compile(r"^\s*<\d+>|^\s*(BY|OBVIOUS|OMITTED|QED)\b|\bPROOF\b", re.M)
        before = len(good)
        good = [p for p in good if not pf.search(p.read_text(errors="replace"))]
        print(f"(excluded {before - len(good)} proof-bearing specs of {before})")
    rejected = []
    for p in good:
        text = p.read_text(errors="replace")
        if not accepts(text if a.cfg else module_region(text)):
            rejected.append(p)
    fr = len(rejected) / max(len(good), 1)
    label = "KNOWN-GOOD .cfgs " if a.cfg else "KNOWN-GOOD specs  "
    print(f"{label} : {len(good)}   false-rejected {len(rejected)}  = {fr:.1%}")
    for p in rejected[:a.show]:
        print(f"    reject: {p.relative_to(REPO) if REPO in p.parents else p}")
    for p in rejected[:a.diagnose]:
        t = p.read_text(errors="replace")
        t = t if a.cfg else module_region(t)
        i = accepts.first_reject(t)
        if i is None:
            continue
        line = t[:i].count("\n") + 1
        lo = t.rfind("\n", 0, max(0, i - 90)) + 1
        print(f"\n--- {p.name}: first refused at char {i} (line {line})")
        print("    " + t[lo:i].replace("\n", "\n    ")[-200:] + "  <<<HERE>>>  "
              + t[i:i + 40].replace("\n", " "))

    if not a.skip_bad and not a.cfg:
        bad = bad_candidates(a.limit)
        caught = [p for p in bad
                  if not accepts(module_region(p.read_text(errors="replace")))]
        tr = len(caught) / max(len(bad), 1)
        print(f"\nMEASURED bad parses: {len(bad)}   rejected {len(caught)}  = {tr:.1%} caught")

    print("\nGATE: " + ("PASS (0 false rejects)" if not rejected
                        else f"FAIL ({len(rejected)} valid specs made unreachable)"))
    return 1 if rejected else 0


if __name__ == "__main__":
    sys.exit(main())
