#!/usr/bin/env python3
"""Measure how often the harness's two module extractors disagree, offline.

    python3 tools/extractor_divergence.py [run-dir ...]

harness.gen_eval.extract_module and harness.repair.extract_candidate are two
different functions, not one function called two ways:

    gen_eval  ^-{4,}\\s*MODULE\\b.*?^={4,}                first match, line-anchored,
                                                        module name optional
    repair    (-{4,}\\s*MODULE\\s+\\w+\\s*-{4,}.*?^={4,})   last match, not anchored,
                                                        name AND trailing dashes required

Unifying them changes extraction for already-scored rows and retroactively
invalidates the ledgers in results/runs/, so the rate has to be known before
that trade is worth making. This measures it with zero API spend and zero
writes.

SCOPE LIMIT, read before quoting any number from this. _persist_candidate only
keeps the raw reply (`*.response.txt`) when gen_eval's extractor FAILED; on
success it stores the already-extracted module. So the measurable population is
exactly the no_module_extracted rows, and the question this answers is:

    of the replies gen_eval scored as no_module_extracted,
    how many would repair's extractor have parsed?

Those are rows currently counted as failures that a different extractor would
have scored. It cannot measure the reverse direction (replies both extractors
parsed but parsed differently) -- that needs raw replies to be persisted on
success too, which is a separate change.
"""
import os
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))

from harness.decoding import extraction_divergence  # noqa: E402
from harness.runner import REPO  # noqa: E402


def scan(run_dirs):
    counts = Counter()
    recoverable = []
    for run_dir in run_dirs:
        for path in sorted(Path(run_dir).glob("candidates/*.response.txt")):
            reply = path.read_text(errors="replace")
            counts["replies_examined"] += 1
            divergent, first, last = extraction_divergence(reply)
            if not divergent:
                counts["both_agree" if first is not None
                       else "neither_extracts"] += 1
                continue
            counts["divergent"] += 1
            if first is None and last is not None:
                counts["only_repair_extracts"] += 1
                recoverable.append((str(path.relative_to(REPO)), len(last)))
            elif last is None and first is not None:
                counts["only_gen_eval_extracts"] += 1
            else:
                counts["both_extract_differently"] += 1
    return counts, recoverable


def main(argv):
    # Same exclusions as tools/staircase.py: QUARANTINE/smoke/drytest/lewm are
    # not measurements of the system. A 20b mechanics smoke stores raw replies
    # like any other run, so without this its extraction behaviour would be
    # folded into the divergence rate (2026-08-31 it80).
    skip = ("QUARANTINE", "smoke", "drytest", "lewm")
    run_dirs = argv[1:] or sorted(
        p for p in (REPO / "results" / "runs").iterdir()
        if p.is_dir() and (p / "candidates").is_dir()
        and not p.name.startswith(skip))
    counts, recoverable = scan(run_dirs)

    n = counts["replies_examined"]
    print(f"run dirs scanned: {len(list(run_dirs))}")
    print(f"stored raw replies (= no_module_extracted rows): {n}")
    if not n:
        print("nothing to measure")
        return 0
    for key in ("neither_extracts", "both_agree", "divergent",
                "only_repair_extracts", "only_gen_eval_extracts",
                "both_extract_differently"):
        print(f"  {key:28s} {counts[key]:6d}  ({counts[key] / n:6.1%})")

    print(f"\nRows scored no_module_extracted that repair's extractor WOULD "
          f"have parsed: {counts['only_repair_extracts']} "
          f"({counts['only_repair_extracts'] / n:.1%} of stored replies)")
    for path, size in recoverable[:20]:
        print(f"  {path}  ({size} chars)")
    if len(recoverable) > 20:
        print(f"  ... and {len(recoverable) - 20} more")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
