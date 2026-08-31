#!/usr/bin/env python3
"""Fail if the Gate-2 answer key is tracked in the public mirror (ticket #11).

Two checks over `git ls-files`:

  1. No tracked path under harness.private_data.STRIPPED. This is the check
     that runs everywhere, including CI, and needs nothing private.

  2. With a private root mounted (TLA_PROVER_PRIVATE, or ./private): no
     tracked file enumerates the holdout membership. A file counts as a leak
     when it names at least MIN_HITS of the 30 holdout specs and at least
     PURITY of its corpus-range spec references are holdout specs -- i.e. it
     is a holdout-only artifact, not a whole-corpus ledger that happens to
     include them.

Check 2 reports rather than fixes. The Gate-2 run ledgers under results/runs/
are holdout-only by construction and are the evidence for the published
numbers, so they are listed in KNOWN_MEMBERSHIP_LEAKS instead of deleted.
Removing them is a separate decision (see docs/PRIVATE_DATA.md).
"""
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from harness import private_data  # noqa: E402

MIN_HITS = 15
PURITY = 0.65
SPEC_RE = re.compile(r"\b\d{1,3}\b")

# Holdout-only artifacts kept on purpose: they hold measured Gate-2 results,
# not the answer key. Tracked here so a NEW leak is not lost in the noise.
KNOWN_MEMBERSHIP_LEAKS = (
    "corpus/e2c_baseline.json",
    "results/analysis/holdout_family_tags.jsonl",
    "results/runs/",
)


def tracked_files():
    out = subprocess.run(["git", "ls-files", "-z"], capture_output=True, text=True, check=True)
    return [f for f in out.stdout.split("\0") if f]


def check_stripped(files):
    bad = [f for f in files if any(f == s or f.startswith(s + "/") for s in private_data.STRIPPED)]
    for f in sorted(bad):
        print(f"::error::{f}: answer-key artifact is tracked; it belongs in the private root")
    return bad


def check_membership(files):
    holdout = set(private_data.holdout_specs())
    if not holdout:
        print("membership check skipped: no private root mounted")
        return []
    new = []
    for f in files:
        if any(f.startswith(k) for k in KNOWN_MEMBERSHIP_LEAKS):
            continue
        try:
            text = Path(f).read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        nums = {int(x) for x in SPEC_RE.findall(text) if 1 <= int(x) <= 206}
        hits = holdout & nums
        if len(hits) >= MIN_HITS and nums and len(hits) / len(nums) >= PURITY:
            new.append((len(hits), f))
    for n, f in sorted(new, reverse=True):
        print(f"::error::{f}: names {n}/{len(holdout)} holdout specs and little else")
    return new


def main():
    files = tracked_files()
    bad = check_stripped(files) + check_membership(files)
    if bad:
        print(f"\n{len(bad)} answer-key leak(s) in the tracked tree")
        return 1
    print(f"no answer-key leaks in {len(files)} tracked files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
