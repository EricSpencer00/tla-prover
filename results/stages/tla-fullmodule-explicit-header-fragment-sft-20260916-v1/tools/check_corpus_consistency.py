#!/usr/bin/env python3
"""Assert the SFT export and the wave audit still agree about the corpus.

Run from repo root (fast, no network, no model):

    python3 tools/check_corpus_consistency.py

Exit 0 = the export and the audit agree. Exit 1 = they have drifted.

WHY THIS EXISTS
---------------
This drift has now happened twice, in two different layers:

1. COUNT layer (fixed by tools/w4_audit.py's delegation to harness.w4_corpus):
   the export globbed shard dirs lexically and ignored the exclusions ledger,
   emitting 3,965 rows against the audit's 4,040 -- wrong exclusions, wrong
   duplicate winners, and 84 rows silently dropped.

2. SCHEMA layer: build_sft_file graded rows only when --min-tier was passed, so
   the documented harvest command (which passes none) emitted rows with no "arm"
   field. The count was right, so the count check could not see it.

Both were silent. Neither changed an exit code. A pooled eval number computed
from an untagged corpus would have looked completely normal, which is precisely
where a liveness regression hides -- and the liveness arm is the thin one.

So this checks BOTH: the row set AND the fields the eval stratifies on. It is
deliberately paranoid about "arm", because Amendment 17's re-entry condition
requires the pre-registered train+eval to report the two arms separately, and
that report is only possible if every row is attributable to an arm.
"""
from __future__ import annotations

import json
import sys
import tempfile
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from harness import w4_corpus  # noqa: E402
from harness.corpus_prep import build_sft_file  # noqa: E402

SHARD_GLOB = "results/runs/w4-opus-shard*"

#: Fields every rendered row must carry, non-empty. "arm" and "tier_name" are
#: the stratification keys; "text" and "seed_key" make a row trainable and
#: traceable back to its ledger entry.
REQUIRED_FIELDS = ("text", "seed_key", "family", "arm", "tier_name")

VALID_ARMS = {"safety", "liveness"}


def audit_truth() -> list[dict]:
    """The audit's view of the corpus, via the same library the audit uses."""
    rows = w4_corpus.load_effective()
    return w4_corpus.grade_corpus(rows)


def render(out_path: Path, **kwargs) -> list[dict]:
    build_sft_file([SHARD_GLOB], out_path, **kwargs)
    return [json.loads(l) for l in out_path.read_text().splitlines() if l.strip()]


def main() -> int:
    if not list(Path().glob(SHARD_GLOB)):
        print(f"FAIL: no shard dirs match {SHARD_GLOB} (run from the repo root)")
        return 1

    truth = audit_truth()
    problems: list[str] = []

    with tempfile.TemporaryDirectory() as td:
        plain = Path(td) / "sft.jsonl"
        floored = Path(td) / "sft_min0.jsonl"
        rendered = render(plain, fmt="harmony")
        render(floored, fmt="harmony", min_tier=0)

        # 1. Same number of rows.
        if len(rendered) != len(truth):
            problems.append(
                f"row count drift: export {len(rendered)} vs audit {len(truth)}"
            )

        # 2. Same rows, identified by seed_key -- catches a count-preserving swap
        #    (wrong duplicate winner) that a bare count check would miss.
        t_keys = Counter(r.get("seed_key") for r in truth)
        r_keys = Counter(r.get("seed_key") for r in rendered)
        if t_keys != r_keys:
            only_audit = sorted((t_keys - r_keys).elements())[:5]
            only_export = sorted((r_keys - t_keys).elements())[:5]
            problems.append(
                f"seed_key set drift: {len(list((t_keys - r_keys).elements()))} "
                f"audit-only (e.g. {only_audit}), "
                f"{len(list((r_keys - t_keys).elements()))} export-only "
                f"(e.g. {only_export})"
            )

        # 3. Every row carries every stratification field, non-empty.
        for field in REQUIRED_FIELDS:
            missing = [r.get("seed_key") for r in rendered if not r.get(field)]
            if missing:
                problems.append(
                    f"{len(missing)} row(s) missing/empty {field!r} "
                    f"(e.g. {missing[:3]})"
                )

        bad_arms = {r.get("arm") for r in rendered} - VALID_ARMS
        if bad_arms:
            problems.append(f"unexpected arm value(s): {sorted(bad_arms)}")

        # 4. Arm and tier histograms match the audit exactly. This is the check
        #    that makes a two-arm eval report trustworthy.
        for field in ("arm", "tier_name"):
            t_hist = Counter(r.get(field) for r in truth)
            r_hist = Counter(r.get(field) for r in rendered)
            if t_hist != r_hist:
                problems.append(
                    f"{field} histogram drift: export {dict(r_hist)} "
                    f"vs audit {dict(t_hist)}"
                )

        # 5. --min-tier 0 keeps every tier, so it must be a pure no-op. It was
        #    not: it used to be the only thing that added the arm field.
        if plain.read_text() != floored.read_text():
            problems.append(
                "--min-tier 0 changed the output; it filters nothing and must "
                "be a no-op (a schema difference here is how the missing arm "
                "tag stayed hidden)"
            )

    arms = Counter(r.get("arm") for r in rendered)
    print(f"export {len(rendered)} rows; audit {len(truth)} rows")
    print(f"arms: liveness {arms['liveness']}  safety {arms['safety']}")
    print(f"tiers: {dict(Counter(r.get('tier_name') for r in rendered))}")

    if problems:
        print("\nFAIL: export and audit have drifted")
        for p in problems:
            print(f"  - {p}")
        return 1

    print("\nOK: export and audit agree on rows, arms, and tiers")
    return 0


if __name__ == "__main__":
    sys.exit(main())
