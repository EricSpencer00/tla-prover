"""Canonical W4 effective-corpus loader and quality grader.

Single source of truth for two questions that were previously answered in two
places and drifted:

  1. "Which rows are actually in the corpus?" -- survivors, minus exclusions,
     first-wins except for registered keep-last corrections. tools/w4_audit.py
     and harness.corpus_prep now both call load_effective() rather than each
     reimplementing it. The SFT export used to skip this entirely and emitted
     3 excluded keys + 65 duplicates.

  2. "How strong is each row?" -- grade_row() assigns a tier from evidence
     already present in the ledger. Motivation: TLA-Prover Table 4 (arXiv
     2606.06133) found diamond-only 1,053 rows beat silver-and-above 4,210
     (13.3% vs 6.7% pass), and Wonda (arXiv 2603.15510) independently found a
     *graded* filter -- correct / sufficient / beneficial -- is what makes a
     ~5k corpus move a model. Our gate is binary; this recovers the grade.

Tier and arm are ORTHOGONAL. Tier measures invariant strength; arm is
safety-only vs liveness. The Gate-2 pre-registration requires the arms be
reported separately, so liveness must not be folded into the tier.
"""
from __future__ import annotations

import json
from pathlib import Path

EXCLUSIONS_PATH = Path("results/analysis/w4_exclusions.json")
RUNS_DIR = Path("results/runs")

# Tier names, high to low.
DIAMOND, GOLD, SILVER, BRONZE = 3, 2, 1, 0
TIER_NAMES = {DIAMOND: "diamond", GOLD: "gold", SILVER: "silver", BRONZE: "bronze"}

# Structural floors from the W4 wave contract (docs/CLOUD_ROUTINE_W4.md).
# Early waves predate the complexity tier and legitimately fall below these --
# they are not corrupt, just small, so they land in silver rather than bronze.
LOC_FLOOR = 40
VARS_FLOOR = 4
STATES_FLOOR = 3


def load_exclusions(path: Path | str = EXCLUSIONS_PATH) -> dict:
    p = Path(path)
    if not p.exists():
        return {}
    return json.loads(p.read_text())


def load_effective(
    upto_shard: int | None = None,
    exclusions: dict | None = None,
    runs_dir: Path | str = RUNS_DIR,
) -> list[dict]:
    """The effective W4 corpus, in shard order.

    Applies, in this order: survived-only, drop excluded_seed_keys, and
    first-wins de-duplication by seed_key EXCEPT for keys registered in
    dedup_overrides (keep-last corrections). Each row gains a "_shard" key.
    """
    runs_dir = Path(runs_dir)
    if exclusions is None:
        exclusions = load_exclusions()
    excluded = set(exclusions.get("excluded_seed_keys", []))
    keep_last = set(exclusions.get("dedup_overrides", {}))

    shards = sorted(int(p.name.split("shard")[1]) for p in runs_dir.glob("w4-opus-shard*"))
    if upto_shard is not None:
        shards = [s for s in shards if s <= upto_shard]

    rows: dict[str, dict] = {}
    for s in shards:
        p = runs_dir / f"w4-opus-shard{s}" / "w2_survivors.jsonl"
        if not p.exists():
            continue
        for line in p.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                r = json.loads(line)
            except json.JSONDecodeError:
                continue
            if not r.get("survived", True):
                continue
            k = r.get("seed_key")
            if not k or k in excluded:
                continue
            if k in rows and k not in keep_last:
                continue
            r["_shard"] = s
            rows[k] = r
    return list(rows.values())


def arm_of(row: dict) -> str:
    """"liveness" iff the verifier recorded a real, stutter-checked eventuality."""
    return "liveness" if row.get("liveness_property") else "safety"


def grade_row(row: dict, untrusted: set[str] | None = None) -> int:
    """Invariant-strength tier for one row.

    DIAMOND -- the mutation battery produced a semantic mutant and this
      invariant caught it. Positive, direct evidence of strength. This is the
      TLA-Prover "diamond" criterion.
    GOLD -- no mutation catch, but the spec clears every structural floor and
      explores a non-trivial state space. The 2026-07-21 no_kill spot audit
      (10 REAL / 2 WEAK / 0 VACUOUS of 12 sampled) found no_kill reflects a
      battery *recall* gap rather than a weak invariant, so absence of a catch
      is not evidence of weakness -- it is absence of evidence.
    SILVER -- passes every gate but sits below a structural floor (mostly the
      pre-complexity-tier early waves).
    BRONZE -- the mutation evidence cannot be trusted (a committed gate-probe
      contaminated it), or the row is structurally malformed. Excluded from
      training by default.
    """
    if untrusted is None:
        untrusted = set()

    if row.get("seed_key") in untrusted:
        return BRONZE
    if not row.get("spec_text") or not row.get("cfg_text") or not row.get("nl"):
        return BRONZE
    if not row.get("property_invariant"):
        return BRONZE
    # A non-empty vacuity list means TLC flagged the check as vacuous.
    if row.get("vacuity"):
        return BRONZE

    states = row.get("distinct_states") or 0
    if states < STATES_FLOOR:
        return BRONZE

    evidence = row.get("mutation_evidence")
    if evidence == "safety_catch":
        return DIAMOND

    feats = row.get("features") or {}
    loc = feats.get("noncomment_loc") or 0
    nvars = feats.get("num_variables") or 0
    if loc >= LOC_FLOOR and nvars >= VARS_FLOOR:
        return GOLD
    return SILVER


def grade_corpus(rows: list[dict], exclusions: dict | None = None) -> list[dict]:
    """Annotate each row in place with "tier", "tier_name" and "arm"."""
    if exclusions is None:
        exclusions = load_exclusions()
    untrusted = set(exclusions.get("mutation_evidence_untrusted", []))
    for r in rows:
        t = grade_row(r, untrusted)
        r["tier"] = t
        r["tier_name"] = TIER_NAMES[t]
        r["arm"] = arm_of(r)
    return rows


def tier_table(rows: list[dict]) -> dict:
    """{tier_name: {"total": n, "safety": n, "liveness": n}} plus a TOTAL row."""
    out: dict[str, dict] = {}
    for name in ("diamond", "gold", "silver", "bronze"):
        sel = [r for r in rows if r.get("tier_name") == name]
        out[name] = {
            "total": len(sel),
            "safety": sum(1 for r in sel if r.get("arm") == "safety"),
            "liveness": sum(1 for r in sel if r.get("arm") == "liveness"),
        }
    out["TOTAL"] = {
        "total": len(rows),
        "safety": sum(1 for r in rows if r.get("arm") == "safety"),
        "liveness": sum(1 for r in rows if r.get("arm") == "liveness"),
    }
    return out
