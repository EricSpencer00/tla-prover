# W2.1 funnel — chattla-corpora-v2 (run w21-funnel-20260708)

**Corpus identity (Rule 8):** input is a **fresh re-scrape dated 2026-07-08**
(pipeline LUC-FMitF/tla-dataset-pipeline @ `0b21a97a`, commands in config.json),
**NOT** the DVC-frozen 2,624-file `47a14165…` set (remote unreachable; regeneration
ratified by Eric). Raw manifest: `raw_scrape_manifest.jsonl`
(sha256 `10498427a77e1c234b81fba47e50ff72cd57a987f0abc63b2e08428f68242100`).

## Scrape
- 19 repos discovered (11 seeds + 8 search); 2,615 files pulled (1,705 .tla, 910 .cfg, 19MB).
- Known pipeline limits, unmodified: 4/5 seed queries use code-search syntax against the
  repo-search API (0 results); no retry on raw.githubusercontent 429s (a handful of files dropped).

## Funnel (in → out)
| stage | count |
|---|---|
| .tla in | 1,705 |
| exact dup removed (normalized-hash) | 158 |
| contaminated removed (Jaccard ≥ 0.65 vs canonical) | 429 |
| SANY scored | 1,118 |
| SANY discard (99 fail + 70 missing-module) | 169 |
| **tier1_sany_cfg** (SANY pass + sibling .cfg) | **779** |
| **tier2_sany** (SANY pass, no cfg) | **170** |

SANY: `harness.runner.check_sany`, serial, nice 19, 60s timeout.
TLC / vacuity / LLM-judge tier passes (later stages of the PLAN W2.1 chain) are **not yet run**
— this run establishes the decontaminated SANY-gated base; follow-on pass required before any
training-set freeze.

## Decontamination
Method: comment-stripped whitespace-normalized tokens → 5-token blake2b shingles → Jaccard vs
every canonical file; **contaminated iff ≥ 0.65** (errs toward removal). Canonical scope =
**full corpus**: all 206 tla_benchmark specs (205 artifacts; 120 is the orphan) +
tlaplus/examples @ `47b0e2cc` (408 .tla). Full per-canonical detail:
`decontamination_report.json` (380 canonical files had ≥1 near-dup removed).

**Holdout-30 section (Amendment 11 mandatory minimum):** 28/30 holdout specs had near-dups in
the raw scrape — 35 hits, mostly **verbatim tlaplus/Examples copies (Jaccard 1.0)** — all
removed. No hits for specs **105** (top sim 0.014) and **128** (top sim 0.459, Quicksort —
below threshold, flagged for awareness). Per-spec hit lists with scores in
`decontamination_report.json → holdout_section`.

## Outputs
- `data/chattla-corpora-v2/`: tier dirs (gitignored, 8.9MB) + per-tier manifest JSONL (committed)
  with source, module, content sha256, tier, decontam verdict + nearest-canonical similarity.
- Harness code (TDD, suite 67 passed): `harness/corpora.py`, `harness/w21_funnel.py`,
  `harness/test_corpora.py`.

## Reproduce
See `config.json → reproduce`.
