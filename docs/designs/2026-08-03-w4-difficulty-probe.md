# W4 Difficulty Probe — retro-fitting a student-pass-rate axis onto the existing corpus

**Goal:** Measure, for a stratified sample of the 5,010-row W4 export, the probability
`p` that the **untuned base gpt-oss-120b** produces a cell that clears the corpus's own
gate stack in a single attempt. Report the fraction of the trained arm
(`W4-diamond-gold`, 4,219 rows) sitting at `p ≈ 1` — i.e. training mass spent teaching
the student something it already does.

**Why now:** Sancaktar et al. (arXiv:2603.24202, Meta FAIR, Mar 2026) filter synthetic
training problems to `0.01 < p < 0.97` on empirical student pass rate, and drop
"student never solved" outright (Fig. 1). W4 has no difficulty axis at all: `tier` is
`"complex"` on all 4,688 tagged rows, `complexity_score` is a static structural metric
(LOC / variables / actions), and the diamond/gold/silver/bronze tiers grade *mutation
kill-rate*, not difficulty. Amendment 17 concluded the binding constraint was corpus
*source*; W4 fixed source (out-of-family teacher, `claude-opus` on all 5,088 rows) and
moved the number (+59% per-sample). Difficulty targeting was never tested. This probe
tests it **without regenerating a single cell**.

**Non-goal:** This is not a curriculum. The paper's curriculum results are marginal and
schedule-dependent (Fig. 10, Fig. 12), and its "hard = sparse reward" caveat is
GRPO-specific — under SFT, `p = 0` cells are the point of imitation, not a liability.
The only transferable rule being tested here is **drop the `p ≈ 1` mass**.

**Architecture:** One new module (`harness/w4_difficulty.py`) that reuses the existing
one-shot verification path verbatim — the same `run_loop_for_seed(_OneShot(reply), ...)`
call `harness/w4_verify_cell.py` already makes, at `max_iters=1`. Nothing in the scoring
path is new, so the probe's bar is the corpus's own bar by construction. Two stages:
a k=8 triage sweep over 300 cells, then a k=32 confirm over only the cells that
saturate, because k=8 cannot resolve the 0.97 boundary (see Task 4).

**Tech stack:** existing `harness.w2_loop`, `harness.w4_corpus`, `harness.corpus_prep`;
OpenAI-compatible serve via `OPENAI_BASE_URL`; TLC via `tools/tla2tools.jar`.

---

## Global constraints

- **Frozen artifacts untouched.** No writes to `corpus/holdout_30.json`,
  `corpus/gate0_closed.json`, `corpus/e2c_baseline.json`, or any
  `results/runs/w4-opus-shard*/` ledger. Assert `python3 tools/w4_audit.py` reports the
  same row/arm/tier counts before and after the run.
- **Probe samples never enter the corpus.** They are student output, not teacher
  survivors. They land only in `results/runs/w4-difficulty-v1/` and are excluded from
  every `survivor_dirs` glob by living outside the `w4-opus-shard*` pattern.
- **Gate-2's bar is unchanged.** This measures the *training* corpus, not the holdout.
  No PLAN amendment is required to run it. Acting on the result — re-exporting a
  p-filtered corpus — *is* a corpus change and needs a ledger entry (Rule 8).
- **Append-only ledger, re-scored from rows.** `rows.jsonl` is never edited;
  `summary.json` is advisory and is never the source of a reported number.
- **Decontam is skipped** (`skip_decontam=True`). The probe asks "can the student produce
  a passing cell", not "may this row be admitted" — decontam is an admission gate and
  would charge the student for overlap with canonical specs it is allowed to resemble.
  Recorded explicitly in the run config so the deviation is visible.
- Commit each task to `main` as it lands.

---

### Task 1: Freeze the sample

**Files:**
- Create: `harness/w4_difficulty.py` (`select_sample`)
- Create: `harness/test_w4_difficulty.py`
- Artifact: `results/runs/w4-difficulty-v1/sample_frozen.json`

**Interfaces:** `select_sample(export_rows, n=300, seed=20260803) -> list[dict]`, stratified
by `(arm, tier)` with proportional allocation, deterministic under the seed.

Stratify across **all four tiers**, not just the trained diamond+gold. If diamond and
gold come out with the same `p` distribution, the mutation-kill tiering carries no
difficulty information — a free secondary result that decides whether tier and difficulty
need to be separate axes at all.

- [ ] `select_sample`: load the export via the same path `tools/check_corpus_consistency.py`
      uses; proportional-allocate 300 across `arm ∈ {safety, liveness}` × `tier ∈
      {diamond, gold, silver, bronze}`; sort by `seed_key` before sampling for determinism.
- [ ] Write `sample_frozen.json` = `{seed, n, strata_counts, seed_keys[], sha256}`; the
      sha256 covers the sorted `seed_keys` list. Commit it — every downstream number
      cites this hash.
- [ ] Test: same seed → identical `seed_keys`; strata counts sum to `n`; no `seed_key`
      appears in `results/analysis/w4_exclusions.json`.
- [ ] Commit.

**Est: 1 h.**

---

### Task 2: Resolve the prompt question (blocking — a real defect surfaced here)

**Files:**
- Modify: `harness/w4_difficulty.py` (`probe_prompt`)
- Test: `harness/test_w4_difficulty.py`

`p` is only meaningful relative to a prompt, and the corpus currently has **two different
ones**:

| | prompt the model sees | source |
|---|---|---|
| **Corpus generation** | `w2_loop.generation_prompt(nl, module_name)` — names the module, demands one ```` ```tla ```` + one ```` ```cfg ```` block, and requires a trailing `PROPERTY_INVARIANT: <Name>` line | [w2_loop.py:138](harness/w2_loop.py:138) |
| **SFT training pair** | bare `row["nl"]` — no module name, no output contract, no `PROPERTY_INVARIANT` line | [corpus_prep.py:378](harness/corpus_prep.py:378) |

The SFT *target* has the same gap: `_target_block` emits only the two fenced blocks and
drops the `PROPERTY_INVARIANT:` line the generation contract requires
([corpus_prep.py:346](harness/corpus_prep.py:346)). So the trained model is taught to
produce a differently-shaped answer from a differently-shaped question than the one every
survivor was verified under.

Decision: **primary arm uses `generation_prompt`** — it is the contract the targets were
produced and verified under, so `p` measured there is the honest "can the student clear
this cell's own bar". Add a **50-cell secondary arm under the bare-`nl` SFT user text** to
quantify the mismatch as a number rather than an assertion.

- [ ] `probe_prompt(row, mode)` for `mode ∈ {"generation", "sft_user"}`; `"generation"`
      calls `w2_loop.generation_prompt(row["nl"], row["module"])` with no `error_context`.
- [ ] Test: `"generation"` output is byte-identical to what `w2_loop` builds for the same
      row (guards against the prompt drifting out from under a recorded `p`).
- [ ] Record the chosen mode in every ledger row — a `p` without its prompt mode is
      uninterpretable.
- [ ] Commit.

**Est: 1 h.** The corpus-prep mismatch itself is **out of scope for this spec** — flag it,
do not fix it here; changing the SFT rendering invalidates the trained arm's provenance
and needs its own ledger entry.

---

### Task 3: The probe loop

**Files:**
- Modify: `harness/w4_difficulty.py` (`probe_cell`, `run_probe`, `main`)
- Test: `harness/test_w4_difficulty.py` (stub model, no network, no Java)

**Interfaces:**
```bash
python3 -m harness.w4_difficulty \
    --sample results/runs/w4-difficulty-v1/sample_frozen.json \
    --model openai:<id> --k 8 --mode generation \
    --run-id w4-difficulty-v1 --concurrency 8
```
Produces `results/runs/w4-difficulty-v1/rows.jsonl`, one row per `(seed_key, sample_id)`:
`{seed_key, arm, tier, mode, sample_id, temperature, survived, rejection_reason,
kill_rate, prompt_sha256, model, k}`.

- [ ] `probe_cell(model, row, k, mode, workroot)`: draw `k` samples at temperature 0.8
      (matching the eval arms), each verified by
      `run_loop_for_seed(_OneShot(reply), row["nl"], module, wd, max_iters=1,
      require_liveness=(arm == "liveness"), skip_decontam=True)`.
      **`max_iters=1` is load-bearing** — repair iterations would measure the loop, not
      the student.
- [ ] Per-sample isolated workdir under an absolute path (the `java.io.tmpdir` trap and
      the 2026-07-14 TLC states-dir race both bite here); clear between samples.
- [ ] Resume: skip `(seed_key, sample_id)` pairs already in `rows.jsonl`, matching
      `gen_eval`'s `load_existing_rows` pattern.
- [ ] Concurrency via a worker pool sized by `--concurrency`; TLC is the bottleneck, not
      the model. Fail the run on any `api_error` rather than scoring around it.
- [ ] Test with a stub model returning a known-good and a known-bad reply; assert
      `p_hat` comes out 0.5 and that no row is written to any `w4-opus-shard*` path.
- [ ] Commit.

**Est: 3–4 h to write and test.**

---

### Task 4: Two-stage estimation (k=8 cannot see the 0.97 line)

**Files:**
- Create: `tools/w4_difficulty_report.py`

At k=8 the finest resolvable step is 0.125, and a cell scoring 8/8 has a 95% Clopper–Pearson
lower bound of ≈0.63 — k=8 **cannot** distinguish `p = 0.97` from `p = 0.70`. The paper
itself flags M=8 as too noisy and uses M=32. Hence:

1. **Triage (k=8, 300 cells).** Bin into `p_hat = 0`, `0 < p_hat < 1`, `p_hat = 1`.
2. **Confirm (k=32).** Re-run only the `p_hat = 1` cells at k=32. A cell is *saturated*
   only if its k=32 Clopper–Pearson lower bound clears 0.97.

The headline number is the **saturated fraction with a CI**, never a point estimate.

- [ ] `tools/w4_difficulty_report.py` re-scores from `rows.jsonl` only (never
      `summary.json`); emits per-`(arm, tier)` bin counts and Clopper–Pearson intervals.
- [ ] Report the diamond-vs-gold `p` comparison — the secondary result on whether
      kill-rate tiering carries difficulty information.
- [ ] Report the `generation` vs `sft_user` delta from the 50-cell arm.
- [ ] Test on a fixture `rows.jsonl` with hand-computed expected bins.
- [ ] Commit.

**Est: 2 h.**

---

### Task 5: Run it

- [ ] `tools/smoke/run_e2e.sh` — mandatory before any long run.
- [ ] `OPENAI_BASE_URL=... python3 tools/smoke/serve_preflight.py --model <id>` — worst-case
      request probe before touching a live serve.
- [ ] Triage sweep: 300 cells × k=8 = **2,400 generate+verify pairs**. At 8 workers and a
      ~20 s median TLC, **≈2–3 h wall**.
- [ ] Confirm sweep: k=32 on the saturated set. If ~25% of triage saturates, that is
      75 cells × 32 = 2,400 more pairs — another **≈2–3 h**.
- [ ] Secondary: 50 cells × k=8 under `sft_user`. **≈30 min.**
- [ ] `python3 tools/w4_audit.py` after — assert unchanged (5,010 / 567 / 4,443).
- [ ] Ledger the run per Rule 8: corpus/split, N, stage, inference budget, repro command.
- [ ] Commit.

**Est: 6–7 h wall, mostly unattended.**

---

## Decision rule

Stated before the data, so the result can't be read to taste.

| saturated fraction of diamond+gold | reading | action |
|---|---|---|
| **> 30%** | a third of the trained arm teaches nothing the base can't do | re-export p-filtered, retrain, re-measure — the cheapest live hypothesis on the board |
| **10–30%** | real but not dominant waste | fold the p filter into the *next* corpus wave's admission gate; do not retrain on the current one |
| **< 10%** | difficulty targeting is not the constraint here | drop this axis, spend the compute on the multi-environment arm (Fig. 14 ported) instead |

Independently, if diamond and gold show statistically indistinguishable `p`, record that
the mutation-kill tiers carry no difficulty information — the `--min-tier` knob is then
selecting on spec strength alone, which is worth knowing before the next export.

## What this does not decide

Curriculum ordering (weak in the paper, GRPO-specific), the multi-environment arm (the
larger untested lever, specced separately), and the `corpus_prep` prompt/target mismatch
found in Task 2 (flagged, needs its own ledger entry).
