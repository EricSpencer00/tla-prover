# prove-TLA — week of 2026-07-13

What actually happened this week, with numbers.

## Gate 2 measured, failed honestly, and closed the fine-tuning question (Amendments 16-17)

v2_sft2/120b vs frozen baseline (keep-first dedup, ledger re-score): A 11/30 vs 12/30,
B 18/23 vs 21/23, B pass@1 10/23 vs 12/23 -> FAILED. The 20b directional on a
task-shape-corrected corpus (558 verified minimal-diff repair triples, W2.6 harvest)
went +1 pass@1 / -8 pass@4 -> diversity collapse reproduced with the shape confound
removed. Fine-tuning SHELVED; the flywheel is loop-only; corpus SOURCE (self-family
rejection sampling) identified as the binding constraint.

## Structural levers measured null (Amendments 18-19)

- W2.7 prompt scaffolding on 70 hard seeds: control 4/70, scaffold 4/70 (sany_fail 59%).
- W3.1-3.3 built: lmgpa 119-thm TLAPS bench (honest floor 0/119), retrieval index over
  5,047 proved obligations, skeleton-first proof loop.
- W3.2 proof generation: 0/20 unguided AND 0/20 grammar-guided (validated grammars:
  spec 100% acceptance on 260 real specs; proof 99% on 255 real proof blocks) -- tlapm
  parse deaths just move down a level. Structural ladder exhausted at tiers 1-2.
- Bonus trap found: vLLM 0.22-dev structured_outputs crashes the engine under sustained
  guided load (2 serve jobs); ledgered in the preflight checklist.

## W4: the cross-family measurement (the week's headline)

Same 400-cell scenario lattice (20 domains x 10 mechanisms x 7 properties x 6 twists),
same unchanged gate stack (SANY, non-vacuous TLC, mutation battery, fidelity, decontam):

| arm | survivors | cell yield |
|---|---|---|
| Claude-Opus teacher subagents (16 shards, 4 waves) | **400/400** | 100% |
| gpt-oss-120b serve-based funnel | **50/400** | 12.5% |

Cross-family corpus audit: 0/79,800 near-dup pairs, similarity distribution matches the
organic corpus, property classes balanced, honest caveats ledgered (mutation-gate
Goodharting in wave 1, idiom convergence pressure, specs skew small vs holdout).
Corpus now ~1.27k verified rows (400 cross-family + 50 lattice-self + 260 organic + 558
repair triples). Train decision remains gated (proposed 5k floor, one pre-registered eval).

## Infrastructure that made the week cheap

Toy e2e smoke (~3 min full-pipeline), serve preflight probe (would have caught the ctx-4096
disaster in 10s), `harness gate-check` (ledger-true scoring, run-id lockfile), eval
concurrency (12.2h -> ~2h), ALCF no_proxy + java.io.tmpdir + venv-cluster traps ledgered.
Every failed run this week died in minutes-to-hours, not days.


---

# prove-TLA — week of 2026-07-06

What actually happened this week, with numbers.

## Gate 1: repair sweep, both models, all 206 specs

Ran `gpt-oss-120b` and `gpt-oss-20b` as repair arms over the full 206-spec FormaLLM corpus,
to the full frozen budget (best-of-8, ≤24 candidates, 16k tokens), every spec attempted.
Then audited the passes and signed the gate off.

Per-method matrix (from GATE1_STATUS.md, traces to `results/runs/` ledger rows):

| arm | baseline pass | model-repaired | pass@1 | pass@N (model-only) | residue |
|---|---|---|---|---|---|
| gpt-oss-120b | 161 | 5 | 162 | **166** | 40 |
| gpt-oss-20b  | 161 (true) | 3 | — | **157** | 49 |

G1 status line (oracle and model reported separately, per Rule 7):

- Oracle (retrieval, no model): **171/206** at sign-off; **167/206** reproducible right now + a 4-spec unreconciled gap.
- Model-only, best arm (120b), after audit: **166/206**.
- Model-new (oracle-open specs the model actually closed): **5** — specs 66, 81, 85, 141, 194.
- Oracle ∪ model (system closure): **176/206**; reproducible floor **172/206**.
- Remaining gap to 206: **30 specs**, system-open.

The 20b arm closes a strict subset of 120b's repairs (66, 81, 85 — no 141/194) and adds no new
union members. Expected for the smaller sibling.

### The audit is where the number moved

gpt-oss-120b's naive count was **170**. After the semantic audit (Rule 9, `harness semaudit`),
it dropped to **166** — 4 false passes rejected: specs 57, 91, 92, 178. Each of those cleared
SANY, cleared TLC, and cleared the vacuity battery; they only failed once the audit checked
whether the repair preserved the *intended* property. On the 20b arm the audit rejected ~91
candidates (that arm also ran under machine contention — 7 specs false-timed-out at the
120–150s TLC boundary; true baseline is 161, not the raw 154).

Residue by failure class (120b, 40 open): 14 state-explosion, 14 tlc-reject, 7 parse,
4 false-pass-rejected, 1 orphan.

## Stage-2 entry work (E2.a–c)

- **E2.a** — reconciled the 4-spec oracle gap, froze `gate0_closed.json` by hash (SHA `f2288bb…`).
- **E2.b** — froze the 30-spec decontaminated holdout (`holdout_30.json`) before any training run; 23/30 structural on framing B.
- **E2.c** — built the generation+repair eval harness: `gen-eval` CLI, framings A (NL→spec generation) and B (repair-from-standardized-corruption), deterministic `corrupt()` reusing the mutation battery, injected-text scorer. Offline core done.
- **W1.3 withdrawn** — the sibling `chattla-20b` adapter is not faithfully loadable (self-referential `adapter_config.json`, LoRA touched only q/k/v/o so the MoE experts got no gradient — the merge ≈ base + noise). Running it would measure a known-broken artifact, so the Gate-2 bar was re-pointed at the strongest *loadable* baseline instead.

Frozen Gate-2 / E2.c budget (set before measurement so pass rates can't be gamed later):
temperature 0.8, max_tokens 16384, TLC verify 120s **serial** (`--jobs 1`), **32 samples** for
pass@32, pass@1 = one temp-0 greedy sample, Rule-9 audit on every counted pass.

## Live smoke test on Sophia/ALCF

1 spec × 4 arms (gpt-oss-20b/120b × framing A/B), real inference endpoint. Confirms the pipeline
runs end to end:

- gpt-oss-120b, framing A: real `pass` on sample 2 (sany pass, tlc pass, vacuity clean).
- gpt-oss-120b, framing B: `pass` on greedy + samples 1–2 — the seeded `/\`→`\/` mutation corrupts, model repairs it back.
- gpt-oss-20b, framing B: greedy corrupts as expected; samples 1–2 repaired to `pass`.
- gpt-oss-20b, framing A: all `fail:sany=fail` — that arm mostly can't produce a parseable module under generation framing.

Only the gpt-oss family stays reliably hot on the endpoint; the intended larger arms
(Devstral-123B, Llama-405B/70B) are endpoint-blocked (cold/408/503, quarantined in the ledger).

## Why anyone else should care

Same corpus, a different group already published a number: `chattla-20b`, **9/30 (30%) Gold** on a
held-out suite. That number doesn't survive a look at how it was produced — the adapter is
self-referential, the LoRA never trained the MoE experts, and its training corpus included all 205
benchmark specs it was later scored on. None of that shows up in the benchmark table.

The reason our model-only number is 166 and not 170 is the same reason theirs looks like 30% and
isn't: a spec can pass SANY, pass TLC, and pass a vacuity check while the "repair" quietly deleted
or weakened the property. If you don't audit for that, you're counting the model finding a way to
make the checker stop complaining. So the thing worth reusing here isn't a bigger score — it's the
harness that tells you when a pass is real, and the discipline of freezing the holdout and the
budget *before* measuring so the number can't drift to fit the result.

## Not done yet

No Stage-2 baseline number exists. The harness is smoke-tested, not swept. Next is the frozen
baseline: both models × 30-spec holdout × framings A and B × pass@1 and pass@32, semantic-audited,
written to `corpus/e2c_baseline.json` and a PLAN amendment before any training run. That's the
number a retrain has to beat. Nothing counts until it's run.
