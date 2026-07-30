# Teaching a machine to close a formal-methods corpus — honestly

A harness + evaluation pipeline that measures, without self-certification, whether an
LLM can produce and repair TLA+ specifications that actually verify.

## The goal ([PLAN.md](PLAN.md), immutable)

- **G1 — Corpus closure.** Produce output that passes SANY and non-vacuous TLC on all
  206 specs in the FormaLLM corpus. No exceptions, no redefinition of "pass."
- **G2 — Prover generalization.** A model that proves TLAPS obligations and passes
  verification on specs it has never seen, measured only on decontaminated
  holdouts — beating published baselines (30% Gold, arXiv:2606.06133; 0/18 proved).

G1 without G2 is a lookup table. G2 without G1 means the harness itself is broken.

## Status (2026-07-30)

| Stage | Result |
|---|---|
| **Gate 0** — harness + oracle | ✅ signed off. `corpus/gate0_closed.json` freezes **170/206** closed (hash-pinned). |
| **Gate 1** — Stage-1 repair sweep | ✅ signed off. oracle 171 / model-only **166/206** (audited) / oracle∪model **176/206**. See [GATE1_STATUS.md](GATE1_STATUS.md). |
| **Stage 2 entry (E2.a–c)** | ✅ complete. Oracle reconciled, 30-spec holdout frozen (`corpus/holdout_30.json`), baseline frozen (`corpus/e2c_baseline.json`). |
| **Gate 2** — beat the frozen baseline | ❌ **measured and failed** on v2_sft2/120b (PLAN Amendment 16): A 11/30 vs 12/30, B 18/23 vs 21/23. Box stays unchecked. |
| **Fine-tuning** | shelved for the v2 corpus (Amendment 17); the W2.6 20b directional reproduced diversity collapse with the task-shape confound removed. Corpus *source* — not method — was the binding constraint. |
| **Structural levers** | measured null (Amendments 18–19): prompt scaffolding 4/70 vs 4/70 control; proof generation 0/20 unguided **and** 0/20 grammar-guided. |
| **W4 cross-family corpus** | ✅ **floors met** (2026-07-27). **5,010 effective rows**, liveness arm **567** — both above the 5,000 / 500 stop floors. `python3 tools/w4_audit.py` is the sole authority. |
| **W4-diamond-gold, trained + measured** | 🟡 framing A **16/30** pass@32 after a prompt-harness fix (15/30 before). Row-level: **+59% per-sample yield over the previous corpus** (p=0.0019), **+4.06pp over the untuned base** (p=0.064). Framing B partial. |
| **Stage 3** — TLAPS prover (G2) | design-sound, scaffolded, honest floor 0/119 on the lmgpa bench — correctly gated behind Stage 2. |

Gate 2 failing on v2_sft2 was a result, not a blocked state: it closed the fine-tuning
question for that corpus and redirected the work to corpus source. That redirection
produced W4, and W4 is the first arm to move the number.

Models tried: only the `gpt-oss` family stays reliably available on the shared
inference endpoint used for this work; larger independent arms (Devstral, Llama,
Mixtral) are endpoint-blocked, not ruled out.

## Results so far

### G1 — corpus closure

| Metric | N | Value | Notes |
|---|---|---|---|
| Oracle closure (G1, hand-verified) | 206 | **170/206 (83%)** | frozen, hash-pinned (`corpus/gate0_closed.json`, SHA `f2288bb…`) |
| Model-only repair, gpt-oss-120b, pre-audit | 206 | 170 naive pass@N | **the naive number, before semantic audit** |
| Model-only repair, gpt-oss-120b, **post-audit** | 206 | **166/206 (81%)** | 4 of the 170 were false passes — property weakened/deleted, not fixed |
| Model-only repair, gpt-oss-20b, pre-audit | 206 | ~154 (contention-inflated) | ~91 additional semantic-audit rejects on this arm alone |
| Oracle ∪ audited model repairs | 206 | **176/206 (85%)**, floor 172 | 5 genuine repairs beyond the oracle: specs 66, 81, 85, 141, 194 |

Full breakdown: [GATE0_STATUS.md](GATE0_STATUS.md), [GATE1_STATUS.md](GATE1_STATUS.md).

### Holdout generation (framing A, 30 frozen specs, k=32)

| Arm | pass@32 | per-sample | vs untuned base |
|---|---|---|---|
| untuned gpt-oss-120b | 12/30 | 66/960 = 6.88% | — |
| v2 SFT | 11/30 | 47/963 = 4.88% | −1.98pp (p=0.26) |
| **W4-diamond-gold** | 15/30 | 105/960 = 10.94% | **+4.06pp (p=0.064)** |
| W4-diamond-gold, post-prompt-fix | **16/30** | 130/960 = 13.54% | not comparable — 13 prompts changed |

Two-level paired bootstrap over specs *and* rows, restricted to byte-identical
`prompt_sha256`, with a same-model/same-prompt control that comes out null (p=0.62)
as it must. W4-diamond-gold beats the v2 corpus outright: **+6.04pp, p=0.0019**.

Analysis and reproduction command:
[results/analysis/rowlevel_reanalysis_2026-07-30.md](results/analysis/rowlevel_reanalysis_2026-07-30.md).

**Read the caveat with the number.** `pass@32` collapses 32 Bernoulli draws into one
bit and sums 30 bits, and it is not a reliable capability signal at this holdout size —
the same model on a byte-identical prompt moved a spec from 5 passes to 1 between two
runs. The row-level statistic recovers the evidence pass@32 throws away. It does not
amend Gate 2's bar, and none of this is a claim that Gate 2 is met.

**The binding constraint is holdout size, not seed count.** 72.6% of the residual
uncertainty is spec-level heterogeneity, which replicate runs cannot shrink. Widening
the holdout to 45 specs would reach significance at R=1 — but enlarging a frozen
holdout is a goalpost change requiring an amendment and a decontamination pass, so it
has not been done.

## Why this should matter to other researchers in this space

This org already has a fine-tuned model with a headline number —
[`chattla-20b`](https://github.com/LUC-AI4FM/TLA-Prove) reports **9/30 (30%) Gold**
on a held-out suite. That number turned out not to hold up under scrutiny: the
adapter is self-referential (its config points at its own merged weights), its
LoRA never touched the MoE experts (so the "fine-tune" is closer to base-model
noise), and its training corpus included all 205 benchmark specs it was later
scored against. None of that is visible from the benchmark table alone — it only
shows up once you go looking for how the number was produced.

That's the gap this repo exists to close. Every number above is:

1. **traceable** — each has a corpus/split, N, verification stage, inference
   budget, and a command that reproduces it (Rule 3/8);
2. **decontamination-aware** — the 206-corpus can score G1 only, never G2, because
   it's known to be in training data; G2 claims require a provably unseen holdout
   (`corpus/holdout_30.json`, frozen before any training run);
3. **audited for meaning, not just syntax** — Rule 9's semantic audit is the reason
   the model-only number *drops* from a naive 170 to an honest 166. A pass/fail
   count that skips this step overstates capability by design, not by accident —
   TLC and the vacuity battery both accepted the 4 rejected repairs.

If you're building on this corpus or comparing against ChatTLA-style results, the
useful thing to take from this repo isn't a bigger number — it's the instrument:
a harness that will tell you when your model found a genuine fix versus when it
found a way to make the checker stop complaining.

## What "honestly" means here

The project runs on a binding rule set (`PLAN.md` §2), enforced in the harness, not
just prose:

- **No self-certification.** Oracle closure is a frozen, hash-pinned positive
  enumeration (`corpus/gate0_closed.json`), never inferred from model behavior.
- **Vacuity checking.** A TLC pass only counts if the harness's mutation/trap battery
  ran on it.
- **Semantic audit (Rule 9).** A model "pass" counts only after `harness semaudit`
  confirms it checks the *intended* property — not a weakened, deleted, or
  substituted one. This caught 4 false passes on the best arm and ~91 on the weaker one.
- **Contamination discipline.** The 206-spec corpus is permanently contaminated
  (used to build chattla-20b) — it can score G1, never G2. G2 numbers come only from
  provably decontaminated holdouts.
- **Append-only ledger.** Every reported number cites its corpus/split, N, stage,
  inference budget, and reproduction command (`results/runs/`, Rule 8). Ledgers are
  never edited in place; re-scoring reads them, it does not rewrite them.

A worked example of the discipline catching itself: while auditing framing-A failures,
`required_signature()` was found to be parsing each cfg `CONSTANT` entry as
`re.split(r"<-|=", body)[0]` — keeping the substitution's *left* identifier and
discarding the *right*. For `Nat <- NatOverride`, the prompt told the model to define
`Nat` and never mentioned `NatOverride` at all, so TLC hard-failed on every attempt.
13 of the 30 holdout specs use `<-`, and 12 of those were among the 15 unsolved. That
bug had been silently corrupting **every framing-A measurement the project has
recorded**, including its own baselines. The fix is worth more than the run that found
it; the write-up is in
[docs/W4DG_GATE2_SESSION_2026-07-29.md](docs/W4DG_GATE2_SESSION_2026-07-29.md).

## Layout

- `PLAN.md` — the normative plan: goal, rules, staged gates, amendment log.
- `harness/` — verification + eval CLI (`run`, `repair`, `semaudit`, `gate1-report`, `gen-eval`).
- `corpus/` — frozen artifacts (`gate0_closed.json`, `holdout_30.json`), patches, wrappers.
- `results/runs/` — append-only per-run evidence (config, logs, summary, rows).
- `results/analysis/` — re-scores and post-hoc analyses over those ledgers.
- `docs/` — design docs, cell rules for the W4 corpus, session write-ups.
- `AUDIT.md`, `ROADMAP.md`, `GATE0_STATUS.md`, `GATE1_STATUS.md` — informational status/history.

## Quickstart

```bash
python3 -m harness run --run-id <id> --specs <list> --stages sany,tlc,tlaps
python3 -m harness repair --model openai:<id> --run-id <id>
python3 -m harness semaudit --run-id <id>
python3 -m harness gen-eval --framing {A,B} --model openai:<id> --run-id <id> --k 32
python3 -m harness gate-check results/runs/<run-id>   # ALWAYS: re-score from rows.jsonl, fail on api_error/extraction defects
```

Inference is reached through any OpenAI-compatible endpoint: set `OPENAI_BASE_URL`,
and either `OPENAI_API_KEY` or `OPENAI_API_KEY_CMD` (a command that prints a
short-lived token). No credentials live in this repository.

### Checks (CI runs these on every push and PR)

```bash
pip install -r requirements-dev.txt
python3 -m pytest harness/ -q                    # harness suite (stdlib-only, no Java, no network)
python3 tools/w4_audit.py                        # corpus accounting + stop floors (exit 10 = floors met)
python3 tools/check_corpus_consistency.py        # the SFT export still agrees with the audit
```

The third one exists because the export and the audit have drifted **twice** — once in
row counts, once in the `arm`/`tier_name` fields the Gate-2 eval stratifies on. Both
were silent and neither changed an exit code, which is precisely how an unstratifiable
corpus reaches a train run. `.github/workflows/ci.yml` references no secrets, so these
work unchanged on forks.

### Toy end-to-end smoke (run before ANY 8-12h experiment)

```bash
tools/smoke/run_e2e.sh
```

Proves every pipeline stage mechanically in ~3 min local wall (first run adds
a one-time venv + SmolLM2-135M download): generation loop with real
SANY/TLC/mutation gates → harmony SFT file → REAL LoRA train + merge (tiny
model) → OpenAI-compatible serve → gen-eval (pass path + resume) →
gate-check, plus a regression that reproduces the 2026-07-14 ctx-4096 serve
bug and asserts gate-check rejects the run. Design:
[docs/designs/2026-07-14-toy-e2e-smoke.md](docs/designs/2026-07-14-toy-e2e-smoke.md).

Before launching any gen-eval against a live serve endpoint, also run the
10-second worst-case-request probe:

```bash
OPENAI_BASE_URL=http://localhost:8322/v1 python3 tools/smoke/serve_preflight.py --model chattla-v2-120b
```

## What's next

The W4 floors are met and the first W4-trained arm is measured. Open, in order:

1. **Finish framing B on W4-diamond-gold** — the arm resumes from row 110 and needs a
   serve. Framing B is the contrast that matters: specs 13 and 14 score 0/33 in
   framing A both before and after the prompt fix, but 29/33 and 9/11 in framing B,
   where the input already contains the substituted operator. Same weights, same specs.
2. **Ledger the framing-A prompt change as an amendment** — framing-A prompts changed
   for 13 of 30 specs, so pass@32 is not comparable across the fix for those. The
   post-fix run is a new baseline, and saying so in the amendment log is not optional.
3. **Decide spec 121's disposition.** Its cfg is `Nat <- [ZSequences]CharacterSet`, a
   module-qualified substitution, and framing A asks for one self-contained module —
   so the spec is *structurally unsuited to the framing*, not merely hard. Excluding it
   from a frozen holdout is a goalpost decision, flagged rather than acted on.
4. **Fix the LoRA resolver in the training repo** — architecture-aware MoE-vs-dense
   resolution plus a trainable-parameter floor that *aborts*. Until that lands, the
   base-model choice is not a free decision: a gpt-oss-hardcoded selector silently
   froze a dense model's entire FFN at 0.0195% trainable, which is why the apparent
   Qwen-beats-gpt-oss result is
   [retracted](results/analysis/base_model_comparison_2026-07-26.md).
5. **Settle the power question before spending more compute.** Replicate runs buy the
   smaller 27.4% of the variance; the holdout buys the rest. Whichever way that goes,
   it is an amendment, not a session-level call.

Known limitations, disclosed rather than fixed: family skew (`mutex_locks` 35.7% vs
`replication_storage` 0.9% — the lattice cell→family map is deterministic, so a hard
gate would be unsatisfiable), real mutation-catch rate 12.8%, specs skewing small
relative to the holdout, wave-1 mutation-gate Goodharting, and idiom convergence
pressure from a single teacher family.

One thing deliberately *not* done: adding `NatOverride == 0 .. MaxNat` as a prompt
example would likely flip three specs — it is the canonical answer. That converts the
benchmark from a capability measure into a hint-following measure. Any further prompt
wording change needs explicit sign-off.

## License

MIT — see [LICENSE](LICENSE). Upstream licenses for the TLA+ tools and community
modules vendored under `tools/`, and for the specifications under `corpus/`, are
recorded in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
