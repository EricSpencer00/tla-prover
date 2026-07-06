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

## Status (2026-07-05)

| Stage | Result |
|---|---|
| **Gate 0** — harness + oracle | ✅ signed off. `corpus/gate0_closed.json` freezes **170/206** closed (hash-pinned). |
| **Gate 1** — Stage-1 repair sweep | ✅ signed off. oracle 171 / model-only **166/206** (audited) / oracle∪model **176/206**. See [GATE1_STATUS.md](GATE1_STATUS.md). |
| **Stage 2 entry (E2.a–c)** | E2.a oracle reconciliation ✅, E2.b 30-spec holdout frozen ✅ (`corpus/holdout_30.json`), E2.c baseline measurement **in progress** (see [E2C_HANDOFF.md](E2C_HANDOFF.md)) |
| **Stage 3** — TLAPS prover (G2) | design-sound, scaffolded, zero measured — correctly gated behind Stage 2. |

Models tried: only the `gpt-oss` family stays reliably available on the ALCF/Sophia
inference endpoint used for this work; larger independent arms (Devstral, Llama,
Mixtral) are endpoint-blocked, not ruled out.

## Results so far

| Metric | N | Value | Notes |
|---|---|---|---|
| Oracle closure (G1, hand-verified) | 206 | **170/206 (83%)** | frozen, hash-pinned (`corpus/gate0_closed.json`, SHA `f2288bb…`) |
| Model-only repair, gpt-oss-120b, pre-audit | 206 | 170 naive pass@N | **the naive number, before semantic audit** |
| Model-only repair, gpt-oss-120b, **post-audit** | 206 | **166/206 (81%)** | 4 of the 170 were false passes — property weakened/deleted, not fixed |
| Model-only repair, gpt-oss-20b, pre-audit | 206 | ~154 (contention-inflated) | ~91 additional semantic-audit rejects on this arm alone |
| Oracle ∪ audited model repairs | 206 | **176/206 (85%)**, floor 172 | 5 genuine repairs beyond the oracle: specs 66, 81, 85, 141, 194 |

Full breakdown: [GATE0_STATUS.md](GATE0_STATUS.md), [GATE1_STATUS.md](GATE1_STATUS.md).

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
  inference budget, and reproduction command (`results/runs/`, Rule 8).

## Layout

- `PLAN.md` — the normative plan: goal, rules, staged gates, amendment log.
- `harness/` — verification + eval CLI (`run`, `repair`, `semaudit`, `gate1-report`, `gen-eval`).
- `corpus/` — frozen artifacts (`gate0_closed.json`, `holdout_30.json`), patches, wrappers.
- `results/runs/` — append-only per-run evidence (config, logs, summary).
- `AUDIT.md`, `ROADMAP.md`, `GATE0_STATUS.md`, `GATE1_STATUS.md` — informational status/history.

## Quickstart

```bash
python3 -m harness run --run-id <id> --specs <list> --stages sany,tlc,tlaps
python3 -m harness repair --model openai:<id> --run-id <id>
python3 -m harness semaudit --run-id <id>
python3 -m harness gen-eval --framing {A,B} --model openai:<id> --run-id <id> --k 32
```

## What's next

Finish E2.c (frozen baseline: `gpt-oss-20b` / `gpt-oss-120b` on the 30-spec holdout,
generation + repair framings, pass@1 and pass@32, semantic-audited) — the number
Stage 2 training must beat before any retraining run starts.
