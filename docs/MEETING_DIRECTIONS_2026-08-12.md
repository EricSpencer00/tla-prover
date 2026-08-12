# Meeting directions, checked against measured evidence

Source: fine-tuning strategy call (Eric, Mohammed, Arsalan), 2026-08-12. Each
direction is scored against ledgers and committed designs, not opinion.

## 1. Multi-binary / staircase reward — ADOPT; already designed and gated

Mohammed's critique of the binary reward is the same conclusion the ledger
resampling reached independently: the historical GRPO runs starved because 89.5% of
draws landed in one bucket. The staircase design is pre-registered at
`docs/designs/2026-08-12-sany-tlc-grpo.md` with the go/no-go measured offline:
untuned base + binary = 73.7% zero-variance groups at G=8 (inside the historical
failure band), W4DG + 4-tier staircase = 22.8%. `tools/group_variance.py`
recomputes the table against any ledger. One refinement over the meeting's
"score individual features": the tiers must stay ordered (a staircase), not
independent binaries — independent feature scores can be gamed additively; an
ordered staircase cannot reward syntax without parse.

## 2. Verifier-in-the-loop with error feedback — ADOPT; this is framing B + the north star

"10 generations with error feedback to change its mind" is the existing repair
loop: framing B measures exactly repair-under-verifier-feedback, and the locked
north star is correctness via the loop, not the weights. The measured caution the
meeting should absorb: every fine-tune so far has DEGRADED repair performance
(baseline 59.7% per-sample vs 26.5%/20.9% for tuned arms). The mech arm
(Amendment 24, eval in flight) is the first corpus built to train that capability
in the eval's own prompt shape. Online RL on repair is then the staircase design's
natural second arm — same reward, framing-B prompts.

## 3. Planner→generator two-step pipeline — TEST CHEAPLY FIRST; the premise is unsupported

The meeting's diagnosis ("models learn syntax but fail on reasoning") is backwards
against Gate-2 data: 69–90% of failed draws do not parse (syntax/mechanics), and
genuine semantic failures — the system modeled wrong — are 2.1–4.2%. The failure
mass is mechanics, not reasoning. A second model that plans better does not fix a
generator that cannot emit a parsing module.

Two caveats keep this direction alive rather than rejected: (a) gpt-oss already
emits reasoning tokens in its analysis channel — a zero-cost probe is to measure
whether pass rate correlates with analysis-channel plan quality on existing
candidates before building anything; (b) if grammar-constrained decoding removes
the parse mass, the residual failure profile could become reasoning-dominated, at
which point this pipeline is the right next lever. Sequence it behind the parse
fix, not in front.

## 4. EXTENDS in prompts — TRUE BUT SMALL; fix is one line, sized ~12% of SANY mass

Verified both halves (agent audit, 2026-08-12): the claim is factually correct —
neither the framing-A eval prompt nor any SFT prompt states which standard modules
to EXTEND (the only exception is the rare builtin-override branch). But sampling
100 sany-fail rows from the best arm's ledger: 12/100 are stdlib
unknown-operator errors (Cardinality, Seq, Len) plausibly EXTENDS-attributable;
56/100 are unrelated parse errors; 32/100 are model-invented identifiers. So the
fix is real but caps at roughly one-tenth of SANY failures. Cheap to do: emit the
reference spec's EXTENDS line into `required_signature` output. It is a prompt
change, so under the standing rule it needs explicit sign-off and re-baselines
framing A (13 of 30 prompts changed last time cost cross-run comparability).

## 5. "Use the Gold dataset" / TLA Bench — ALIGNED, with one correction

The corpus already tiers on verification strength (diamond = mutation-gated, gold,
graded), and the best arm trained on exactly diamond+gold. The correction worth
making at the next sync: the numbers anchoring the meeting (80% SANY / 30% TLC)
are not from the current harness — 80% SANY matches the old 20-problem rl_loop
suite (n=20, mutable model tag, March), and 30% TLC is the published 9/30 that is
4-shot-with-feedback, holdout-contaminated, and checkpoint-unverified. Current
frozen-holdout numbers are SANY 30.9%, TLC-criterion 9.6%, per-sample 13.6% (best
arm). Decisions calibrated to 80/30 are calibrated to measurements this program
has retracted.

## 6. "Bigger model beat fine-tuning smaller" — HALF-RIGHT

20b→120b helped, but the controlled comparison inside 120b shows corpus provenance
was the decisive variable: same base, same LoRA geometry (536.8M trainable in every
arm), corpora differing → 5.1% vs 13.6% per-sample. Scale is necessary context,
not the lever.

## Order of operations implied by the evidence

1. Mech arm eval (running) — decides the RL start checkpoint.
2. Grammar-constrained decoding probe (env-var only, no training) — attacks the
   69–90% parse mass directly; also cheapest test of whether the residual profile
   becomes reasoning-dominated (which would justify direction 3).
3. Staircase GRPO per the pre-registered design (direction 1), recomputing group
   variance against whichever checkpoint won.
4. EXTENDS prompt fix bundled with the next pre-registered prompt change, not
   shipped ad hoc (direction 4).
5. Planner→generator only if the post-grammar failure profile shows reasoning as
   the new mass (direction 3).
