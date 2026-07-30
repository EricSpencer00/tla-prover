# Row-level re-analysis of the framing-A Gate-2 arms (2026-07-30)

`pass@32` collapses 32 Bernoulli draws per spec into one bit and then sums 30 bits.
That is why the headline swung 11 → 15 → 16 across arms while
[W4DG_GATE2_SESSION_2026-07-29.md](../../docs/W4DG_GATE2_SESSION_2026-07-29.md)
watched spec 30 go 5 → 1 between two runs of the **same model on a byte-identical
prompt**.

Re-scoring the existing `rows.jsonl` ledgers at the row level uses all ~960 samples
per arm instead of 30 bits. No new compute; no new inference; the ledgers are
unmodified.

Comparisons are formed only between specs whose `prompt_sha256` matches, so the
`required_signature` fix (which changed 13/30 framing-A prompts) cannot contaminate
a cross-arm delta. The first pair is a control — the same model on the same prompts,
two different runs — and it must come out null, or nothing below it is trustworthy.

Reproduce:

```bash
python3 tools/rowlevel_power.py
```

Verbatim output:

```
==============================================================================
PER-SAMPLE PASS RATE (framing A, temp-0.8 samples, 95% Wilson CI)
==============================================================================
e2c-baseline-120b-a          66/960  = 0.0688  CI [0.0544,0.0865]   pass@32 12/30
gate2-v2-120b-A              47/963  = 0.0488  CI [0.0369,0.0643]   pass@32 11/30
gate2-w4dg-120b-A           105/960  = 0.1094  CI [0.0912,0.1307]   pass@32 15/30
gate2-w4dg-120b-A3          130/960  = 0.1354  CI [0.1152,0.1585]   pass@32 16/30

==============================================================================
TWO-LEVEL PAIRED BOOTSTRAP (resamples specs AND rows within spec)
==============================================================================
comparison                           n     delta                95% CI       p
------------------------------------------------------------------------------
CONTROL same model/prompts          17   +0.0184 [-0.0460,+0.0864]  0.6189
v2 SFT vs untuned base              30   -0.0198 [-0.0583,+0.0135]  0.2586
W4-diamond-gold vs untuned base     30   +0.0406 [-0.0021,+0.0854]  0.0641
W4-diamond-gold vs v2 SFT           30   +0.0604 [+0.0208,+0.1031]  0.0019 *

==============================================================================
VARIANCE DECOMPOSITION — W4-diamond-gold vs untuned base
==============================================================================
spec-level heterogeneity  sd = 0.0189   72.6%  fixed by holdout size, NOT by more runs
within-spec binomial      sd = 0.0116   27.4%  shrinks as 1/R with R replicate runs

Projected 95% CI lower bound (assumes the observed delta is the true one):
  R runs        sd    CI lower   verdict
       1    0.0222     -0.0030   still null
       2    0.0207     +0.0001   SIGNIFICANT
       3    0.0201     +0.0012   SIGNIFICANT
       5    0.0196     +0.0021   SIGNIFICANT
      10    0.0193     +0.0028   SIGNIFICANT
     inf    0.0189     +0.0035   SIGNIFICANT

   specs        sd    CI lower   verdict  (R=1, wider holdout)
      30    0.0222     -0.0030   still null
      45    0.0182     +0.0050   SIGNIFICANT
      60    0.0157     +0.0098   SIGNIFICANT
      90    0.0128     +0.0155   SIGNIFICANT
     120    0.0111     +0.0188   SIGNIFICANT

Caveat: the wider-holdout projection assumes new specs are drawn from
the same difficulty distribution and that the delta holds. Enlarging a
frozen holdout is a goalpost change and needs an amendment + decontam.
```

## What this changes

- **W4-diamond-gold beats the previous corpus outright** — +6.04pp per-sample,
  p=0.0019, on a paired test that reproduces the measured noise floor.
- **Against the untuned base it sits at the edge of significance** — +4.06pp,
  p=0.064, a ~1.6× relative gain in per-sample yield, versus p=0.22 at pass@32.
  "No improvement" was an artifact of the statistic, not a property of the
  fine-tune. This is not a claim that the bar is met; it is a claim that the
  previous measurement could not have detected it either way.
- **v2 SFT is, if anything, negative** (−1.98pp, p=0.26) — consistent with
  Amendment 16 and unchanged by the finer statistic.

## The multi-seed question, answered

72.6% of the remaining uncertainty is **spec-level heterogeneity**, which does not
shrink with replicate runs. R=3 replicates land the CI lower bound at +0.0012 and
the asymptote at +0.0035; widening the holdout to 45 specs reaches +0.0050 at R=1.

**The 30-spec holdout is the binding constraint, not the number of seeds.** Buying
replicate runs buys the smaller 27.4% of the variance. Note that this cuts against
the cheaper option: enlarging a frozen holdout is a goalpost change and needs an
amendment plus a decontamination pass, which is exactly why it has not been done
here.

## Scope

This re-analysis changes the *statistic*, not the *gate*. Gate 2's bar is defined in
PLAN.md in terms of the pre-registered protocol; nothing here amends it, and the
pass@32 numbers in the ledger stand as recorded.
