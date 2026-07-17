# Cross-family flywheel (W4 candidate design)

**Status:** DRAFT for Eric's review — implements Amendment 17's re-entry condition.
**Premise:** two measured diversity collapses (Amendments 16, 17) localize the failure to
the corpus SOURCE: rejection-sampling a model's own outputs and SFT'ing on the survivors
contracts the sampling distribution (pass@1 +1, pass@4 17→9 both rounds). Verifiers only
delete; they cannot inject novelty. Therefore the flywheel must have **no self-loop**.

## Design

```
   [seed diversity, external]          [generator ≠ student]         [verifier stack]
   human NL corpora, textbook   →   Claude / GPT / Gemini API   →   SANY
   invariants, perturbation          drafts spec / repair /          non-vacuous TLC
   grammar over gold seeds           proof-sketch                    mutation battery (kill-rate floor)
                                                                     Apalache (symbolic, catches TLC-blind)
                                                                     TLAPS on proof targets
                                                                     diamond pass (below)
                                              ↓ survivors only
                                     train gpt-oss-120b (student)
                                     — student NEVER generates its own training rows
```

## Diamond pass (semantic inversion gate)

Round-trip fidelity, checked by a THIRD family (neither generator nor student):
NL → spec (generator) → NL′ (independent model) → compare NL vs NL′ on the property
anchor. Accept only if the safety property survives the round trip verbatim-or-entailed
(deterministic string/structure check on the SAFETY PROPERTY block — no LLM-judge scoring,
per Eric's hard-metrics rule; the third model only *translates*, never *scores*).

## Why this kills both measured failure modes

- Diversity collapse: training distribution is the generator-family's, filtered — the
  student's modes are not reinforced by construction. The student can only be pulled
  *toward* the teacher's (broader) verified distribution.
- Wholesale-rewrite style drift (Amendment 16 secondary): diff-minimality gate stays at
  corpus time (harness/repair_harvest.py, threshold 0.15) regardless of generator.

## Costs / risks

1. API spend on frontier models for generation (vs free-ish self-sampling). Mitigation:
   the verifier stack is cheap to run locally; sample k small (teacher pass rates are
   high), spend scales with SURVIVORS not attempts.
2. License/ToS: check each provider's synthetic-data-for-training terms before any run.
3. Contamination: teacher may emit memorized public specs — the existing decontam gate
   (Jaccard vs 206-corpus + tlaplus-examples + holdout) already covers this; keep it.
4. The student could still collapse if RL/SFT overtrains on a small corpus — corpus-size
   floor before any train (≥5k rows, family-balanced), else stay loop-only.

## Relationship to the standing system

The production deliverable remains the verified LOOP (Amendment 17); this flywheel is an
efficiency bet on the same terms as before: a 20b directional is DEAD (Eric dropped 20b);
the bar is a 120b eval vs the frozen baseline, run once, pre-registered.

## Open questions for Eric

- Which teacher family/families (Claude via API is natural here; spend cap?)
- Corpus-size floor before the one permitted train run (proposal: 5k verified rows)
- Diamond-pass third family choice (must differ from teacher AND student)
