# Apalache informational sweep

**Scope reminder: informational only.** Per `RALPH_INSTRUCTIONS_APALACHE.md` (Eric
confirmed directly): PLAN.md §1 (G1, immutable) requires "SANY and non-vacuous TLC"
literally; Apalache is Stage 4 scope (§3, W4.1 — reward provider first, then a gate
layered *on top of* TLC in the full ladder), not a Stage 0 substitute. **Nothing here
changes the 157/206 closed count, `populations.json`, or `DEFERRED.json`.** A
`NoError` result below means "no counterexample found by symbolic search up to depth
N" — bounded evidence, not exhaustive proof. Say so every time, not "verified."

## Method

For each target spec: copy the corpus `.tla` + local deps to a scratch dir, add
Apalache `\* @type: ...;` annotations to every `VARIABLE`/`CONSTANT`, run
`apalache-mc check --length=N --inv=<name> --config=<cfg>`. Corpus files are never
modified — only scratch copies.

## 1 (aba_asyn_byz) — `NoError` up to depth 5

Command: `apalache-mc check --length=5 --inv=TypeOK --config=aba_asyn_byz.cfg aba_asyn_byz.tla`
(N=4, T=1, F=1, same constants as the corpus `.cfg`). Result: `NoError`, 3.3s.
Depth 10 did not complete within 90s — Apalache's SMT solver gets stuck on a specific
`TypeOK` conjunct at deeper symbolic paths (not simply "more states," a specific
verification-condition query scaling badly). This is an Apalache/SMT-scaling
characteristic, not the same failure mode as TLC's explicit-state exhaustion.

Two harmless-to-TLC but Apalache-blocking corpus imperfections found and fixed in the
scratch copy only (not the corpus):
- `Init0`/`Init1` (unused by the target `Init`) write `pc \in [i \in Proc |-> "V0"]`
  — membership-testing a single function value, not a real set — almost certainly a
  typo for `pc = [i \in Proc |-> "V0"]`. TLC never evaluates these since our `Init`
  is used instead; Apalache's whole-file type-checking still fails on them regardless.
- `Decide(i)`'s `UNCHANGED << nSntE, nSntE, nSntR, ... >>` lists `nSntE` twice —
  harmless duplicate for TLC, but trips Apalache's stricter single-assignment
  analysis ("Manual assignment is spurious, nSntE is already assigned!").

Only `TypeOK` attempted (the `PROPERTIES` — `Unforg_Ltl`/`Corr_Ltl`/`Agreement_Ltl` —
are temporal/liveness, which Apalache handles differently and was not attempted this
spec given the time already spent on the type-annotation/assignment-error round trip
above).
