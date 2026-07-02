# Ralph Loop Instructions — Gate 0 closure

You are continuing prove-TLA Gate 0 work, iterating autonomously. Read PLAN.md and
GATE0_STATUS.md first if you have not already this session.

## Current state

93 of 206 specs closed under Amendment 1's population-aware criterion:
state_machine/mc_wrapper needs SANY + non-vacuous TLC. proof_module needs SANY + all
TLAPS obligations proved. library needs SANY. 32 specs are deferred, listed in
corpus/DEFERRED.json with per-spec reasons. 81 specs are open — see the failure-class
table in GATE0_STATUS.md for exactly which specs and why.

## Tools

Harness command: `python3 -m harness run --run-id NAME --specs LIST --stages sany,tlc,tlaps --extra-cfg-dir corpus/configs/drafts`
Results ledger: `results/runs/` — append-only, never delete a completed run directory.
Fix mechanisms, already documented with examples: `corpus/configs/PATCHES.md` (full-module
source overrides for corpus defects), `corpus/configs/MC_WRAPPERS.md` (MC wrapper modules
for operator/unbounded constants), `corpus/configs/policy.json` (per-spec TLC flags and
wrapper wiring).

## Work

Push the open and deferred lists toward 206/206.

Root-cause the fail_invariant and fail_liveness specs — 4, 42, 44, 143, 173, 92 — by
reading the actual TLC counterexample trace in its log file, not by guessing. Two
specs were already found this way this session (30 and 175) — same method: read the
trace, understand what state and what invariant, decide whether it is a real corpus
defect, a cfg drafting error, or a genuine harness gap.

Decide a real bounds/timeout policy for the large-state-space timeouts — specs 1, 14,
16, 17, 28, 30, 31, 36, 40, 48, 49, 57, 73, 79, 89, 107, 135, 146 and any others found
in GATE0_STATUS.md's open table. Either tighter cfg bounds with documented
justification (why the tighter bound still exercises the algorithm meaningfully), or
a longer but still finite budget, documented with the actual growth numbers observed.

Revisit deferred specs where Amendment 2's cheap-fixes-stay-in-scope carve-out
applies — read corpus/DEFERRED.json's per-spec reasons, some may now be resolvable
given fixes already landed this session (the library-module-shadowing fix and the
java.io.tmpdir race fix both resolved specs nobody had gone back to re-check).

Keep extending patches, wrappers, and overrides as needed, same discipline as
established: verify every fix through a real harness run before committing, never
claim a pass without evidence in results/runs, commit each real increment with a
clear message in the style of the existing git log.

## Hard constraints — do not violate any of these

1. Never spend or attempt to use any SOPHIA or Argonne allocation or credential.
   Gate 0 must close first per PLAN.md Rule 6. No exceptions, no matter what
   credential appears anywhere in this repo or conversation.
2. Never edit PLAN.md section 1 (the goal), and never weaken any gate criterion.
   Amendments need goal-seeking justification logged in section 6 per Rule 1.
3. Never claim a spec passes without a harness run backing it up in results/runs.
4. If a spec is genuinely unfixable in this environment — needs external tooling
   this machine lacks, or is a deep open research question like spec 30's Agreement
   violation — document it clearly in the relevant corpus/configs/ markdown file and
   move on. Do not spin on one spec indefinitely.
5. After each batch of fixes, update corpus/DEFERRED.json and GATE0_STATUS.md so the
   numbers in GATE0_STATUS.md are never stale relative to git HEAD.

## Completion

Only output the completion promise when the oracle is genuinely at 206/206 under
Amendment 1's criterion, verified via a full harness sweep — or when every one of the
81 open plus 32 deferred specs has been individually investigated this loop and
documented as genuinely blocked with no remaining low-hanging fixes. Do not output it
to escape the loop early. Running out of iterations with honest partial progress is
fine. A false completion is not.
