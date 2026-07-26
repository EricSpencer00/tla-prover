# How to resume the W4 corpus build (written 2026-07-19 at the usage-pause)

State at pause: 1,848 effective cross-family Opus-teacher survivors (33 waves,
shards 0-73 committed; wave 34 = shards 74-75 was dispatched but stopped before
producing output — its cells 1850-1900 are UNUSED and should be re-assigned).
Corpus total ~2.72k verified rows (~54% of the proposed 5k train floor).
Checkpoint commit: 27fff3a. Session-agnostic recipe — any Claude session can
continue with only this file + the repo.

## Per-wave loop (repeat until the floor or a new decision)

1. Generate the next 50 cells (N = first unused lattice position, currently 1850):
   python3 -c "
   from harness.w4_scenarios import lattice, DOMAINS, MECHANISMS, PROPERTIES, TWISTS, cell_key
   N=1850; S=74   # S = first unused shard number, currently 74
   cells = lattice(20260718, N+50)[N:N+50]
   for s in range(2):
       sl = cells[s*25:(s+1)*25]
       with open(f'/tmp/shard{S+s}.txt','w') as f:
           for k, c in enumerate(sl):
               arm = 'LIVENESS' if (N + s*25 + k) % 2 == 0 else 'SAFETY-ONLY'
               f.write(f'  {cell_key(c)} | {arm} | {DOMAINS[c[0]]} | {MECHANISMS[c[1]]} | {PROPERTIES[c[2]]} | {TWISTS[c[3]]}\n')"

2. Dispatch 2 Opus subagents (Agent tool, model=opus, run_in_background), one per
   shard file, with the CURRENT canonical brief. The brief has evolved through 33
   waves of incident response — reuse the latest version verbatim from this
   session's shard-74/75 dispatch (git log context) or reconstruct from these
   REQUIRED clauses, all load-bearing:
   - output dir results/runs/w4-opus-shard<S>; touch nothing else; scratch in /tmp
   - complexity tier HARD floors: 40-90 non-comment LOC, 4-6 vars, >=4 actions,
     <100k states; check floors BEFORE appending
   - anti-self-copy: every cell from scratch; shingle audit quarantines
   - ledger: append-only, one survivor row per cell, FULL cell key in cell/seed_key,
     never edit/strip rows, corrections as new rows flagged keep-last
   - per cell: NL scenario ending "SAFETY PROPERTY: <sentence>"; NL updated
     BEFORE final verify when actions change; module W4O<key-no-dashes>;
     verify via `python3 -m harness.w4_verify_cell --nl .. --spec .. --cfg ..
     --invariant .. --workdir /tmp/...`; max 4 attempts; survivors merged with
     {"cell","seed_key":"w4opus::<full-key>","nl","teacher":"claude-opus","tier":"complex"}
   - LIVENESS/SAFETY SPLIT (Eric 2026-07-23, from shard 129 on): each shard
     file marks every cell LIVENESS or SAFETY-ONLY (deterministic: even
     lattice index = LIVENESS -- never reassign). SAFETY-ONLY cells follow the
     original contract above unchanged. LIVENESS cells additionally end the NL
     with "LIVENESS PROPERTY: <sentence>" and verify with the extra flag
     `--require-liveness`. Rows self-tag: liveness cells carry non-null
     liveness_property + stutter_check fields; corpus rendering and Gate-2
     eval MUST stratify on that (report the two arms separately).
   - LIVENESS cell contract detail: the spec must define
     a real eventuality (<> or ~>) implementing the NL's LIVENESS PROPERTY,
     Spec must include the WF_/SF_ fairness that makes it true, and the .cfg
     must check it with a PROPERTY line. The harness FIX-5 gate re-runs TLC
     with fairness stripped and REJECTS "liveness_stutter_trivial" unless the
     property FAILS there -- so an Init-true or stutter-insensitive eventuality
     cannot pass. Do not game with <>TRUE-shaped properties; write progress
     properties the mechanism actually guarantees (e.g. "every admitted request
     is eventually serviced", "the token eventually returns to the ring").
   - INTEGRITY: no mutation.py access of ANY kind (a violator shard's evidence was
     flagged untrusted); on typeok_only rejections restructure naturally; no
     engineered mutation-catch constructs; no_kill/no_site acceptable
   - DIVERSITY: avoid `Cardinality(S)<=1`, `applied+Len(queue)=admitted`, ghost
     `badActions=0`, bare `count<=1`, pairwise slot-uniqueness,
     counter-vs-cardinality where honest alternatives exist
   - RETURN: survivors/attempted, reject histogram, median LOC+states, 3 hardest
     cells, honesty note

3. AFTER BOTH shards report, run the audit:
   python3 tools/w4_audit.py
   It derives the shard range itself, honors w4_exclusions.json (exclusions +
   keep-last), and prints effective corpus, arm split, family/mutation/cfg drift,
   near-dups, and a STOP=YES/NO line. Exit 10 = every floor met. The floors are
   constants at the top of that file: total >=5000 AND liveness arm >=500. Near-dup
   is incremental (new wave vs everything); `--full` forces the O(n^2) sweep.

   This replaced an inline heredoc whose range end had to be hand-bumped, and whose
   floor (4130) would have stopped the run at ~3% liveness. See
   docs/CLOUD_ROUTINE_W4.md for the full changelog.

4. Handle incidents exactly as the ledgered precedents (results/analysis/
   w4_exclusions.json holds all state): near-dup pair -> add loser to
   excluded_seed_keys; double-append/keep-last disclosure -> add to
   dedup_overrides; agent claims done but ledger short -> SendMessage the agent to
   finish missing cells; mutation-gate engineering disclosure -> add seed_keys to
   mutation_evidence_untrusted + note. Every shard report gets read for honesty
   flags before commit.

5. Commit: `git add results/runs/w4-opus-shard<S> results/runs/w4-opus-shard<S+1>
   results/analysis/w4_exclusions.json && git commit` with the wave count +
   effective total in the message. Update memory round3-status counts.

## When the corpus is deemed big enough (floors enforced by tools/w4_audit.py)
Floors: total >=5000 effective W4 rows AND liveness arm >=500. The liveness floor
exists because the arm only started producing at shard 155 — at shard 161 it was
85 rows (2.1%), and the old 4130 total-only floor would have frozen it near 3%.
Family balance ("family-balanced" in the design doc) is reported but NOT gated:
the lattice cell -> family map is deterministic, so a hard gate could be
unsatisfiable. mutex_locks is 35.8% vs replication_storage 0.9%; treat that as a
known limitation to disclose, not something a wave can fix.

Render + gate per round3-status "AFTER HARVEST" notes: corpus_prep sft over all
w4-opus-shard* dirs (honor w4_exclusions.json exclusions + keep-last overrides
and the shard-50 short-key mapping in commit 81bfb65), then the ONE pre-registered
120b train+eval per Amendment 17's re-entry condition. STRATIFY by arm: rows with
non-null liveness_property are the liveness arm (all shard <=128 rows plus odd-index
cells after are safety-only); the pre-registration must report the two arms
separately -- do not let a liveness regression hide inside a pooled number.

The rendered SFT file carries `arm` and `tier_name` on every row, unconditionally
(this was broken until 2026-07-26: grading ran only under --min-tier, so the command
above emitted untagged rows and the two-arm report was impossible). Guarded by
`tools/check_corpus_consistency.py`, which asserts the export and the audit agree on
rows, arms, and tiers -- run it after rendering; it is also a CI job.

## The three calls: DECIDED 2026-07-26 (PLAN Amendment 20)

Formerly "outstanding: Eric's explicit calls." He delegated them; they are ledgered in
PLAN.md Amendment 20. Summary for the wave loop:

- **(a) Wave rate: FULL RATE.** Continue 50-cell waves to the floors, ~10 waves. The
  TOTAL floor binds (488 to go); liveness clears on the way (~244 of those cells are
  liveness under the deterministic even/odd split), so do NOT re-weight the arms and
  do NOT reassign already-fixed arms.
- **(b) Train run: NOT yet, and no longer pinned to gpt-oss-120b.** The
  pre-registration is now pinned to the corpus + protocol; the base model is chosen
  after `src/training/train.py` (the OTHER repo) gets architecture-aware LoRA
  resolution and a trainable-parameter floor that ABORTS. gpt-oss collapses entropy in
  both measured batch configs, and the Qwen arm that appeared to answer this is
  RETRACTED. Do not launch the reserved run from a wave session.
- **(c) Publish / HF upload: DEFER** until the floors are met AND the eval has run. Do
  not upload a mid-build corpus. Waves continue meanwhile -- this blocks nothing.

## Cost calibration (measured)
~500k Opus subagent tokens per 50-spec wave; ~25-35 min/wave wall; 100% survival
across all 33 waves; audit catches ~1 incident per 2-3 waves (all recoverable).
