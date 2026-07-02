# Ralph Loop Instructions — Apalache informational sweep

You are continuing prove-TLA work, iterating autonomously. Read PLAN.md and
GATE0_STATUS.md first if you have not already this session.

## Why this loop exists, and its hard boundary

PLAN.md §1 (G1, immutable) says the system must produce output that "passes SANY and
non-vacuous TLC" — literally TLC, not "TLC or Apalache." §3 Stage 4 (W4.1) explicitly
slots Apalache in as a *reward provider first, correctness gate second*, layered
**on top of** TLC in the eventual "full ladder" (W4.2: `SANY ∧ TLC ∧ TLAPS ∧
Apalache`) — not as a Stage 0 substitute for TLC. Rule 1 says an amendment that
"substitutes a proxy for the goal is invalid" unless it corrects a measurement error.
Eric confirmed this reading directly: this loop is **informational only**.

**Hard rule: nothing in this loop may change the 157/206 closed count, touch
`corpus/configs/populations.json`, or move anything in/out of
`corpus/DEFERRED.json`.** No new PLAN.md amendment. Findings go in a new
`corpus/configs/APALACHE_FINDINGS.md`, reported *alongside* the existing honest
"still open under TLC" status in `GATE0_STATUS.md`, never replacing it.

## What to do

Target the specs already confirmed genuinely too large for exhaustive TLC (see
`GATE0_STATUS.md`'s "Ralph Loop conclusion" section): **1, 16, 17, 28, 30, 40, 48, 49,
57, 73, 79, 89, 92, 146**. (Not 107/KnuthYao — its blocker is TLC simulation mode +
an R runtime, unrelated to state-space size, Apalache doesn't apply.)

For each spec:

1. Copy the corpus `.tla` (and any corpus-local deps, same `local_deps()` logic the
   harness already uses) to a scratch dir, add Apalache type annotations.
2. Run `apalache-mc check --length=N --inv=<name> --config=<cfg>` for a reasonable
   bounded depth (start around `--length=10`, raise if it completes quickly and you
   want more confidence; Apalache is symbolic/SMT-based, not explicit-state, so it
   can behave very differently than TLC on the same spec — do not assume TLC's
   observed growth rate predicts Apalache's runtime).
3. Record the result — `NoError` (no counterexample up to that depth), a genuine
   counterexample found, a timeout, or a tool/annotation error you couldn't resolve —
   in `corpus/configs/APALACHE_FINDINGS.md` with the exact command, depth, and
   runtime. Every finding must say **"bounded to depth N"**, never "verified" or
   "proved" unqualified — that overstates what a bounded symbolic check means.

## Type-annotation lessons already learned (proof-of-concept on spec 1)

- Annotation syntax is a `\* @type: ...;` **line comment directly preceding each
  variable/constant name inside the `VARIABLES`/`CONSTANTS` list**, not before the
  keyword and not a block `(* *)` comment — see `tools/smoke/Counter.tla` for the
  canonical example. Getting the placement wrong produces a confusing "Expected a
  type annotation for VARIABLE x" error that looks like the annotation is missing
  even when one exists nearby but misplaced.
- Both `VARIABLES` **and** `CONSTANTS` need annotations.
- **Apalache type-checks the whole file, including operators never referenced by
  your target `INIT`/`NEXT`/`INVARIANT`.** A spec with multiple alternate
  `Init`/`Init0`/`Init1`-style definitions (common in this corpus) will fail type
  checking on the ones you're not even using, unless those are also
  well-typed. You may need to comment out or annotate-through unused alternates
  rather than just the ones on your direct call path.
- Common TLA+-to-Apalache type mappings seen so far: `Nat`/counters → `Int`;
  `[Proc -> Nat]` (function) → `Int -> Int`; `[Proc -> {"a","b"}]` (string-valued
  function) → `Int -> Str`. Sets of records, tuples, and model values need their own
  more complex annotations — consult Apalache's type-annotation docs
  (`tools/apalache-0.58.2`'s bundled docs, or the smoke test) rather than guessing.

## Hard constraints — do not violate any of these

1. **Never claim a spec is "closed," "verified," or "passing Gate 0" based on an
   Apalache result.** Bounded symbolic non-error is real evidence, not exhaustive
   proof — say exactly that, every time.
2. Never touch `corpus/configs/populations.json`, `corpus/DEFERRED.json`, or the
   closed/open counts in `GATE0_STATUS.md`'s "Corpus closure" table.
3. Never edit PLAN.md except to log a new row in §6 if you find something that
   genuinely warrants a goal-seeking amendment proposal (unlikely for this loop,
   given the boundary above) — mark it PENDING Eric, never self-approve.
4. If a spec's Apalache run finds a genuine counterexample (like spec 30's known
   Agreement violation), that's a valuable confirmation — record it clearly, note
   whether it matches an already-known TLC finding or is new.
5. Commit each spec's finding as you go (small, verifiable increments, same
   discipline as the rest of this session) — don't batch everything into one giant
   commit at the end.
6. Do not spend more than ~20-30 minutes of wall-clock per spec on annotation
   debugging. If a spec's types are too complex to annotate cleanly in that time
   (e.g. genuinely intricate record/tuple structures), record it as "not attempted,
   annotation complexity" and move to the next spec rather than spinning.

## Completion

Only output the completion promise `APALACHESWEEP_DONE` when all 14 target specs
have an entry in `corpus/configs/APALACHE_FINDINGS.md` (result, or a documented
reason it wasn't attempted) — not before. Running out of iterations with partial
coverage honestly documented is fine; claiming completeness that isn't there is not.
