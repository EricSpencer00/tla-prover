# Sibling-corpus-spec wrapper pattern

A recurring class in the `tlc=error` bucket: the original `.cfg` file substitutes a
constant with an identifier (`Nat <- NatOverride`, `Jug <- MCJug`, `Quorum <-
MCQuorum`, ...) or requires a constant the base module's own file doesn't define at
all — but the identifier IS defined, in a *different* corpus spec that is the actual
MC-wrapper module (`EXTENDS <base module>`). Both the base spec and its wrapper exist
as independent numbered entries in the 206-spec corpus; the original `.cfg` was
clearly written for the wrapper, not the base module it got filed under.

Extended `harness/runner.py`'s wrapper mechanism (`corpus/configs/policy.json`) with a
second form: `{"wrapper": {"corpus_spec": "13"}}` resolves spec 13's own module +
transitive corpus-local deps dynamically at run time (via `num2mod`/`mod2path`,
respecting `corpus/configs/patches/` like any other local dep) — no vendored copy to
go stale, unlike the `{"module":..., "file":...}` form used for genuinely external
(tla-examples) wrappers.

## Resolved this pass

| base spec | wrapper spec | result |
|---|---|---|
| 11 (Bakery) | 13 (MCBakery) | **closed** — clean pass |
| 54 (Echo) | 55 (MCEcho) | **closed** — clean pass |
| 111 (LamportMutex) | 113 (MCLamportMutex) | **closed** — clean pass |
| 136 (ParReach) | 133 (MCParReach) | **closed** — clean pass |
| 141 (Reachable) | 135 (MCReachable) | **closed** — clean pass |
| 158 (Voting) | 156 (MCVoting) | **closed** — clean pass |
| 164 (Voting, duplicate of 158) | 162 (MCVoting, duplicate of 156) | **closed** — clean pass |
| 185 (tcp) | 184 (MCtcp) | **closed** — clean pass |
| 43 (DieHarder) | 44 (MCDieHarder) | **closed** via Amendment 3's `expected_violation` (NotSolved) — see PATCHES.md-adjacent notes in populations.json |
| 12 (Boulanger) | 14 (MCBoulanger) | wired, but 14 times out (large state space) — same disposition as other timeouts |
| 35 (CheckpointCoordination) | 36 (MCCheckpointCoordination) | wired, but 36 times out |
| 47 (DiskSynod) | reuses spec 48's vendored `MC_HDiskSynod.tla` wrapper (HDiskSynod EXTENDS DiskSynod, so the same wrapper transitively covers both) + spec 48's override cfg copied to `corpus/configs/overrides/47.cfg` | wired, times out — same large state space as spec 48, no longer a hard parse/config error |

Fixing spec 47 required a second change: the vendored-file wrapper form
(`{"module":..., "file":...}`) previously only wrote the wrapper file itself into the
workdir, assuming the checked spec's own `local_deps()` already covered everything the
wrapper needs. That held for spec 48 (its own module IS `HDiskSynod`, one `EXTENDS`
away from `DiskSynod`+`Synod`) but not spec 47 (its own module is `DiskSynod`, one
level *below* `HDiskSynod` — `MC_HDiskSynod`'s `EXTENDS HDiskSynod` was never
satisfied). Fixed by copying the vendored wrapper's own transitive `local_deps()` too,
the same way the `corpus_spec` form already did.

## Not resolved — needs an experimental TLC feature

**88 (CRDT) and 94 (ReplicatedLog)**, wrapped by 91 (MCCRDT) and 93 (MCReplicatedLog)
respectively: both wrapper modules carry `ASSUME TLCGet("-Dtlc2.tool.impl.Tool.cdot")
= "true"` — a guard for TLC's experimental "action composition" support
(tlaplus/tlaplus#805). Passing `-Dtlc2.tool.impl.Tool.cdot=true` as a JVM flag (added
`jvm_flags` support to `check_tlc()` for this) still leaves
`TLCGet("-Dtlc2.tool.impl.Tool.cdot")` reporting undefined — either this specific
tla2tools.jar build (pinned per `tools/TOOLS.md`) doesn't implement this exact
experimental hook, or it needs a different registration mechanism than a plain JVM
system property. Not root-caused further — genuinely needs either a newer/different
TLC build or deeper investigation of TLC's `TLCGet("-D...")` internals, both out of
scope for a quick per-spec fix. `jvm_flags` plumbing is in place in `harness/runner.py`
and `policy.json` for whenever this gets picked up again.

## Remaining `tlc=error` specs not yet investigated

72, 124, 130, 134, 138, 140, 148, 157, 163, 168, 170, 176, 198, 205, 206, 61 — each
reports "constant parameter X is not assigned a value" or a substitution error not yet
traced to a sibling. Same method applies: find the undefined identifier's real
definition (`grep -rl "IDENT ==" tla_files/`), confirm which corpus spec's module
actually EXTENDS the base module, wire via `corpus_spec`. Not attempted this pass —
time-boxed to what was resolved above.
