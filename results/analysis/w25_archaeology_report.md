# W2.5 Archaeology Report (2026-07-16 pass)

Builds on `results/runs/w25-archaeology/W25_FINDINGS.md` (2026-07-08, exhaustive prior
session). `corpus/DEFERRED.json` already reflects that session's TERMINAL rulings for
109 and 120 (Eric-approved, applied). This pass re-verified reproducibility (spec 199
re-probed: `results/runs/w25-probe-199`, still `sany=fail`, matches prior) and confirms
no new evidence changes any of the remaining 11 classifications.

| Spec | Deferral reason (short) | Classification | Evidence / next step |
|---|---|---|---|
| 109 | TLCExt missing + POSTCONDITION cfg unsupported + R runtime | **terminal** (applied) | SANY closed via vendored `tools/extra-modules/TLCExt.tla`; TLC blocked on unsupported `POSTCONDITION` cfg keyword (TLC 2.19, Aug-2024 jar) + R-runtime dep, same accepted-residue class as spec 107 |
| 120 | orphan — no `.tla` source anywhere | **terminal** (applied) | Exhaustive search of tlaplus/examples tree + dataverse manifests + web search, zero hits for `KnuthMorrisPratt`; only structured NL description survives |
| 66 | `EXTENDS TLCExt`, spec uses `Trace` op (Java-native) | terminal-leaning / needs-library-scoring | TLCExt.tla source vendored but `Trace` requires compiled `tlc2.module.TLCExt.class`; extracted from newer jar, crashes with ABI-incompatible `StatefulRuntimeException` against pinned TLC engine. Fix path = full tla2tools.jar upgrade (out of W2.5 scope, breaks CommunityModules-deps elsewhere per `harness/runner.py` comment) |
| 75 | same as 66 | terminal-leaning | same ABI-incompatibility, same fix path required |
| 76 | same as 66 | terminal-leaning | same ABI-incompatibility, same fix path required |
| 77 | `EXTENDS TLCExt`, uses only `TLCGet`/`TLCSet` (native) | closable-now (SANY only) / needs-harness-feature (TLC) | SANY closed via vendored stub, verified. TLC needs `-generate` simulation mode + `-DIOEnv.*` passthrough — harness (`harness/runner.py`) has no plumbing for this; real capability gap, not corpus defect. Next step: harness feature work item, separate from archaeology |
| 71 | `ENABLEDrules`/`ENABLEDrewrites` undefined in tlapm 1.6.0-pre | terminal-leaning | Confirmed absent from tlapm stdlib, tla-examples, and `tools/tlapm/lib/tlapm/stdlib/`; no `--help` flag either. Needs different tlapm build — outside corpus/harness scope as currently pinned |
| 83 | same ENABLED gap as 71 | terminal-leaning | same as 71 |
| 24 | `vars` becomes Unknown operator inside nested TLAPS proof steps (VoteProof.tla internal defect) | needs-library-scoring / terminal-leaning | Confirmed not a missing-Consensus dependency (Consensus present, parses fine); genuine proof-structure defect inherited from spec 27 (VoteProof.tla). Needs TLA+ proof-language expertise to fix; not a quick harness/dep fix |
| 26 | same VoteProof defect as 24 | needs-library-scoring / terminal-leaning | same as 24, inherited from spec 27 |
| 27 | root VoteProof.tla defect (`vars`/`LiveSpecEquals` undefined at line 941/1195) | needs-library-scoring / terminal-leaning | Root cause of 24/26's failure; genuine internal scoping/proof-tree defect, not environment-caused |
| 169 | FastPaxos declares wrong CONSTANTS, doesn't match Paxos naming (Acceptor/Ballot vs Replicas/Ballots) | closable-with-effort (not closable-now) | Re-probed not repeated this session (unchanged from 07-08); needs cross-reference against the Fast Paxos paper cited in module header to write correct CONSTANTS block — real authoring work, not a lookup fix |
| 199 | MCTwoPhase wrapper vars/INSTANCE totally disconnected from TwoPhase (spec 196/201) | closable-with-effort (not closable-now) | **Re-verified this session**: `results/runs/w25-probe-199`, `sany=fail`, matches prior finding exactly. Needs a from-scratch MC wrapper per the W0.3 discipline (Amendment 9(b)); no existing wrapper content to repair |

## Closable-now count: 0

None of the 13 are closable via a simple "fetch missing file" step this session — the two
that *were* closable-now that way (109 SANY-side via TLCExt stub, 77 SANY-side same) are
already applied/tracked as such from the prior session; their remaining TLC-side blockers
are harness-capability or tool-version gaps, not missing dependencies. The 2 orphan/
terminal rulings (109, 120) are already applied to `corpus/DEFERRED.json`. The other 11
remain open, each requiring either genuine authoring work (169, 199), proof-language
expertise (24/26/27), a different tlapm build (71/83), or a harness/toolchain upgrade
(66/75/76 ABI, 77 simulation-mode) — none are quick closes, matching the 2026-07-08
findings exactly. No corpus/harness files were modified this pass; only
`results/runs/w25-probe-199/` was added as scratch evidence.
