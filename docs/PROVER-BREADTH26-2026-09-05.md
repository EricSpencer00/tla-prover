# Prospective broader proof TRAIN controls

Decision: test these26 whole-target human proofs across four additional families
before any new training. This is a discovery shortlist, not certified data.
The previous three-policy feedback round proved0/4DEV for each policy; further
tiny-six memorization or the same feedback round is not the next experiment.

Source root: `tools/tlaplus-examples/specifications/`, pinned commit
`47b0e2cc0268836b89f5ce451f38e5df5f1cf773`.
Tuple fields: relative source, theorem, declaration line, first proof line,
last proof line (one-based inclusive).

```python
SELECTION = (
 ('LoopInvariance/Quicksort.tla','AutomorphismsCompose',58,61,61),
 ('LoopInvariance/Quicksort.tla','PermsOfLemma',63,69,69),
 ('LoopInvariance/Quicksort.tla','PermsOfPermsOf',71,74,84),
 ('LoopInvariance/Quicksort.tla','MinIsMin',93,96,96),
 ('LoopInvariance/Quicksort.tla','MaxIsMax',98,101,101),
 ('LoopInvariance/Quicksort.tla','IntervalMinMax',179,182,182),
 ('LoopInvariance/Quicksort.tla','PartitionsLemma',200,208,208),
 ('LoopInvariance/BinarySearch.tla','SortedLess',29,33,35),
 ('glowingRaccoon/clean_proof.tla','NatMinNat',18,21,21),
 ('glowingRaccoon/clean_proof.tla','PrimerPositive',63,64,66),
 ('lamport_mutex/LamportMutex_proofs.tla','BroadcastType',13,17,17),
 ('lamport_mutex/LamportMutex_proofs.tla','NotContainsAtMostOne',112,115,115),
 ('lamport_mutex/LamportMutex_proofs.tla','NotContainsPrecedes',117,121,121),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesHead',123,128,134),
 ('lamport_mutex/LamportMutex_proofs.tla','AtMostOneTail',136,140,140),
 ('lamport_mutex/LamportMutex_proofs.tla','ContainsTail',142,146,152),
 ('lamport_mutex/LamportMutex_proofs.tla','AtMostOneHead',154,158,158),
 ('lamport_mutex/LamportMutex_proofs.tla','ContainsSend',160,163,163),
 ('lamport_mutex/LamportMutex_proofs.tla','NotContainsSend',165,169,169),
 ('lamport_mutex/LamportMutex_proofs.tla','AtMostOneSend',171,175,175),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesSend',177,181,187),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesTail',189,193,203),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesInTail',205,211,225),
 ('tcp/tcp_proof.tla','NetworkType',21,25,25),
 ('tcp/tcp_proof.tla','PrefixOneNonEmpty',42,47,61),
 ('tcp/tcp_proof.tla','PrefixTwoNonEmpty',63,69,77),
)
HASHES = {
 'LoopInvariance/Quicksort.tla':'65c70e42eb28bef01e7754cffe66d87ac1d00b4cd27b107ce389da3f31ad7672',
 'LoopInvariance/BinarySearch.tla':'fa56deb7c8d1cce2e5b9c4559ab7a1ced1fea5098edc46eb8d99c257e8eaecec',
 'glowingRaccoon/clean_proof.tla':'f653d9241d938ead6ee72c509b6e46fdd46eab05678f576d0c8878155863f0f4',
 'lamport_mutex/LamportMutex_proofs.tla':'9cbecb6501595b2222e663e09145f48d3cd73df2c817f07acc4d76acb9ca9f61',
 'tcp/tcp_proof.tla':'23e7180bc27ce366579f604dfda04887e0b32e5642531c5efaf768ebea1e8cd7',
 'glowingRaccoon/clean.tla':'48ba67d167d158f4e34238e13b135ad83cb705ea12d842c0a3506ff851990d73',
 'lamport_mutex/LamportMutex.tla':'dfa726da541fb0515ad482c3b5ca82c81b6f54df6626c3b9edfcebedc2a9c05a',
 'tcp/tcp.tla':'c77f6c0c33e54d4b3ce8ecfd934967569be3f7c613c89b4fdcdfa3768fc56e92',
}
```

Read-only audit by whole_probe: current fragment contract passes all26; actual
whole-prompt maximum4481tokens, leaving3072 output within8192; selected proof
maximum213tokens including approximate terminal allowance. Custom dependencies
above inspected definition-only. Main must independently reconstruct source
and exclusions before certifying these claims in the machine manifest.

Mandatory full audit: official119/30, original18 source AND reference exclusion,
public DEV source/dependencies, target body without label, assembled prefix,
custom dependencies. Reuse `proof_breadth_manifest.exclusions` and comparison
logic; never use reference answers as prompts or candidate proofs. Generic
TypeCorrect helper proofs in prefixes must remain disclosed, not described as
independent unseen-theorem evidence.

Rejected discovery candidates: Majority/MajorityProof.tla has0.9187 source
Jaccard vs official30:131 and exact goal-body overlap. Quicksort NonemptyMin,
NonemptyMax and clean.Preservation fail the current full-proof contract.
Do not relax that contract to admit them. Quicksort source maximum0.4585 vs
official30:128 is preliminary; assembled target audits are still required.

Historical `results/proof_traces/examples-v1/summary.json` has70partial modules
and3timeouts; `harness/proof_traces.py` used toolbox checks without strict/nofp.
Those traces support discovery, not training admission.

Next implementation: NEW frozen26 driver with disjoint append-only run output.
Reuse exact-source `extract`, `wrong_conclusion`, `control_identity` and the
full-fragment checker. Do not mutate historical six-task builders or reuse
their hard-coded six-count summary/480second budget. Budget52serial controls,
30seconds/control,1800seconds total; ledger all26 selected tasks including
selection failures and unmeasured controls. Require positive rc0, nonzero all
obligations, and intended parsed FALSE failure; verify exactcandidate/dependency
hashes and runtime identity before/after. Preserve all failed controls. No GPU
run before new multi-family admission evidence; no G1/G2 claim from TRAIN.

Research method: autoresearch, local source/log evidence only, stopped at the
executable validation boundary. No new checker, optimizer or GPU run in audit.

## Pre-execution control correction

Main independently re-read and extracted all26targets: all8source/dependency
hashes match the pinned commit exactly, and all26 current fragment contracts
pass. Of26 targets,24 declare ASSUME NEW bindings before PROVE. The historical
six-task `wrong_conclusion` replaces the entire goal, which would discard these
bindings while preserving proofs that use them. Such undefined-name rejects
would not be intended FALSE controls. Therefore the NEW driver preserves exact
assumptions through the unique code PROVE token and replaces only the conclusion
with FALSE. Plain-expression goals PrimerPositive and NetworkType replace the
whole goal. Nested/multiple PROVE structures are unsupported and fail closed;
comments/strings cannot supply the boundary. Candidate proof bytes remain exact.
This is fixed before any run, with regression coverage; no historical data or
checker contract changes, no acceptance of parser failures as negatives.

Main full exclusion precheck completed (24381/85525):193 source entries and283
goal bodies including original18 reference exclusions; all26 source, assembled
candidate and target-body comparisons pass the frozen0.65 threshold with no
exact-normalized matches. All three custom dependencies also pass (maximum
0.0229). Definition-only dependency assumptions are preserved: LamportMutex
N/maxClock natural-number constraints and tcp's exactly-two-Peers constraint.
There are10hierarchical and16leaf targets. Preceding generic TypeCorrect bodies
in clean_proof and LamportMutex_proofs match the abstract Spec=>[]TypeOK template
in DEV/original18; their actual Spec/TypeOK definitions differ. This is disclosed
context-template overlap, not a claim of semantic independence or unseen training.
Machine selection must reconstruct these checks instead of trusting this prose.
