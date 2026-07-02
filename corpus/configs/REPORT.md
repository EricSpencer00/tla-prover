# W0.3 — Drafted TLC Configs for FormaLLM Corpus Gaps

Source corpus: `/Users/eric/GitHub/tla_benchmark/data/` (205 `.tla`, 134 original `.cfg`, 206 descriptions).
Outputs: `corpus/configs/drafts/N.cfg` (71 files), `corpus/configs/INVENTORY.csv` (all 205 specs).
Nothing in `tla_benchmark/` was modified. TLC was **not** run (validation happens in the harness).

## Counts

| Confidence | Count | Meaning |
|---|---|---|
| HIGH | 14 | Standard state-machine spec; all constants expressible in cfg syntax; invariants identified. Expected to run as-is (after file-to-module rename). |
| MED  | 13 | Runnable draft but something needs human eyes: definition overrides, proof-module deps, unbounded state space needing a constraint, symmetry, nested-set literals. |
| LOW  | 44 | Not model-checkable as drafted: no behavior spec (libraries/theorem modules), operator/function/sequence/record-valued constants, unbounded CHOOSE, or missing library modules. |

HIGH: 2, 5, 30, 38, 45, 62, 107, 108, 144, 151, 152, 165, 172, 179
MED: 67, 71, 89, 102, 104, 112, 118, 119, 122, 145, 147, 174, 191
LOW: 29, 39, 41, 47, 48, 50, 53, 56, 69, 72, 77, 80, 81, 83, 86, 87, 101, 105, 106, 110, 114, 115, 116, 117, 121, 123, 124, 129, 131, 134, 137, 138, 139, 140, 142, 148, 176, 182, 183, 189, 190, 192, 198, 200

## Orphan description

**Spec 120**: `data/descriptions/120.json` exists but there is no `data/tla_files/120.tla`. (206 descriptions vs 205 tla files; every other number 1-206 pairs up.)

## Module-name mismatch reminder

Every file is numbered (`N.tla`) but TLC requires filename == module name. `INVENTORY.csv` records the true module name per spec; the harness must rename on copy — and must also co-locate dependency modules (e.g. `2.tla`/ACP_NB EXTENDS ACP_SB = `5.tla`; proof modules EXTEND their base spec + `TLAPS`). Note `TLAPS.tla` appears 5 times in the corpus (specs 69, 86, 116, 183, 200).

## LOW-tier breakdown (44)

- **No behavior spec (libraries/theorem/constant-only modules), 24**: 29 (CarTalkPuzzle, constant puzzle), 56 (Relation), 69/86/116/183/200 (TLAPS x5), 81 (EWD998 sim-control script), 87 (Utils), 101 (ClientCentric), 105 (DyadicRationals), 106 (Util), 110 (Functions), 114 (NaturalsInduction), 115 (SequenceTheorems), 117 (WellFoundedInduction), 123 (ZSequences), 124 (LevelSpec), 134/138/139/140 (Reachability test/lib family), 182 (sums_even), 190 (Bits).
- **Constants not expressible in cfg (operator/function/tuple/record-valued), 10**: 47, 48, 50, 137, 142, 148, 176, 189, 192, 198.
- **Missing non-corpus library modules, 6**: 72 (SVG), 77/80 (CSV + `TLCGet("config")` generate-mode ASSUMEs), 83 & 131 (FiniteSetTheorems), 129 (SequencesExtTheorems).
- **No zero-arity Next action, 3**: 39 (Age_Channel), 41 (EPFailureDetector), 53 (RingBuffer — component module).
- **Infinite Init set, 1**: 121 (LeastCircularSubstring; use its MC wrapper, spec 122).

## Ten gnarliest cases

1. **148 Nano** — `CalculateHash(_,_,_)` operator constant plus function-valued `KeyPair`/`Ownership`; only checkable through MCNano (spec 147, drafted MED with `CalculateHash <- CalculateHashImpl`).
2. **47/48 DiskSynod/HDiskSynod** — operator constants `Ballot(_)`, `IsMajority(_)` *and* the parent Synod's unbounded `CHOOSE c : c \notin Inputs`; both need an MC module.
3. **50 Synod** — `ISpec` is checkable in principle, but `NotAnInput` (unbounded CHOOSE) blocks TLC and `SynodSpec` uses temporal quantifier `\EE`.
4. **189 TLCMC** — a model checker modeled in TLA+: `StateGraph` is a record-valued constant (`[states |-> ..., actions |-> ...]`) that a cfg cannot express.
5. **174 Slush** — `HostMapping` is a set of 3-element sets mixing three model-value sorts (`{{n1,l1,q1},...}`); drafted as a nested set literal, but TLC cfg support for nested literals must be verified (MED).
6. **192 HanoiSeq** — towers are *constants* `A, B, C` that must be sequences (`ASSUME A \in [1..Len(A) -> Nat]`); cfg has no tuple syntax.
7. **77/80/81 EWD998 opts family** — `ASSUME TLCGet("config").mode = "generate"` means they only run in TLC simulation mode, and they EXTEND the CSV community module which is not in the corpus.
8. **83 EWD998_proof / 131 MajorityProof / 129 SumSequence** — EXTEND TLAPS-distribution theorem modules (`FiniteSetTheorems`, `SequencesExtTheorems`) that are *not* in the corpus, so they will not even parse without fetching those libraries (unlike `NaturalsInduction`/`SequenceTheorems`/`WellFoundedInduction`, which the corpus does contain).
9. **39/41/53 (Age_Channel, EPFailureDetector, RingBuffer)** — define `Init` and parameterized actions but no zero-arity `Next`; a wrapper module must build the next-state disjunction before TLC can run.
10. **121/122 LeastCircularSubstring** — the base spec's `Corpus == ZSeq(CharacterSet)` is infinite (TLC cannot enumerate Init); the MC wrapper (122) bounds it, but may additionally need a `ZSeqNat`-style override into ZSequences — flagged for review.

## Notable patterns

- The corpus mixes four kinds of "spec": real state machines, MC wrapper modules, TLAPS proof modules over a base spec elsewhere in the corpus, and pure operator/theorem libraries. Only the first two are directly checkable; proof modules are checkable *through* their inherited `Spec` when their dependencies are in the corpus (drafted MED).
- Duplicates exist: `TLAPS.tla` x5; the EWD998 family spans 8+ numbered files.
- Several specs follow the `CHOOSE v : v \notin S` "null value" idiom (KeyValueStore); drafted using cfg *definition overrides* (`NoVal = NoVal`), a standard TLC trick worth encoding in the harness template.
- Original cfgs use both `INVARIANT`/`INVARIANTS` and `PROPERTIES` spellings; drafts standardize on `INVARIANTS`/`PROPERTIES` to match the dominant corpus style (e.g. `1.cfg`, `166.cfg`).
