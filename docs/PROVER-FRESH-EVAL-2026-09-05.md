# Fresh proof evaluation discovery — 2026-09-05

## Verdict

A **14-target control shortlist across six directory families and seven source files** is available from the pinned local Examples checkout. All14 pass read-only whole-fragment syntax, source/assembled/target-goal lexical exclusion, definition-only custom dependency checks, exact Git-byte checks, and the current3072-output/8192-context feasibility test. **Zero are admitted evaluation tasks yet:** no TLAPS positive or negative controls, generation, training, or model-output-based selection was performed.

This is an isolated evaluation proposal, not another TRAIN harvest. Do not add these targets, their references, controls, or feedback to training. No G2 claim follows from this discovery: unknown foundation-model pretraining remains unknown, multiple targets share human-proved prefix scaffolding, and a lexical test does not certify semantic novelty.

The autoresearch workflow guided the decision: establish actual exposure provenance first; screen source identity and dependency trust before examining target shape; stop after a bounded shortlist and recommend controls rather than expanding the search indefinitely. Parent supplied ongoing model outcomes only after the candidate pool had been selected; those outcomes were not consulted for selection.

## Actual prior-training exclusion inventory

Paths below are relative to /Users/eric/GitHub/prove-TLA. The following are recorded training inputs/configurations, not inferred from names alone.

| Population | Binding manifest / actual evidence | SHA256 |
|---|---|---|
| Earlier6 SFT; subset of hierarchical17 | results/runs/proof-training-cycle-20260905-v1/training/manifest.json | 23811bcbae1967a56b1a7e7421c32569662040dbae7d9503e1ab0c790aeae19f |
| Corrected family6 metadata | results/runs/proof-family-manifest-20260905-v3/manifest.json | 58196ff75d174ff97ec6b70306c01ab709b814688422629f9424fee4801e4ce7 |
| Leaf50 SFT | results/runs/proof-leaf-manifest-20260905-v1/defs-complete/manifest.json | fa42ce3fa8db5b928ffa69d3da338bf32f0720c60d22f78a2776e9ba9000daca |
| Hierarchical17 SFT and finite-candidate RL17 | results/runs/proof-multistep-manifest-20260905-v2/manifest.json | c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344 |
| Whole6 SFT | results/runs/proof-breadth-controls-20260905-v1/manifest.json | 23d15fba5fcb08e8d8436d02deb727a34976bc220e8d66ec7bc333728949627e |
| New26, combined with whole6 for broader32 | results/runs/proof-breadth26-controls-20260905-v1/manifest.json | fa9891e67e8c099e2956d5d9f78a29780f186c132a6446d0ed02e5dc89487526 |
| Actual RL17 frozen prompts/candidates/context | results/runs/proof-candidate-rl-20260905-v1/frozen.json | 0c5a9d23e74afa55a6b03e4ebb865b93858bef3efa10f9b81436663fc9167e63 |

The six corrected-family TRAIN prefix/reference/suffix/source-hash fields were compared against the earlier6 training snapshot: all identical. Thus the metadata revision adds no distinct training source or response.

Actual CUDA training/train.json hashes, checked against their manifest bindings and training/config.json train_ids:

- proof-cuda-cycle-20260905-v2: 64c27f262f9eba2694ba05a428aaba66ddf3af12dd0e92cc6537cd10a41263f9 (leaf50).
- proof-cuda-hierarchical-cycle-20260905-v2: b105e352f5cfdda5fe878ea5d9760a5bc220d17c0c7f511a875577acbff00e06 (hier17).
- proof-cuda-whole-cycle-20260905-v2: 78c3dd57247edde10c50dc12e6e8a3ca2f720f0a98f6d0eca901c359c13cfeff (whole6).
- proof-cuda-broader-cycle-20260905-v1 and proof-cuda-exposure-cycle-20260905-v1: 5adb8315e8d9563fbf42a40fa5055d4e4b3b7f3e3c6e4ec7fe889b05ca030860 (same broader32 packet; repetition adds exposure, not new membership).

Earlier Qwen SFT configs inspected: proof-training-cycle-20260905-v1/training/config.json and proof-multistep-cycle-20260905-v1/training/config.json. RL config binds the hierarchical17 manifest, the frozen17 SHA above, and its hierarchical SFT parent. The premise-search run is symbolic development evaluation, not an optimizer input; its four DEV sources are independently excluded. The retrieved-context evaluation is likewise not mistaken for training. Actual RL imported context resolves only to installed TLAPS.tla; its raw library source and every frozen relevant/imported statement were included conservatively.

The union is **99 distinct configured TRAIN task IDs** (50+17+6+26), not99 independent sources: **12 target source files,17 target-source-plus-custom-dependency paths**. Earlier6 are duplicates. Raw source hashes matched every available training-manifest hash; no drift found.

Under tools/tlaplus-examples/specifications/, the17 excluded paths are:

```text
LearnProofs/AddTwo.tla
LearnProofs/FindHighest.tla
TeachingConcurrency/Simple.tla
sums_even/sums_even.tla
locks_auxiliary_vars/Lock.tla
barriers/Barriers.tla
barriers/Barrier.tla
MisraReachability/ReachabilityProofs.tla
MisraReachability/Reachability.tla
LoopInvariance/Quicksort.tla
LoopInvariance/BinarySearch.tla
glowingRaccoon/clean_proof.tla
glowingRaccoon/clean.tla
lamport_mutex/LamportMutex_proofs.tla
lamport_mutex/LamportMutex.tla
tcp/tcp_proof.tla
tcp/tcp.tla
```

The scope here is locally recorded proof-training experiments. This is not an audit of all historical ChatTLA pretraining, corpus SFT, or opaque Llama pretraining. That broader provenance gap remains explicit.

## Exclusion method and accounting

Reuse tools/proof_breadth_manifest.py:exclusions(parent), compare(), comparison_key(), goal_bodies(), extract(); parent is results/runs/proof-multistep-manifest-20260905-v2/manifest.json, SHA c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344. Its official_sources array is the exact149-path/hash inventory (119+30); its four development rows bind DEV source/dependency paths. Original18 stays commit-bound to /Users/eric/GitHub/ChatTLA/ChatTLA commit fd1fd3671ca62940c78210f7125a0a42c4a1a857:

- public blob: 2a0e846e5ff7cfd1c4fae282a9ae1a64e8b3f677dac27fe32379dd839c710357.
- reference exclusion blob: 5444bd7da9a1946380877202f48658376df0c8e77bbf5328b9547c9eecb78e35.

The original18 paths at that commit are data/processed/prover_eval.jsonl and outputs/hf_publish/chattla-tla-prover-corpora-v1/data/traces/tlaps_verified_autoprover_traces_v1.jsonl. Read these only inside the isolated exclusion/control audit; never export their proof answers. The additional RL library source is tools/tlapm/lib/tlapm/stdlib/TLAPS.tla, bound by each RL frozen row's context.library_sha256.

Append every TRAIN raw source/custom dependency, each complete prefix+reference+suffix training assembly, explicit target_goal where available, and all named goal bodies in those sources/assemblies. This deliberately retains all leaf50 scaffold/context variants even though their source files overlap hierarchical17. Finally append the RL frozen target statements and visible/imported statement context and its TLAPS library source.

The read-only comparison population contained **316 source/assembly entries and901 goal/context entries**, including repeated historical entries (not independent counts). The five scanned training manifests contain105 rows because earlier6 are repeated;99 IDs are distinct.

Reject a candidate when **any** of raw source, assembled control module, target goal body, or custom dependency has exact normalized equality or token-shingle Jaccard >=0.65 against the corresponding exclusion population. The existing harness/corpora.py lexical normalization/shingle parameters were unchanged. Raw source and reference bytes are not normalized for controls. Also disclose matching earlier goals in the immutable prefix separately; do not hide them by reporting only target overlap.

We additionally compared proposed goals against one another. Two of the original16 were removed before freezing this14 shortlist: AsyncTerminationDetection.TypeCorrect vs its Safety goal scored0.666667; byzpaxos.InductiveInvariance vs spanning.SntMsgStep had exact normalized equality/1.0. They remain rejected alternatives, not extra attempts.

## Exact14 target shortlist

All source paths below are relative to tools/tlaplus-examples/specifications/. Every source and custom dependency was byte-compared to Git commit **47b0e2cc0268836b89f5ce451f38e5df5f1cf773**. The checkout was clean. Reference spans are isolated future control data only; their contents are intentionally absent from this document.

Line tuples are **(theorem declaration first line, proof first line, proof last line inclusive)**. Use exact prefix through the line before proof; exact proof substring for positive controls; suffix newline + ==== + newline. No source renaming, proof rewriting, declaration deletion, or semantics changes.

| Source | Path | SHA256 |
|---|---|---|
| S1 | DieHard/DieHard_proof.tla | 581a7773656302ec59ec3dc6eae78e4c9d39ee9e70894b6fba364f185b123033 |
| S2 | Paxos/Consensus.tla | c5c181338db9d7489da158daaead6e8ed47b91ca5802f64ecab02dfd379f8e21 |
| S3 | byzpaxos/Consensus.tla | 5b877e93b31c982e80b1443127bc2c50c090d7f8d729d468f3b42849315205bf |
| S4 | ewd840/EWD840_proof.tla | 2b00ab2de84711226037c464f6d39213169d695a1f049f57058c55e115c0586e |
| S5 | ewd840/SyncTerminationDetection_proof.tla | 77cb25e68e54084a4ac07327bb60f0ad171d3aa969cdf278cb4836a504d4983b |
| S6 | ewd998/AsyncTerminationDetection_proof.tla | 87cc4e25be553691b1819b1be20b0addec2f724cec9ffe081014b23f99722ec7 |
| S7 | spanning/spanning_proof.tla | 2c96247c40d77a391d56f0cc744d0c0fa7818ffbb0d99d10e411bf82afedf59a |

| # | Source / theorem | Line tuple | Prompt tokens | Reference tokens* | Max Jaccard source / assembled / goal |
|---|---|---|---:|---:|---|
| 1 | S1 / MinNat | (9, 12, 12) | 1645 | 5 | 0.146958 / 0.011236 / 0.021739 |
| 2 | S2 / LivenessTheorem | (59, 60, 68) | 578 | 147 | 0.113433 / 0.113433 / 0.000000 |
| 3 | S3 / EnabledDef | (185, 186, 186) | 2060 | 13 | 0.077114 / 0.108392 / 0.000000 |
| 4 | S3 / LiveSpecEquals | (205, 207, 207) | 2254 | 22 | 0.077114 / 0.077114 / 0.000000 |
| 5 | S4 / Safety | (55, 56, 59) | 2818 | 43 | 0.070141 / 0.168521 / 0.000000 |
| 6 | S4 / EnabledSystem | (95, 100, 109) | 3385 | 169 | 0.070141 / 0.125131 / 0.010638 |
| 7 | S5 / CorrectDetection | (16, 17, 22) | 799 | 96 | 0.083916 / 0.120141 / 0.000000 |
| 8 | S5 / Quiescent | (24, 25, 28) | 908 | 60 | 0.083916 / 0.103125 / 0.000000 |
| 9 | S5 / Enabled_ST | (37, 40, 40) | 1040 | 16 | 0.083916 / 0.094556 / 0.018868 |
| 10 | S6 / Safety | (19, 20, 26) | 1390 | 89 | 0.074236 / 0.108108 / 0.004149 |
| 11 | S6 / Stability | (28, 29, 31) | 1497 | 59 | 0.074236 / 0.098214 / 0.004167 |
| 12 | S6 / EnabledDT | (41, 44, 44) | 1642 | 16 | 0.074236 / 0.090164 / 0.018182 |
| 13 | S7 / SntMsgStep | (30, 31, 147) | 1123 | 1573 | 0.105521 / 0.092990 / 0.250000 |
| 14 | S7 / SntMsgInv | (149, 150, 156) | 2711 | 94 | 0.105521 / 0.104749 / 0.000000 |

*Reference token counts are feasibility metadata only, without chat EOS overhead; references were never exported in prompts. Actual rendered prompts used tools/proof_whole_packet.py:task_prompt and the exact inference encoder, local pinned Llama tokenizer at results/runs/proof-cuda-tokenizer-20260905-v2. All14 prompt counts plus3072 are <=8192; maximum prompt3385. All reference fragments are below3072 tokens (maximum1573). This checks one exact reference's representability, not that any model will find it. Any new prompt wording must be re-tokenized before sampling.

Families: DieHard1, Paxos1, byzpaxos2, ewd8405, ewd9983, spanning2. These are14 whole-target tasks, not14 independent protocols or14 full system proofs.

### Definition-only custom dependency closure

| Dependency path | SHA256 |
|---|---|
| DieHard/DieHard.tla | 295495de6509d86a82b88757835b95e3f91fad8691d764ece4d98886dcf42b66 |
| ewd840/EWD840.tla | 4a42e8a67c7ecb8425c6e370a5d3b180ad697751128d7b331e778afbcd29b747 |
| ewd840/SyncTerminationDetection.tla | 3626ab87e7431a7c07cf0f92b442fdf38363e6d7a9928f2391476c54a1e4fb2e |
| ewd998/AsyncTerminationDetection.tla | c1b15be68a73c6e5f69c5c09f2736870182a9b0765ad9860452240119911b030 |
| spanning/spanning.tla | 878e917b075f6cd2bfa2a2d0083c1c66e9eb47fe2baaed41dd9a0a28fbcb2c36 |

S1 uses DieHard; S4 uses EWD840 plus SyncTerminationDetection; S5 uses SyncTerminationDetection; S6 uses AsyncTerminationDetection; S7 uses spanning. S2/S3 require no custom dependency. The maximum custom-dependency Jaccard against exclusions is0.048. check_dependency accepted all listed custom modules: no custom THEOREM/LEMMA/COROLLARY/PROPOSITION/AXIOM/OMITTED declarations. Existing parameter assumptions and INSTANCE substitutions remain immutable; installed theorem libraries remain explicitly trusted, not newly certified here.

All14 exact reference fragments passed full-proof-fragment-v1 validate_fragment via extract(). All14 targets also support the scoped conclusion-only FALSE mutation from proof_breadth26_manifest.wrong_conclusion without deleting ASSUME/NEW bindings. Neither result is proof verification.

### Context overlap disclosures

- Paxos.LivenessTheorem, byzpaxos.EnabledDef and LiveSpecEquals retain earlier Invariance goal templates matching excluded material.
- EWD840.Safety/EnabledSystem retain earlier TypeCorrect/Invariant templates.
- SyncTerminationDetection.CorrectDetection/Quiescent/Enabled_ST retain earlier TypeCorrect templates.
- The other shortlisted prefixes have no >=0.65 or exact normalized named-goal matches in this audit.

These human preceding proofs remain in the evaluation prompt and full checked module, as with the existing whole-target task contract. Do not describe this as unscaffolded whole-spec theorem discovery. Paxos/byzpaxos Consensus are also familiar protocol templates: lexical clearance of these goals does not prove conceptual novelty relative to the official Consensus problem.

## Rejected or deferred sources

The bounded lexical inventory screened76 files containing named THEOREM/LEMMA declarations;57 cleared the source-only threshold. Most were then rejected before target selection because their custom imports export unchecked theorem declarations or overlap protected sources.

- CigaretteSmokers_proof: its definition module is0.957806 near an excluded source. ReadersWriters and MissionariesAndCannibals custom modules have exact normalized excluded-source matches. Low overlap of a newly added proof file does not rescue its dependency.
- SchedulingAllocator/AllocatorImplementation/SimpleAllocator, MultiCarElevator, EWD687a, EWD998/EWD998PCal, transaction_commit proofs, several SpecifyingSystems proof modules, and byzpaxos BPCon/PCon/Vote proofs import custom theorem-bearing modules. Do not strip those declarations to force admission. They require separate audited theorem-dependency certification or a different task, beyond this shortlist.
- Bakery/Boulanger, DieHard.TypeCorrect, SpanningTree.TypeCorrect, SyncTerminationDetection.TypeCorrect: exact normalized generic goal overlap. TeachingConcurrency.SimpleRegular goals overlap actual earlier TRAIN, even where whole-source Jaccard is below0.65.
- MajorityProof: source0.9187 against official30:131. Existing TRAIN raw source matches, e.g. Quicksort/Lock/Lamport/tcp, remain excluded at1.0.
- KnuthYao.Prob.Converges: no source proof to supply positive control.
- TwoPhase.Implementation: current full-fragment hierarchical structure unsupported.
- byzpaxos.Liveness, EWD840.Round1/2/3, SyncTerminationDetection.Live and AsyncTerminationDetection.Liveness: current single-definition hierarchical DEFINE contract rejects the exact original proof. No contract relaxation or rewriting was attempted.
- EWD840.Live: otherwise lexical/contract credible, but prompt5961+3072 exceeds8192; no truncation.
- SumSequence has otherwise plausible new source goals but belongs to the already-trained LoopInvariance family, so it was not needed for this fresh-family shortlist. Its late Lemma5_Proof also exceeds the unchanged context budget (5316+3072). No sum-sequence task is included.
- The two within-shortlist goal overlaps described above were removed independently of any model or checker outcome.

The search stopped at the14 credible, pairwise-screened candidates. This is not an exhaustive theorem census; heuristic proof-boundary discovery can miss unusual syntax. Exact shortlisted boundaries, unlike the broader inventory, were individually extracted and contract-validated.

## Fastest next experiment and gates

1. Implement a NEW evaluation-only selection/control wrapper. Freeze these exact14 tuples, all raw Git hashes, the exclusion-manifest/packet hashes, algorithm code, tokenizer files, installed standard libraries/backends and exact prompt bytes. Never call a training export API on this population.
2. Run **28 serial controls**, positive then conclusion-only FALSE for each task, **30 seconds/module,1000 seconds total**, append-only unique output; keep all14 denominator and explicit unattempted/timeout/infrastructure states. Snapshot full verifier identity before/after. No checker was invoked in this discovery.
3. Require positive strict uncached TLAPS rc0, total=proved>0, exact module/dependency hashes, timed_outFalse. Require negative parsed rc10 with exactly one failed obligation and the intended PROVE FALSE diagnostic, not merely a parse failure or nonzero exit. Full-proof-fragment-v1 remains unchanged.
4. If a reference/control fails, preserve the selected14 and diagnose that construction/control failure before model sampling. Do not silently shrink to successes or claim14 admitted. A revised population must be separately preregistered before any model outputs are seen.
5. Only after controls and complete exclusion reconstruction pass, freeze a reference-free evaluation packet and matched BASE/parent/child sampling budget. Report per-family results, short helper lemmas versus protocol properties, and scaffolded task shape. Any later feedback adaptation turns this set into development and requires another unseen evaluation.

No control invocation is provided as an existing executable: the new14 evaluation-only wrapper does not yet exist. Reusable pure APIs are extract(), exclusions()/compare(), check_dependency(), and conclusion-only wrong_conclusion(); reuse the existing strict full-fragment checker rather than altering it. This report does not authorize training or amend PLAN gates.

## Remaining uncertainty

- Actual positive/negative control validity and runtime within30 seconds are unmeasured. Installed library resolution and complete backend attestation remain execution preflight requirements.
- Earlier module prefixes can contain proof constructs that are not part of the target fragment; full-module TLAPS must validate them. A fragment syntax pass cannot establish them.
- The lexical normalization is not alpha-equivalence or semantic duplicate detection. Generic helpers and familiar Consensus protocols may be much less novel than low Jaccard suggests.
- The inventory binds locally recorded proof-training runs, not unknown foundation-model pretraining or the entire historical corpus-training lineage.

## Main-agent independent review before controls

All14 frozen source/proof boundaries and source hashes were independently
reconstructed against the pinned Git commit; each exact fragment passed the
unchanged syntax contract and supported conclusion-only FALSE construction.
The actual five CUDA training packets were also matched to their input hashes,
ordered config IDs, exact manifest reference responses and assembled-module
hashes:99 distinct training IDs. These checks are not TLAPS proof results.

The SyncTerminationDetection.Enabled_ST and
AsyncTerminationDetection.EnabledDT statements share the same logical template:
the detection action is enabled exactly when termination holds and has not yet
been detected. Source definitions differ, but lexical clearance must not be
reported as independent mathematical novelty. Both remain in the frozen14;
there is no post-selection substitution. Results must distinguish helper lemmas,
enabledness characterizations, temporal properties and inductive steps.

Implementation clarification: the fresh-evaluation exporter calls
`whole_prompt(task)` directly. `task_prompt` dispatches only legacy TRAIN/DEV
splits; no fresh task is relabeled TRAIN to use that dispatcher. Prompt text and
the pinned inference encoder remain identical to the research feasibility check.
