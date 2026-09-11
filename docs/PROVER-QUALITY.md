# Prover quality pillars

These requirements govern the continuing prover goal. They supplement the frozen
acceptance contract in `PROVER-GOAL-2026-09-05.md`; they do not replace its gates
or create a second execution board. Current ownership, results and next decisions
belong only in `PROVER-BOARD.md` through its publisher.

Experiments may regress or fail. Promotion must not silently degrade established
quality. Keep the last verified baseline available until its replacement satisfies
every applicable requirement below. Missing evidence means unverified, not passed.
These checks establish quality on the evaluated contract, not a guarantee about
every unseen input.

## 1. Preserve the intended behavior

The gates remain 100% SANY, then 100% applicable TLC, non-vacuous intended behavior
on unseen specifications, and genuine TLAPS proofs. Preserve theorem statements,
invariants, obligations and immutable scaffold bytes. Do not replace a requested
behavior with a weaker property, trivial theorem, admission or empty obligation set.
Success at a later gate must retain the earlier gates.

Required evidence: the frozen contract identity and gate-by-gate results, including
applicability and non-vacuity checks. A diagnostic subset cannot certify the goal.

## 2. Compare fairly and prevent regressions

Freeze evaluation rows, source-family separation, prompts, scaffolds, checkers,
budgets and scoring rules before measuring a candidate. Keep every eligible row
in the denominator, including failures, timeouts and unknowns. Compare parent and
candidate under the same contract and report paired per-row outcomes, not only
an aggregate that can hide lost capabilities. Preserve relevant symbolic baselines.

Required evidence: a paired comparison showing no loss of previously verified
required behavior and the claimed improvement. A regression blocks promotion;
retain the candidate as an experiment and investigate it. Changed inputs, targets,
budgets or denominators define a separately labeled diagnostic, not an improvement
under the frozen gate. Changes to user requirements require explicit user direction.

## 3. Trace every result to its actual producer

Distinguish hand-written positive/negative controls, reference repairs, symbolic
search and model-generated candidates. A hand-written malformed patch rejected
by SANY is a control result, not a model rejection or evidence of a tokenizer bug.
Do not infer provenance from a directory name, job ID or shared row number.

Required evidence: source and candidate hashes, producer type, exact prompt and
scaffold identity, raw outputs, and checker receipts. Model claims also require
model/tokenizer identity and actual checkpoint restore evidence; training claims
require actual updates and saved/reloaded checkpoint evidence. Correct mistaken
claims with a linked correction while preserving original receipts.

## 4. Verify the verifier and the complete execution path

Use known-good and known-bad controls through the actual checker interface. Require
the relevant exit status and substantive output; a success string, valid prefix,
empty obligation set or stale cache is insufficient. Genuine TLAPS certification
requires strict uncached checks and positive fully proved obligation counts.

Required evidence before a remote experiment: the exact staged file manifest and
dependency closure, executable entry-point checks, and a bounded representative
path exercising the intended inputs and outputs. An import or `--help` smoke only
certifies what it actually executed. An empty successful script does not establish
inference, model loading, assembly, checker execution or remote readiness. Keep
infrastructure failures and unavailable observations separate from model outcomes.

## 5. Advance by evidence, not repeated activity

State the hypothesis, its distinguishing observation and the decision it will
change before an experiment. Fix reproducible local defects in scope. Repeated
unchanged passing tests, fixture edits or retries are not progress toward model
quality. When scores flatten, failures repeat or fixes merely move the error,
reopen materially different hypotheses and choose a discriminating check.

Required evidence: the observed failure, causal intervention and resulting decision.
Only a verified external dependency justifies an external wait; a failed experiment
does not block useful local work. Preserve one execution owner and reconcile live
job ownership before submission using the submission guard.

## 6. Make accepted work reproducible and recoverable

Commit each coherent verified change and relevant small reproducibility records
before handoffs or remote experiments. Preserve unrelated edits and keep secrets,
checkpoints, locks and bulky generated output out of Git. Record large artifacts
by identity and location. Inspect saved artifacts even after a nonzero exit: a
summary-writing crash does not establish that training or checkpoint saving failed.

Required evidence: commit and payload identities, targeted verification, artifact
locations, measured results and explicit unknowns. Publish meaningful transitions
on the board with actual observation times and pass its checker before handoff.
Do not rewrite historical evidence or treat an old observation as live truth.

## Promotion and handoff decision

For an implementation acceptance, model promotion or completion claim, record on
the existing board a concise decision linking the applicable evidence above:
what changed, which contract was measured, what passed or regressed, what remains
unknown, and whether the candidate is diagnostic-only or eligible for promotion.
Unmet requirements keep the candidate unpromoted and the last verified baseline
intact. Continue useful authorized work; this contract adds no permission request
for routine fixes and grants no additional external authority.
