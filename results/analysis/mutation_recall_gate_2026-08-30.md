# Mutation-operator recall gate: first measurement (2026-08-30)

Closes the TODO at PLAN.md:480 and follow-up 1 of
`w4_nokill_spot_audit_2026-07-21.md`. Gate: `python3 -m harness mutation-recall`.

Method: a localized reference probe set (guard_relax, conj_to_disj, cmp_relax,
bound_shift; one mutant per site) runs through the same SANY+TLC+verdict path as
the deployed 4-operator battery. A spec is `covered` when both sets score a
non-TypeOK safety kill, `recall_miss` when only the probes do, `no_evidence`
when neither does (excluded from the denominator). Probes never touch a
cfg-checked definition; the whole-module battery does, so the recall numbers
below are an UPPER bound. 12 specs per arm, seed 0, 60s timeouts.

| arm | ledgers | covered | recall_miss | no_evidence | operator recall |
|---|---|---|---|---|---|
| A: W4 Opus wave 1 | shards 0-3 | 9 | 2 | 1 | **0.82** PASS |
| B: W4 Opus audit region | shards 60-75 | 1 | 7 | 4 | **0.12** FAIL |
| C: organic gpt-oss funnel | w2-gen-20260710* | 1 | 7 | 4 | **0.12** FAIL |

Result: the audit's conclusion holds and now has a number. On arms B and C the
battery finds 1 of 8 corruptions that the specs' own invariants demonstrably
catch. Every `no_kill` and `no_site` in those ledgers is a battery artifact
first; it cannot be read as spec weakness.

Missing operators, by how many recall_miss specs they killed:
- arm B: bound_shift 5, guard_relax 4, cmp_relax 1
- arm C: conj_to_disj 3, guard_relax 3, bound_shift 3, cmp_relax 2

Arm A's 0.82 is not good news. Wave-1 shards 0 and 3 reverse-engineered the
battery's regex quirks and planted guaranteed-catch sites (PLAN.md:478). High
recall there measures the planting, not the battery. The two arms that were not
engineered against the battery both read 0.12.

Not done: promoting the probe operators into `mutation.MUTATIONS` and re-scoring
the corpus. That changes the `mutation_evidence` of every ledgered survivor, so
it is a corpus decision, not a harness fix.
