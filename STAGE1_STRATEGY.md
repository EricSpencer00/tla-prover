# Stage 1 Sweep Strategy (W1.2c) — as executing, 2026-07-04

Written while `g1-sweep-gptoss120b` runs, at Eric's request, with a resource
critique below. Binding context: PLAN.md Stage 1, STAGE1_BRIEF.md, budget frozen
in corpus/configs/repair_budget.json (commit 2994165).

## The strategy as launched

**Models (Eric's decision 1: open-source first, ALCF Argonne inference):**

| arm | model | role |
|---|---|---|
| 1 (running) | `openai/gpt-oss-120b` | primary — strongest general reasoner on Sophia |
| 2 (queued) | `mistralai/Devstral-2-123B-Instruct-2512` | second method — coding-tuned |

Endpoint `https://inference-api.alcf.anl.gov/resource_server/sophia/vllm/v1`,
Globus refresh-token auth (token minted by a local helper script named in
`OPENAI_API_KEY_CMD`; nothing credential-bearing lives in this repo), no dollar
spend. gpt-oss-20b was the dry-run model only.

**Per-spec escalation (fixed in repair_budget.json):** baseline → 2 iterative
repair rounds (fed the candidate's own trace/error + fault-localized fragment) →
best-of-8 at T=0.8 → symbolic mutation pass on near-misses; ≤24 candidates,
16k max_tokens (reasoning models starve at 8k), TLC timeout 120s (600s for the 7
HPC-certified intractable specs).

**Discipline:** verification strictly sequential (TIMEOUT_CONTENTION.md); one
arm at a time for the same reason. Append-only ledger rows per attempt; pass@1
vs pass@N separated; vacuity battery on every pass.

**Expected row economics per arm:** ~171 specs pass at baseline (0 model calls,
1 TLC run each) · ~13 timeout-class specs burn full budget unverifiably ·
~20 genuinely repairable specs get the real model work. Wall-clock estimate
12–24h/arm, dominated by sequential TLC, not model latency.

## Critique — resource allocation

**1. The big waste: full escalation on specs where verification cannot succeed
locally (≈ half the wall-clock, zero information).** The ~13 timeout/
state-explosion specs (HPC-closed 1/16/17/73/79/146 + certified-intractable
28/40/48/49/60/64/89) fail baseline *by timeout*, so the agent escalates — but
every candidate's TLC also times out. No repair can ever be *confirmed*, so all
~8–24 rows per spec record `tlc=timeout` at 30–60 min/spec: ~6–12h/arm spent
learning nothing we don't already have HPC evidence for. Gate 1 wants a row and
a failure class (`state-explosion`) for these, not an unfalsifiable candidate
pile.

*Fix:* per-spec budget overrides (`iterative_rounds: 0, best_of_n: 0`) with a
`_reason` citing the HPC certification — the same Amendment-4 logic that closed
Gate 0. This is a *documented budget allocation*, not a dropped spec: the specs
keep their 206-matrix rows (baseline + class). Saves ~⅓–½ of each arm.
Amendment-guard check: it does not make the gate easier — the gate is
completeness of measurement, and a model "pass" on these specs is unmeasurable
locally by definition.

**2. Redundant baseline re-verification in arm 2 (~3–4h).** Baseline rows are
model-independent; arm 2 re-runs ~200 TLC checks that arm 1 just ran. Kept
anyway: rerunning is the cleaner Rule-3 story (each run reproduces from its own
config alone), the cost is hours not days, and it doubles as a flakiness check
on the instrument. Revisit only if we add a 3rd+ arm.

**3. Model latency is not on the critical path — don't engineer around it.**
The brief allows parallel model calls; but with sequential TLC dominating,
prefetching best-of-N samples would save minutes/spec at real complexity cost
(the iterative rounds are inherently serial anyway). Rejected for v1.

**4. Sophia queue behavior.** gpt-oss-120b is served hot; Devstral may need a
cold-start (~minutes) on first call and unloads after 2h idle — arm 2 will hit
one cold start at most, negligible.

**5. What would actually raise the model-only ceiling** (if the residue after
both arms disappoints): a 3rd arm on Llama-3.1-405B costs only wall-clock;
escalating best_of_n 8→16 on near-misses (Eric pre-approved); and TLAPS-repair
prompting for proof_module specs (currently best-effort per decision 5). All
cheaper than any engineering change.

## Recommendation

Adopt fix 1 now: kill arm 1 (30 min in, still on spec 1 — itself one of the 13),
add the 13 per-spec zero-escalation overrides with reasons, restart. Net saving
≈ 6–12h per arm, identical Gate-1 evidence. Fixes 2–4: no action.
