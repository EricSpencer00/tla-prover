# Stage 1 Brief — the repair sweep, from here to Gate 1

This file doubles as the handoff prompt for a fresh autonomous session. Everything
in it is grounded in PLAN.md (binding, incl. Amendment Log §6) and the state of the
repo at commit `639b144`. Written 2026-07-04, at Eric's direction.

## Where things stand

Gate 0 is SIGNED OFF as amended (Amendment 4, 2026-07-03): oracle closes 171/206
under the population-aware criterion, with a frozen residue list (22 open + 13
deferred) whose causes are all measured and instrument-external — see
GATE0_STATUS.md. The harness is proven (controls, tlapm/apalache wiring, append-only
ledger in results/runs/). The W1.1 repair agent is scaffolded and stub-tested:
`python3 -m harness repair --run-id <id> --specs <list> --model <name> --n <N>`
(harness/repair.py; budget schedule in corpus/configs/repair_budget.json). The W1.3
HF adapter fix is live and guarded. Zero model-API spend has occurred.

## Objective (Gate 1, from PLAN.md)

The honest model-generated ceiling on the 206, and the residue list:
- [ ] Complete 206-row matrix per method in the ledger — every spec attempted to
      full budget, pass@1 and pass@N reported separately (Rule 3).
- [ ] Residue list committed: every still-failing spec with failure class
      (parse / config / vacuous / TLC-reject / state-explosion).
- [ ] G1 status line: `oracle ∪ model` = 206/206 (system closure), model-only =
      X/206, both published.

## Eric's binding decisions (2026-07-04)

1. **Models: open-source first.** Frontier-API spend is limited; open-source
   inference is effectively unlimited (Argonne compute; generous providers like
   OpenRouter). Add an OpenAI-compatible `Model` implementation to
   harness/repair.py (base-url + key from env, e.g. `OPENROUTER_API_KEY` /
   `OPENAI_BASE_URL`) and run the sweep primarily on strong open models (e.g.
   DeepSeek/Qwen/Llama-class via OpenRouter). A small frontier-model method
   (claude, existing `AnthropicModel`) may run as a comparison arm ONLY with
   Eric's explicit go-ahead on spend — ask before any Anthropic-billed sweep.
2. **Best-of-N: 8–16. Do not skimp.** Raise `best_of_n` in repair_budget.json
   (default 8; escalate to 16 on near-misses if budget math allows). The last
   ChatTLA paper suffered hardware issues; sampling breadth is the cheap
   insurance here.
3. **No model-hosting work yet.** The eventual generator is a local model;
   chattla-20b/vLLM backends are a later work item. Do not build Sophia
   inference containers for this sweep.
4. **Bad specs: correct, disregard, or note.** Existing discipline applies —
   repair corpus defects from upstream evidence (corpus/configs/patches/ +
   PATCHES.md), or document/defer per Amendment 2. Never silently drop;
   denominator stays 206 (deferred count stated beside every number).
5. **Scope: solid plain TLA+ out of a model.** State machines first. TLAPS
   proof repair, per-obligation localizers, and other advanced topics are
   future additions — proof_module specs still get their 206-matrix rows, but
   model repair of proofs is best-effort, not a v1 goal.

## Work plan

- **W1.2a** Add the OpenAI-compatible Model implementation + tests (stub-style,
  no spend). Pick 1–2 open models as the primary methods; record exact model ids
  in every row.
- **W1.2b** Dry-run the full pipeline on ~10 diverse specs (mix of currently-
  closed and residue specs) at N=2 with the cheapest open model to validate cost
  and row integrity, then freeze the budget config (Rule: budget fixed in config
  before the sweep).
- **W1.2c** The sweep: all 206 specs × each method, `--jobs 1` verification
  discipline locally (TIMEOUT_CONTENTION.md — false timeouts under parallelism).
  Model calls may parallelize; TLC/tlapm verification must not. Expect the 7
  HPC-certified intractable specs (28/40/48/49/60/64/89) to fail verification at
  local budgets — their rows still get produced (failure class state-explosion);
  do NOT try to verify them exhaustively locally.
- **W1.2d** Gate 1 report: matrix, pass@1 vs pass@N per method, residue list by
  failure class, G1 status line. Commit everything; GATE1_STATUS.md mirrors the
  GATE0_STATUS.md style (evidence for Eric's sign-off, not self-certification).

## House rules (do not violate)

- PLAN.md Rules: append-only results ledger (Rule 8); pass@1/pass@N separated
  (Rule 3); vacuous pass = failure (Rule 5); never edit anything under
  `tla_benchmark/` or `tla-examples/`; corpus repairs go through
  corpus/configs/patches/ with documentation.
- Check for concurrent sessions before mutating the repo
  (`ps aux | grep -i "claude.*prove-TLA"`, unrecognized commits in `git log`).
- One verification job at a time on this machine; harness `--jobs 1`.
- SOPHIA access needs a one-time passcode only Eric can provide (Discord) — do
  not plan work that requires it unless he's in the loop. (Bundle pattern and
  gotchas documented in GATE0_STATUS.md "HPC sweep" and memory if needed:
  `PROVE_TLA_WORKROOT` on Lustre, `TLC_WORKERS`, ship corpus/descriptions/.)
- Spend discipline: open-model inference freely; Anthropic API only with
  explicit confirmation; report cost estimates before any sweep-scale run.
