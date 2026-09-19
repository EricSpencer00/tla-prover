# TLA-Prover team guide

This project has one job: make it possible for a teammate to understand what a
training run did, inspect the evidence it produced, and tell a real prover
advance from a healthy machine or a better-looking proxy.

## The three surfaces

| Surface | What it is for | What it never does |
|---|---|---|
| [Research hub](../site/index.html) | A plain-language status board and links to evidence | It does not execute code or expose a shell |
| [Evidence notebook](../notebooks/tla_prover_lab.ipynb) | Live, read-only toolchain and backend probes | It does not submit, cancel, or promote jobs |
| Repository ledger | The reproducible source for runs, gates, and analysis | It does not turn an unfinished run into a claim |

The public hub publishes a snapshot. The notebook can make a fresh read-only
probe of the configured backends. A stale snapshot is labelled as stale; it is
never silently presented as live scheduler truth.

## What a training run means

A run is a bounded experiment with a hypothesis, a frozen input split, a
resource budget, and an evaluation plan. It is not just a process that consumed
GPU time.

1. **Freeze** — record the corpus, holdout, prompt framing, model identifier,
   adapter configuration, and acceptance predicate before generation.
2. **Preflight** — check dependency closure, hashes, trainable-parameter floors,
   output paths, and the expected service interface. A preflight can block a
   run; it cannot improve its score.
3. **Train** — produce a checkpoint and append its configuration and logs. Loss,
   throughput, and GPU utilization describe optimization, not proof ability.
4. **Evaluate** — generate candidates at the registered budget and run the same
   SANY/TLC/TLAPS checks used by the baseline. The holdout stays separate from
   the training corpus.
5. **Audit** — reject vacuous or semantically weakened candidates. Keep the
   rejected rows and their reason codes.
6. **Promote or quarantine** — promote only on a strict, reproducible protected
   improvement with genuine proof evidence. Everything else remains a useful
   result, a failure, or an infrastructure observation.

## Status vocabulary

- **Running**: a process is active. No capability claim follows.
- **Preflight passed**: the requested inputs and guards are ready. No model
  claim follows.
- **Measured**: the registered evaluation completed and its rows are in the
  ledger.
- **Audited**: semantic and integrity checks were applied to the measured rows.
- **Promoted**: the protected acceptance rule improved and the evidence is
  reproducible.
- **Quarantined**: the artifact is retained but excluded from claims because a
  guard, comparison, or provenance condition failed.

## The protected boundary

The protected gate is the only promotion metric. Current public status is
**0/119** for the Stage 3 TLAPS prover target. The following are deliberately
not substitutes for that number:

- lower training loss;
- more generated samples;
- a reachable Polaris or Sophia login;
- a healthy TLAKit endpoint;
- a SANY-only parse pass;
- a completed scheduler job;
- an optimizer preference or a hand-picked example.

The browser workbench demonstrates a real SANY check on a self-contained module.
It is a toolchain demonstration, not a prover score.

## How teammates should use the suite

Start at the research hub. Read the current claim boundary and the run board,
then open the linked ledger or plan entry. Use the password-protected notebook
when you need a fresh backend/process view or want to repeat the harmless
toolchain smoke check. If a run is interesting, inspect its `config.json`,
`rows.jsonl`, summary, and audit artifacts together; never quote a headline
number without its denominator and verification stage.

The notebook and hub intentionally have no job-submission control. Compute
actions belong in the existing scheduler/run workflow, where a separate
preflight and append-only ledger entry can be reviewed.
