# Bounded offline local model pilot — 2026-09-05

Completed in **31.47 seconds**, below the 180-second wall-clock cap. This is a
tiny-model pipeline pilot, **not evidence about 120B quality**. Both selected
specs remained unsolved. No downloads, credentials, or external writes were used.

## Implementation and reproduction

```sh
cd /Users/eric/GitHub/prove-TLA
tools/smoke/e2e/.venv/bin/python -B tools/local_sany_pilot.py
```

The script creates a unique results directory on every invocation. It loads
cached `Qwen/Qwen2.5-0.5B-Instruct` weights with `local_files_only=True`, disables
Hub/Transformers network resolution, and disables remote model code. Missing
weights cause a recorded worker failure; no download fallback exists.

The parent process bounds model loading, generation, and verification together
to 180 seconds and kills the worker process group on timeout. Partial artifacts
remain available. The process exit status denotes execution completion, not
model quality; consult verdicts and the ledger summary for quality.

Actual Transformers generation uses MPS when available, otherwise CPU, float32,
four CPU threads, 512 output tokens maximum, and the harness-derived seed.
One chain and two rounds run sequentially for fixed holdout specs `2` and `5`.
The first round is greedy; the second uses the harness temperature of 0.8.
Full prompts are passed through the tokenizer's chat template without truncation.
No canonical answer is substituted and no generated text is repaired by this script.

The script inspects `run_loop_eval` for a `model` parameter. The version used in
this run lacked it, so a scoped in-process replacement of `make_model` supplied
the custom `Model`; no harness files were edited. `MAX_TOKENS` is scoped to 512
so the harness config records the actual pilot budget. SANY/TLC/TLAPS scoring,
timeouts, extraction, nonvacuity checks, and ledger gates remain unchanged.

## Observed results

Run: `results/runs/local-sany-pilot-20260905-113312-6814b438`

Cached snapshot: `7ae557604adf67be50417f59c2c2f167def9a775`.
Backend: MPS, float32, torch 2.13.0, transformers 5.14.1.

| Spec | Round | Output tokens | Generation seconds | Verdict |
| --- | --- | ---: | ---: | --- |
| 2 | 0 | 75 | 4.087 | no_module_extracted |
| 2 | 1 | 512 | 12.348 | no_module_extracted |
| 5 | 0 | 318 | 7.472 | no_module_extracted |
| 5 | 1 | 85 | 2.271 | no_module_extracted |

Four real model calls completed; **0/2 specs solved**. One output hit the token
cap. The first reply imitated configuration syntax inside a module and ended
with `---- END MODULE ACP_NB ----`, rather than a valid TLA+ module terminator.
All four replies failed the existing extractor. Consequently **SANY, TLC, and
nonvacuity verification were not exercised** by these generations. No verifier
success or feedback-repair success can be claimed. Round two regenerated from
the original prompt under the existing no-extraction behavior.

Every raw reply is preserved verbatim in `candidates/*.response.txt`, including
all extraction failures. `generations.jsonl` additionally preserves raw replies,
original and chat-rendered prompts, output token IDs, token counts, seeds,
generation parameters and timings. `rows.jsonl`, `summary.json`, `config.json`,
`backend.json`, `injection.json`, `console.log`, and `pilot.json` capture the
ledger and execution context. Seed recording does not promise bitwise
reproducibility across hardware or runtime versions.

## Verification and limits

- Script syntax parsed successfully.
- Actual offline run completed with exit code zero and four ledger rows.
- An independent artifact audit passed: exact spec/round coverage, derived seeds,
  prompt hashes, raw artifact equality, output token cap, extraction verdicts,
  and zero-solved ledger summary all agree.
- Existing `harness.test_loop_eval` and `harness.test_decoding` suites could not
  import because this runtime lacks `pytest`. No dependency installation was
  attempted. The timeout kill path and CPU fallback were not exercised.
- Transformers emitted a deprecated `torch_dtype` warning and a warning about
  sampling-only `top_k` on greedy generation; these did not stop generation.

Only the new pilot script, this document, and the unique run artifacts are owned
by this work. Concurrent deterministic fixes/replay and other-agent diagnostics
remain separate. The user reports main replay results of 8 samples, 5 SANY
passes, and 1 repaired TLC-clean result (diagnostic, not frozen), plus tested
preflight concurrency 8. Those are user-reported results, not verified or
attributed to this tiny-model pilot.

## Experimental extraction-feedback run

After the main agent's opt-in `TLA_LOOP_EXTRACTION_FEEDBACK` patch was ready,
the pilot gained `--extraction-feedback`. It explicitly sets the worker flag to
`1` when requested and `0` otherwise, before importing the harness; an inherited
environment flag cannot silently enable the default pilot. The parent forwards
the option and records `extraction_feedback` in `pilot.json`. The original run
and its artifacts are unchanged. This is an experimental separate run, not a
frozen evaluation change.

```sh
tools/smoke/e2e/.venv/bin/python -B tools/local_sany_pilot.py --extraction-feedback --timeout 180
```

Run: `results/runs/local-sany-pilot-20260905-113800-30d79543`.
Completed in **23.20 seconds**, exit code zero, no timeout, four actual model
calls, **0/2 specs solved**. The same cached model, MPS backend, specs, chain and
round counts, and 512-token output cap were used. No downloads were performed.

| Spec | Round | Output tokens | Generation seconds | Input rung | Verdict |
| --- | --- | ---: | ---: | --- | --- |
| 2 | 0 | 75 | 2.140 | generate | no_module_extracted |
| 2 | 1 | 75 | 1.864 | extraction | no_module_extracted |
| 5 | 0 | 318 | 7.523 | generate | no_module_extracted |
| 5 | 1 | 318 | 7.916 | extraction | no_module_extracted |

Both second-round prompts contain the extraction-feedback section and previous
response excerpt. The model nevertheless repeated its first-round reply verbatim
for each spec. All raw replies remain in `candidates/*.response.txt` and
`generations.jsonl`. No output hit the token cap in this run. SANY/TLC and
nonvacuity verification were again not reached; their gates were not weakened.

Verification passed for script syntax and CLI help, option reporting, both
second-round feedback prompts and ledger rungs, all raw artifact equality,
derived seeds, prompt hashes, output caps, and extraction verdicts. This checks
that feedback reached actual generation, but shows no quality improvement on
these two specs. Unique run IDs change sampled-round seeds, so this is not a
controlled estimate of the feedback effect or evidence about a 120B model.
