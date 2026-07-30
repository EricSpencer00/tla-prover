# Toy End-to-End Pipeline Smoke Test Implementation Plan

**Goal:** A single command (`tools/smoke/run_e2e.sh`) that exercises the ENTIRE ChatTLA RFT pipeline — seed → generation loop → TLC verify → corpus build → harmony SFT file → real (tiny) SFT train → merge → OpenAI-compatible serve → gen-eval → ledger re-score — locally in ~15–30 min, so config-class bugs (like the ctx-4096 truncation that invalidated Gate-2 framing B) are caught before an 8–12h Sophia run.

**Architecture:** Two tiers. **Tier L (local, this plan):** reuse the real harness modules end to end with a tiny real model (SmolLM2-135M, CPU) standing in for gpt-oss; a small OpenAI-compatible FastAPI server with a configurable `max_model_len` lets us both serve the merged toy model AND deliberately reproduce the ctx-4096 bug to prove the new preflight check catches it. **Tier S (Sophia, follow-up script only):** parameterized SMOKE=1 versions of the real PBS scripts (5 train steps, 20b, 1 GPU) — written but only run before big submissions.

**Tech Stack:** existing `harness.*` modules (w2_loop, corpus_prep, gen_eval, runner/TLC), torch+transformers+peft (CPU) in a dedicated venv, FastAPI/uvicorn stub server, TLC via tools/tla2tools.jar.

## Global Constraints

- Frozen Gate-2 scoring must NOT change: gen_eval scoring logic untouched; new checks are fail-fast preflights and post-run re-score, additive only.
- Zero Sophia/API spend in Tier L: all model calls are local (stub or tiny local model).
- Smoke artifacts go to `results/runs/smoke-e2e-*` and `tools/smoke/e2e/` — never overwrite real run dirs or `results/analysis/sft_harmony_v2.jsonl`.
- Toy train uses the same harmony jsonl format produced by `harness.corpus_prep.build_sft_file` (channel discipline is a real past failure mode — keep it in the loop).
- Everything committed to main (Eric: commit often, to main).

---

### Task 1: Smoke venv + seeds

**Files:**
- Create: `tools/smoke/e2e/requirements.txt` (torch, transformers, peft, datasets, fastapi, uvicorn)
- Create: `tools/smoke/e2e/seeds/` (2 tiny gold seed specs + cfgs copied from existing corpus data)

**Interfaces:** Produces venv at `tools/smoke/e2e/.venv` used by Tasks 3–5.

- [ ] Create requirements.txt; `python3 -m venv tools/smoke/e2e/.venv && .venv/bin/pip install -r requirements.txt` (CPU torch).
- [ ] Pick 2 small seeds (SANY+TLC pass in <10s each) from the v3-wide seed pool; verify with `harness.runner.check_sany/check_tlc`.
- [ ] Commit.

### Task 2: Stage A+B — generation loop + corpus build (pure harness, stub model)

**Files:**
- Create: `harness/smoke_e2e.py` (orchestrator, stage functions `stage_gen`, `stage_corpus`)
- Test: run inline (this IS the test)

**Interfaces:** Produces `results/runs/smoke-e2e-<date>/survivors/` and `results/runs/smoke-e2e-<date>/sft_smoke.jsonl` (harmony format).

- [ ] `stage_gen`: drive `harness.w2_loop` with a deterministic FakeModel (pattern from `harness/test_w2_loop.py`) that emits known-good tiny specs; real SANY + TLC + mutation battery gates run for real. Assert ≥1 survivor.
- [ ] `stage_corpus`: run `harness.corpus_prep.build_sft_file` over survivors → `sft_smoke.jsonl`; assert harmony channel markers (`<|channel|>final`) present in every row.
- [ ] Run both stages; commit.

### Task 3: Stage C — tiny real SFT train + merge

**Files:**
- Create: `tools/smoke/e2e/train_toy.py` (SmolLM2-135M + LoRA, ~20 steps CPU on sft_smoke.jsonl; saves adapter, merges to `merged_toy/`; prints first/last loss)

**Interfaces:** Produces `results/runs/smoke-e2e-<date>/merged_toy/` loadable by transformers.

- [ ] Write train_toy.py: load jsonl, tokenize rendered harmony text, LoRA r=8, 20 steps, assert final loss < first loss; merge_and_unload; save.
- [ ] Run it under the smoke venv; verify merged model loads and generates.
- [ ] Commit.

### Task 4: Stage D — OpenAI-compatible toy server with configurable context limit

**Files:**
- Create: `tools/smoke/e2e/serve_toy.py` (FastAPI: `/v1/models`, `/v1/chat/completions`; flags `--model-dir`, `--port`, `--max-model-len`; returns 400 when prompt+max_tokens exceed max-model-len — mirroring vLLM behavior)

**Interfaces:** Produces `http://localhost:<port>/v1` consumed by gen-eval via OPENAI_BASE_URL.

- [ ] Write serve_toy.py; also support `--canned-dir` mode that returns a known-good spec (so gen-eval can be made to PASS deterministically at least once — proves the pass-path scoring, not just fails).
- [ ] Start it; curl `/v1/chat/completions`; verify 200 and vLLM-style 400 on oversize.
- [ ] Commit.

### Task 5: Stage E — gen-eval + gate-check re-score + ctx-bug reproduction

**Files:**
- Create: `harness/gate_check.py` + `gate-check` subcommand in `harness/__main__.py` (re-score from rows.jsonl only; hard-FAIL if api_error rate >5% or any finish_reason truncation on scored rows; prints pass@k table)
- Modify: `harness/smoke_e2e.py` (stages `stage_eval`, `stage_gatecheck`, `stage_ctxbug`)

**Interfaces:** Consumes toy server URL; produces run dirs `smoke-e2e-eval-A` and `smoke-e2e-ctxbug`.

- [ ] `stage_eval`: `OPENAI_BASE_URL=http://localhost:<port>/v1 python3 -m harness gen-eval --framing A --model openai:toy --run-id smoke-e2e-eval-A --k 2 --specs <2 specs>`; assert rows.jsonl written; re-run to assert resume works (0 new calls).
- [ ] `gate-check` subcommand: recompute pass@k from rows.jsonl; FAIL on api_error/truncation thresholds; run it on the eval dir → expect PASS report.
- [ ] `stage_ctxbug`: restart server with `--max-model-len 512`; rerun gen-eval fresh run-id; `gate-check` must exit nonzero naming the api_error rate — this is the regression test for the Gate-2 framing-B disaster.
- [ ] Commit.

### Task 6: One-command wrapper + Tier-S script + docs

**Files:**
- Create: `tools/smoke/run_e2e.sh` (venv check → stages A→E → summary table, exit nonzero on any stage failure)
- Create: `tools/smoke/e2e/sophia_smoke.pbs` (Tier S: 20b, 1 GPU, 5 train steps + serve + 1-spec gen-eval; NOT run now)
- Modify: `README.md` (smoke section)

- [ ] Write run_e2e.sh; run full pipeline clean-room (delete smoke run dirs first); confirm green.
- [ ] Write sophia_smoke.pbs mirroring train_120b_real.pbs structure with SMOKE overrides.
- [ ] Update README; final commit.

## Self-Review

- Coverage: seed✓(T1) gen✓(T2) TLC✓(T2) corpus✓(T2) SFT-file✓(T2) train✓(T3) merge✓(T3) serve✓(T4) gen-eval✓(T5) ledger re-score✓(T5) ctx-bug regression✓(T5) one-command✓(T6). Gap: Sophia PBS scripts only smoke-tested by inspection (Tier S deliberately not executed — queue time is the enemy this plan exists to avoid).
- Known risk: gen-eval's holdout-30 prompts are fixed; toy model will fail them — that's fine, the smoke asserts *mechanics* (rows written, resume, scoring, error-handling), with `--canned-dir` proving the pass path.
