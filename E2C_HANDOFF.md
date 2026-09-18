# E2.c Handoff — Gate-2 Baseline Measurement

**For:** a fresh agent orchestrating the completion of Stage-2 entry criterion **E2.c**.
**As of:** 2026-07-05, HEAD `f58fe8b`. **Owner sign-off:** Eric (all decisions below are ledgered + approved).

Read this top-to-bottom before touching anything. Then read `PLAN.md` §"Stage 2" and Amendment Log rows **7, 10, 11, 12** (they are the binding spec). `AUDIT.md` explains the chattla-v1 defect.

---

## 1. Where things stand

Stage-2 entry criteria (PLAN Amendment 7) gate every W2.x result. Status:

| | Status | Frozen artifact | SHA-256 | Commit |
|---|---|---|---|---|
| **E2.a** oracle frozen | ✅ DONE | `corpus/gate0_closed.json` (170 closed) | `f2288bbcb11f7281cf51f8cf995780c00fa5e24480cfc37be832ac4b437d3540` | `ec338a8` |
| **E2.b** holdout frozen | ✅ DONE | `corpus/holdout_30.json` (30 specs) | `ecfc20533b9dc9a6e727ab989732310659d469eefbcc3705df72e3094ef54f78` | `ce1dd5c` |
| **E2.c** baseline measured | ⏳ IN PROGRESS | (this doc) | — | `d53eab0`, `f58fe8b` |

**E2.c is the last gate before W2.1 can emit any tier score.** Do not start W2.1/W2.3 until E2.c's baseline is measured and frozen in the ledger.

---

## 2. Frozen invariants — DO NOT change without a PLAN amendment + Eric sign-off

These are decided and ledgered (Amendment 12). Treat as constants.

- **W1.3 = WITHDRAWN.** chattla-v1 is not faithfully loadable (self-referential `adapter_config.json`; only artifact is 373GB merged bf16 needing a custom Sophia vLLM deploy; LoRA touched q/k/v/o only, MoE experts got no gradient → merge ≈ base + noise). **Do not attempt to deploy or measure chattla-v1.**
- **Baseline = two model arms**, measured on the 30 holdout, both framings, at the frozen budget:
  - untuned **`openai/gpt-oss-20b`** (the base chattla was built on)
  - best Stage-1 prompt-only arm **`openai/gpt-oss-120b`** (Gate-1 audited ceiling 166/206)
- **Two task framings, both required:**
  - **A — NL→spec generation.** Input = FormaLLM `descriptions/{spec}.json`; model emits a complete TLA+ module; score by the Amendment-1/3 population criterion.
  - **B — repair-from-standardized-corruption.** Apply **one deterministic seeded** `harness.mutation` swap to the holdout spec's canonical text; model repairs; same criterion.
- **Frozen budget (equal for baseline and, later, chattla-v2):** temperature **0.8**, `max_tokens` **16384**, TLC verify **120s SERIAL** (`--jobs 1` — contention discipline, see `corpus/configs/TIMEOUT_CONTENTION.md`), **32 samples** for pass@32, **pass@1 = one temp-0 greedy sample**.
- **Rule 9 (semantic audit) is binding** on every counted pass — a model "pass" counts only after `harness semaudit` confirms the intended property was what got checked. Rejects ledger as failures.
- The Gate-2 checkbox now reads: *chattla-v2 beats the frozen E2.c baseline (best of the two arms) on the 30 holdout, under BOTH A and B, pass@1 AND pass@32, Rule 9 applied.*

---

## 3. Reusable building blocks (don't reinvent)

- **Model client:** `harness/repair.py` → `OpenAICompatModel` (Sophia via `OPENAI_BASE_URL` + `OPENAI_API_KEY_CMD`). `LocalStub` for zero-spend dry runs. `.generate(prompt, n, temperature, max_tokens)`.
- **Scoring machinery:** `harness/runner.py` → `check_sany`, `check_tlc`, `check_tlapm`, plus `eval_one` which applies patches/wrappers/`policy.json`/`populations.json` and the **population criterion** (state_machine: SANY∧non-vacuous TLC; library: SANY; proof_module: SANY∧all TLAPS obligations; expected_violation: SANY∧named property violated → normalized to `pass_expected_violation`).
- **Semantic audit:** `harness/semaudit.py` (`harness semaudit`), `corpus/configs/SEMAUDIT_FINDINGS.md`.
- **Mutations (Option B):** `harness/mutation.py` (`MUTATIONS`, SpecGen-style operator swaps).
- **E2.c deterministic core (already built, TDD, 5 tests green — `harness/gen_eval.py`, `harness/test_gen_eval.py`):**
  - `required_signature(cfg_text)` → identifiers a generated module must define (constants/spec/init/next/invariants/properties), so the reference `.cfg` can score generated output.
  - `extract_module(response)` → pulls `---- MODULE … ====` from a model reply (tolerates markdown fences / prose).
  - `summarize_passk(results, k)` → pass@1 (greedy) + pass@k (any-of-k) ledger summary.
- **FormaLLM corpus:** `/Users/eric/GitHub/tla_benchmark/data` — `descriptions/{n}.json` (rich structured NL), `cfg/{n}.cfg`, `tla_files/{n}.tla`, `test_split.json`. Its `src/metrics.py` is FormaLLM's own metric — **NOT used**; Gate-2 scores with prove-TLA's population criterion.
- **Endpoint auth:** the ALCF inference service takes a short-lived Globus access token. Point `OPENAI_API_KEY_CMD` at a local helper that mints one; the harness re-invokes it per call, so no token is ever written to disk here. Endpoint: `inference-api.alcf.anl.gov/resource_server/sophia/vllm/v1`. Only the **gpt-oss family is reliably hot**; expect 408/503 on cold models (harness already retries with long backoff).

---

## 4. Remaining steps (ordered) — build with TDD

Steps 1–4 are offline/testable (use `--model local-stub`, no spend). Step 5 is the compute run. Steps 6–7 close the gate.

1. **Prompt builders** (`gen_eval.py`, TDD in `test_gen_eval.py`):
   - `build_generation_prompt(description_json, cfg_text, module_name)` — NL + the required signature from `required_signature(cfg)`, instructing the model to emit one complete module defining exactly those identifiers so the reference cfg scores it. Wrap output convention so `extract_module` can recover it.
   - `build_repair_prompt(broken_module, error_evidence)` — reuse the Stage-1 repair prompt shape (spec text + SANY/TLC error head+tail + fault-localized fragment) from `repair.py`.
2. **Injected-text scorer** (the one non-trivial refactor): `runner.eval_one` currently reads the spec from `corpus/tla_files/{n}.tla`. Add a path (new function, or an optional `override_text=`/`override_cfg=` arg) that scores an **arbitrary module string** for spec `n` under the same criterion (deps, patches for deps, wrapper resolution, `populations.json`, serial TLC 120s). Keep `eval_one`'s existing corpus behavior unchanged (there are no other unit tests guarding it — add one when you touch it).
3. **Option-B corruption** (`gen_eval.py`): `corrupt(spec_text, seed)` → apply exactly one `harness.mutation` swap deterministically (seed from spec num + frozen holdout hash, mirroring E2.b's un-gameable seeding). Assert the result still SANY-parses but fails the criterion (else the "repair" task is empty). One deterministic mutation per spec, recorded.
4. **CLI + orchestration** (`harness/gen_eval.py` `main`, wired into `harness/__main__.py`): `python3 -m harness gen-eval --framing {A,B} --model openai:<id> --run-id <id> --k 32`. Per (spec, sample): build prompt → `model.generate` → `extract_module` → injected-text score → JSONL row (Rule 8 append-only: spec, framing, model id, prompt hash, sample idx, temperature, verdict, budget). Greedy sample = temp 0 recorded separately.
5. **Sophia baseline sweep** (compute — confirm with Eric before launching; ~3,960 model calls = 2 models × 2 framings × 30 specs × (1 greedy + 32)):
   - `export OPENAI_BASE_URL=…/sophia/vllm/v1 OPENAI_API_KEY_CMD=<your token-minting script>`
   - Run all four (model × framing) combinations; **serial TLC verify**; `--resume-from` for cold-endpoint restarts; quarantine 408/503-polluted rows (Stage-1 pattern).
6. **Semantic audit (Rule 9):** run `harness semaudit` over every counted pass in both framings, both arms. Rejects → failures. Ledger the rejects (`SEMAUDIT_FINDINGS.md` style).
7. **Freeze E2.c baseline:** write `results/` summary + a `corpus/e2c_baseline.json` (per arm × framing: pass@1, pass@32, audited). Record the frozen baseline in a **new PLAN ledger amendment (13)** — *before* any W2.3 training. This is the number chattla-v2 must beat.

**Acceptance:** E2.c is satisfied when the ledger carries the measured baseline (best of gpt-oss-20b / gpt-oss-120b), under BOTH A and B, pass@1 AND pass@32, Rule-9-audited, dated before W2.3.

---

## 5. Guardrails (project discipline — violations corrupt the evidence chain)

- **Append-never / sign-off files:** `gate0_closed.json`, `holdout_30.json`, and any `e2c_baseline.json` are frozen-by-hash. Corrections require a PLAN amendment + **Eric's explicit sign-off before writing**. Present evidence, get approval, then edit + re-hash + ledger. (This is how E2.a/E2.b were done — see commits.)
- **Serial TLC only** for verification (`--jobs 1`). `--jobs 8` produces contention false-timeouts that silently miscount (bit Gate 1; `TIMEOUT_CONTENTION.md`). Specs 14/30/135/141 in the holdout are near the 120s boundary — serial is not optional.
- **Rule 9 before any pass counts.** The 20b arm produced ~91 semantic-audit rejects in Gate 1 — the reward-hacking channel is live and worse for weaker models.
- **Decontamination:** W2.1 (later) MUST near-dup-remove the 30 holdout specs from `chattla-corpora-v2`. The holdout's whole value is that the model hasn't seen these.
- **No secrets in the repo.** Endpoint auth is a short-lived Globus token minted out-of-band; never commit tokens, keys, or one-time codes.
- **Concurrent-session hazard:** more than one agent or operator may be editing this repo at once. Check `git log` and the working tree before large edits.
- **Rule 3 / Rule 8:** every number carries its reproduction command; every attempt is an append-only JSONL row. Logs under `results/runs/*/logs/` are gitignored; `rows.jsonl`/`summary.csv`/`config.json` are committed as evidence.

---

## 6. After E2.c → E2 complete

With E2.a+E2.b+E2.c all ledgered, Stage 2 work opens:
- **W2.1** funnel over TLA-Extraction's 2,628 files (decontaminate against the 30 holdout) → `chattla-corpora-v2`.
- **W2.4** (proof-trace bootstrap, tlapm over corpus TLAPS + tlaplus/examples) and **W2.5** (deferred-spec archaeology, 13 specs) — CPU-only, run in parallel with W2.1.
- **W2.3** retrain on Sophia — only after the baseline is frozen and corpora-v2 exists.
Gate 2 then compares chattla-v2 against the frozen E2.c baseline.
