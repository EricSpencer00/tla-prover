# The dense-vs-MoE "capacity gap": what it is, and why closing it is the wrong move

Investigation date 2026-08-04. Read-only; no cluster jobs, no tracked files changed.
Ground truth: ChatTLA at `6427de9` (`land/lora-resolver-onto-main` == `origin/main`),
PEFT **0.19.1** source in `/Users/eric/GitHub/ChatTLA/ChatTLA/.venv311-repair/lib/python3.11/site-packages/peft/`,
and the two published `config.json`s (`Qwen/Qwen3.6-27B`, `openai/gpt-oss-20b`).

**Bottom line: the gap is not a confound and should not be closed. It is an exact,
derivable consequence of the fact that one model has 32× more FFN matrices than the
other, measured at a rank that is already identical in both arms. The right move is to
reframe the comparison as equal-budget best-vs-best on a dev split, and to retire the
capacity worry empirically — by measuring each arm's sensitivity to rank — rather than
by nulling it out with a deliberately mis-specified config.**

---

## 0. First: the two numbers are now fully derived, not just observed

Both arms' trainable-parameter counts reproduce to the digit from architecture +
PEFT source. This matters because every recommendation below is arithmetic on those
derivations, and because it retires any residual doubt that the 2026-08-03 measurement
was itself an artifact.

### PEFT semantics, verified in source (not from memory)

| Claim | Verified at |
|---|---|
| `"all-linear"` expands to every `nn.Linear` and `Conv1D` in the model, **minus the output-embedding head** | `peft/tuners/tuners_utils.py:1891-1939` (`_maybe_include_all_linear_layers`); provenance comment cites the QLoRA repo |
| A targeted `nn.Linear` contributes `r*(in+out)` trainable params | `lora/layer.py` `update_layer`: `lora_A = nn.Linear(in_features, r)`, `lora_B = nn.Linear(r, out_features)` |
| A targeted **3D packed** param (`target_parameters`) contributes `r*E*(in+out)`, i.e. **rank r per expert, E experts** | `lora/layer.py:2221-2222`: `lora_A = nn.Linear(in_features, r*num_experts)`, `lora_B = nn.Linear(r*num_experts, out_features)`; `num_experts` set at `:2166-2177` |
| Each expert really gets its own independent rank-`r` slice (no cross-expert mixing) | `lora/layer.py:2304-2307`: `einsum("o r e, e r i -> e o i", weight_B, weight_A)` |
| Effective scale is `alpha / r` (`alpha / sqrt(r)` iff `use_rslora`) | `lora/layer.py:212-215`, `:1096-1099`, `:1435-1438`, `:2225-2228` |
| Two `target_parameters` on the *same* module work by **nesting** `ParamWrapper`s (the class docstring's "not implemented" caveat is stale for 0.19.1) | `lora/model.py:249-250` |
| A `target_parameters` miss is `warnings.warn(..., RuntimeWarning)`, **not** an exception, whenever `target_modules` matched something | `tuners_utils.py:1039-1043` — this is the mechanism of the original silent freeze |
| `rank_pattern` / `alpha_pattern` **do** apply to `target_parameters`, because the pattern is matched against the full param path | `lora/model.py:205-208` + `current_key` = `"...mlp.experts.gate_up_proj"` (`tuners_utils.py:1105-1140`); matcher is a suffix regex, `utils/other.py:1435-1443` |
| `ParamWrapper` **forbids** `lora_dropout != 0`, `use_dora`, `lora_bias`, `fan_in_fan_out` | `lora/layer.py:2139-2150`, `:2210-2213` |
| `exclude_modules` exists on `LoraConfig` | `lora/config.py:481` |

### gpt-oss-20b (MoE), r=8 — exact

Config: 24 layers, hidden 2880, expert intermediate 2880, 32 local experts (top-4),
64 heads / 8 KV / head_dim 64.

```
attention  sum(in+out) over q,k,v,o per layer = 20,736 ; x24 layers  =    497,664
experts    E * [(2880+5760) + (2880+2880)]    = 460,800 ; x24 layers  = 11,059,200
trainable(r) = r * 11,556,864
r=8 -> 92,454,912   <-- matches the measured 92,454,912 exactly
```

Tensor count also checks: 24·(4 modules·2) = 192 attention tensors + 24·(2 params·2) = 96
expert tensors = **288 total, 96 expert** — exactly as job 170815 reported.

Composition at r=8: **95.7% of trainable params are expert LoRA; 4.3% is attention.**

### Qwen3.6-27B (dense), r=8 — exact

The published config is `Qwen3_5ForConditionalGeneration`: a **multimodal, hybrid
linear-attention** model. Text side: 64 layers, hidden 5120, intermediate 17408,
`full_attention_interval: 4` → 16 full-attention + 48 linear-attention layers,
`attn_output_gate: true` (so `q_proj` is double width, 12288), vocab 248320.
It also ships a 27-block vision tower and a 1-layer MTP head.

From the real `model.safetensors.index.json`, the `nn.Linear` inventory of the text
model is: 48×{`in_proj_qkv`, `in_proj_z`, `in_proj_a`, `in_proj_b`, `out_proj`} +
16×{q,k,v,o} + 64×{gate,up,down} = **496 modules**.

```
full attention (16 layers)  sum(in+out) =   655,360   ( 9.0%)
linear attention (48)                   = 2,314,752   (31.7%)
MLP (64)                                = 4,325,376   (59.3%)
                            TOTAL S     = 7,295,488
trainable(r) = r * 7,295,488
r=8 -> 58,363,904   <-- matches the measured 58,363,904 exactly
992 LoRA tensors = 2 x 496 modules   <-- matches exactly
```

Independent cross-check on the *total*: base = 26,954,362,368 − 58,363,904 =
26,895,998,464, and summing the text-only architecture from config gives
**26,895,998,464** to the byte (including `A_log`/`dt_bias`, 4,608 params).

**Two consequences of that exact match, both new:**

1. **`AutoModelForCausalLM` loads the text model only** — the vision tower (~0.6B) and
   the MTP head are absent. Confirmed by the byte-exact total. This is fortunate:
   had they loaded, `"all-linear"` would have adapted 27 vision blocks
   (`visual.blocks.N.attn.qkv/proj`, `mlp.linear_fc1/fc2`) plus the merger — ~110
   modules of capacity spent on a modality this project never uses, inflating the
   trainable count with parameters that cannot possibly help TLA+. This is a latent
   trap: any change to the load path (e.g. `AutoModelForVision2Seq`,
   `AutoModelForImageTextToText`, or a transformers version bump that re-points the
   Auto mapping) silently re-introduces it, and the 0.1% floor would happily pass it.
   **Recommendation: add `exclude_modules=["visual\\..*", "mtp\\..*"]` to the dense
   resolver path now**, as a load-path-independent guard.
2. `"all-linear"` reached the *linear-attention* projections, which is 31.7% of the
   dense arm's capacity. The existing `_FFN_NAME_HINTS` list in `lora_resolver.py:42-46`
   would *not* recognise `in_proj_qkv` / `out_proj` as FFN — so `is_attention_only()`
   correctly returns `False` for a list containing them only by accident (they contain
   no hint, so a hypothetical yaml naming only linear-attn modules would be
   misclassified as attention-only and silently overridden to `"all-linear"`). Benign
   today because the dense path is `"all-linear"` anyway. Worth a comment, not a fix.

---

## 1. What the "gap" actually is

`trainable(r)` is **exactly linear in r for both arms**. So the entire 1.584×
absolute gap and 2.03× fractional gap is one number:

```
92,454,912 / 58,363,904 = 1.58412      (absolute, both at r=8)
0.4401%    / 0.2165%    = 2.0328       (fraction of total params)
```

and that number decomposes cleanly:

- **The rank is already matched.** Both arms are r=8, alpha=16, `alpha/r = 2.0`, dropout 0.
  Every matrix either arm adapts gets a rank-8 update. There is no per-matrix
  capacity asymmetry to fix.
- **The MoE arm has more matrices.** gpt-oss has 32 FFN matrix-pairs per layer where
  Qwen has one. PEFT gives each expert its own rank-8 adapter
  (`lora/layer.py:2221`, verified above). 32 × rank-8 = 32× the parameters at
  identical per-matrix expressivity.
- **The denominators differ for an unrelated reason.** 27.0B vs 21.0B, from different
  depth/width/vocab choices. The *fraction* gap (2.03×) is the absolute gap (1.58×)
  times the inverse size ratio (1.28×) — i.e. a third of the fractional gap is pure
  denominator artifact and has nothing to do with adapters at all.

So the honest statement is: **there is no bug and no confound here. The measurement is
telling you what MoE is.** Job 170815's own writeup calls this "the arms do not have
equal capacity", which is true but frames a structural property as a defect.

There is one further asymmetry that no scalar match can fix, and it cuts the other way:

- **Gradient signal per parameter is ~8× lower in the MoE arm.** Each token routes to
  4 of 32 experts, so each expert-LoRA tensor receives gradient from ~1/8 of the tokens.
  Active LoRA params per token in the MoE arm = 3,981,312 (attention, always active) +
  11,059,200 × 4/32 = **15,040,512**, against 58,363,904 for the dense arm — the MoE arm
  is *under*-parameterised per gradient step by 3.9× at the same nominal r=8.

Matching total parameter count would therefore *worsen* the mismatch in
parameters-per-update while "fixing" the mismatch in parameters-per-model. There is no
single scalar for which matching is neutral. That is the core reason the premise should
be rejected.

---

## 2. If you insisted on equalizing: the exact numbers, and the sacrifice

All of this follows from `trainable(r) = r·S` with `S_dense = 7,295,488`,
`S_moe = 11,556,864`. `alpha` must move with `r` to hold the effective scale
(`scaling = alpha/r`, verified at `lora/layer.py:215`) — so `alpha = 2r` throughout.

| Target | Config | Trainable | Fraction | Error vs target |
|---|---|---|---|---|
| **equal absolute count**, raise dense | dense r=13 α=26 vs MoE r=8 α=16 | 94,841,344 vs 92,454,912 | 0.3514% vs 0.4401% | **+2.6%** |
| equal absolute count, raise dense (alt) | dense r=12 α=24 vs MoE r=8 | 87,545,856 vs 92,454,912 | 0.3244% vs 0.4401% | −5.3% |
| **equal absolute count**, cut MoE | dense r=8 α=16 vs MoE r=5 α=10 | 58,363,904 vs 57,784,320 | 0.2165% vs 0.2755% | **−1.0%** |
| **equal fraction of total** | dense r=16 α=32 vs MoE r=8 α=16 | 116,727,808 vs 92,454,912 | 0.4321% vs 0.4401% | **−1.8%** |
| equal rank per adapted matrix | dense r=8 vs MoE r=8 — **already the case** | 58,363,904 vs 92,454,912 | 0.2165% vs 0.4401% | 0 |
| equal active-params-per-token | dense r≈2 vs MoE r=8 | ~14.6M vs 15.0M | 0.054% — **trips the floor** | — |

Which sacrifice is right, if you must choose one:

- **`target_modules`/`target_parameters` must not change.** They are already the correct,
  architecture-resolved coverage. Anything else re-introduces the freeze class of bug.
- **Do not cut MoE to r=5.** 95.7% of that arm's capacity is experts, so lowering `r`
  to hit a count target *also* drops its attention adapters from rank 8 to rank 5 — the
  one component that is genuinely apples-to-apples between the arms. You would degrade
  the comparable part to equalize the incomparable part, and you would owe a defence
  that the loser wasn't simply crippled.
- **If a matched leg is needed, raise the dense arm: dense r=13, α=26.** Raising rank on
  a dense LoRA is a monotone-capacity direction at this scale and within a 2-epoch cap,
  so if the MoE arm still loses at matched count you have an *a fortiori* result rather
  than a handicap argument. The unavoidable sacrifice: the dense arm is then no longer
  at its own selected config, and `alpha/r` fidelity across ranks is itself contested
  (see rsLoRA note below).
- **`r=16 / r=8` is the fraction-matched pair** (0.4321% vs 0.4401%, 1.8%). Convenient,
  because a `r ∈ {8,16}` sweep on the dense arm — which you want anyway (§5, Stage 2) —
  *contains* the fraction-matched cell for free. You get the matched-capacity
  comparison as a by-product without designing the study around it.

### Effect on the 0.1% floor in `lora_resolver.py`

No configuration proposed anywhere in this document trips `TRAINABLE_FLOOR_PCT = 0.1`:

| config | fraction | headroom over floor |
|---|---|---|
| dense r=4 | 0.1084% | **1.08×** — effectively at the floor |
| dense r=8 | 0.2165% | 2.17× |
| dense r=13 | 0.3514% | 3.51× |
| dense r=16 | 0.4321% | 4.32× |
| MoE r=5 | 0.2755% | 2.76× |
| MoE r=8 | 0.4401% | 4.40× |
| MoE r=16 | 0.8764% | 8.76× |

But the floor is the wrong shape for this job and the table shows why: it is a fraction,
so it moves with `r` *and* with model size, while the thing it exists to catch — "the
selector matched nothing" — is a **coverage** property independent of both. At dense r=4
the floor is one refactor away from a spurious abort, and (per §0) a vision-tower-loaded
Qwen would sail past it while wasting a fifth of its capacity.

Recommended shape, r-independent (do not implement yet — see Stage 0):

1. Keep `TRAINABLE_FLOOR_PCT = 0.1` as a cheap backstop. It has earned its place.
2. Add an **expected-count assertion**: compute `expected = r · Σ(in+out)` over the
   modules/params the resolver claims to have targeted, and require
   `actual == expected`. This is derivable from parameter metadata alone (same property
   `report_coverage` already relies on), catches partial attachment, and does not move
   when `r` moves.
3. Add **architecture-derived exact tensor counts**: MoE requires
   `expert_tensors == 4 · num_hidden_layers` (gpt-oss-20b: 96 ✓; gpt-oss-120b: 144 ✓ per
   `9fd653f`); dense requires `targeted_modules == (#nn.Linear − 1)` after
   `exclude_modules`. `preflight_120b.py:68,80` already does the weaker version of both —
   promote it into `report_coverage` so it runs on every job, not just preflight.

### alpha, and the rsLoRA temptation

`scaling = alpha/r` is confirmed in source. So holding `alpha/r = 2.0` across ranks is
what keeps the *initial update scale* fixed, and that is what `alpha = 2r` above does.
[Kalajdzievski 2023](https://arxiv.org/pdf/2312.03732) argues this under-scales as `r`
grows and that `alpha/sqrt(r)` is the gradient-stable choice, which is precisely the
regime a cross-rank comparison lives in. **Do not enable `use_rslora` here anyway**, for
three concrete reasons: (a) at r=8 it would change the gpt-oss scale from 2.0 to 5.66, a
2.8× larger update, which is the direction that makes the known entropy collapse
(1.720 → 0.685) *worse*; (b) it would invalidate the transfer of the 2-epoch / 0.68-floor
parameter, which is the one durable result this project has; (c) PEFT itself warns that
`use_rslora` combined with `rank_pattern`/`alpha_pattern` breaks merge-back into base
weights (`lora/config.py:854-871`). Note this as a known limitation of any cross-rank leg
rather than fixing it — and observe that the recommendation in §4 avoids cross-rank
comparison in the primary contrast entirely, which dissolves the issue.

### Arm-asymmetric constraints you cannot design around

`ParamWrapper` forbids `lora_dropout != 0`, `use_dora`, and `lora_bias`
(`lora/layer.py:2139-2150`). So the MoE arm **can never** use dropout or DoRA. Any
hyperparameter grid containing those knobs is unrunnable on one arm. This retroactively
justifies `lora_dropout: 0.0` in `lora_config.yaml` on grounds independent of the
gradient-checkpointing reason recorded there, and it bounds what "tune each arm to its
best" can mean: the searchable space is `{r, lr, epochs, schedule}`, matched, and nothing
adapter-structural.

---

## 3. What is legitimately comparable across arms

The good news is that this harness is already built the right way: **every primary metric
is computed by running Java (SANY / TLC / tlapm) over generated text.** None of it touches
a tokenizer, a logit, or a chat template. That makes the whole verifier layer valid across
arms by construction.

**Valid across arms** (all in `/Users/eric/GitHub/ChatTLA/ChatTLA/src/validators/`):

| Metric | Where |
|---|---|
| SANY parse rate | `sany_validator.py:42,88` |
| TLC tier (gold/silver/bronze), clean-pass rate | `tlc_validator.py:219-226` |
| Diamond rate = `distinct_states>1 ∧ ¬trivial_invariant ∧ invariants_checked>0 ∧ mutation_caught` | `tlc_validator.py:77-96` |
| Mutation kill rate (invariant is load-bearing) | `tlc_validator.py:460,525` |
| `partial_credit ∈ [0,1]` from 6 sub-verdicts | `component_validator.py`, wired at `tlc_validator.py:558` |
| `distinct_states`, `action_coverage`, `tlc_depth1_ok`, `module_mismatch_rate` | `tlc_validator.py:379-448`, `scripts/eval_diamond_holdout.py:37,176` |
| TLAPS `obligations_proved/total`, `parse_rate`, `full_proved` | `tlaps_validator.py` |

**Invalid across arms — never put these in a comparison table:** per-token loss,
per-token entropy, token accuracy, perplexity, grad norms, anything per-optimizer-step,
and **any length- or token-normalised quantity** (different tokenizers ⇒ "tokens to first
valid spec" and tokens-per-spec are unit-mismatched; use characters or AST node counts if
a length control is needed). Job 170815's `loss 1.641→1.033` vs `1.952→1.467` and
`entropy 0.654` vs `1.75` are in this category, as its own §"What this does NOT license"
already says.

**The bridge that makes the entropy finding usable.** The known-real gpt-oss result —
entropy 1.720→0.685 (−60%) in 64 steps, and v2_sft2 failing a gate at 0.547 — is a
*within-arm* observation that cannot be compared to Qwen's number. But its predicted
downstream consequence *is* tokenizer-independent: diversity collapse shows up as **loss
of pass@k gain**, which is exactly the W2.6 signature (+1 pass@1 / −8 pass@4). So:

> `pass@8 − pass@1` on the verifier metric, plus the count of *distinct* valid specs
> among k samples (canonicalised AST dedup, not string dedup), is the legitimate
> cross-arm operationalisation of the entropy-collapse hypothesis.

That is worth stating explicitly, because it converts the project's single most solid
finding from "an unusable within-arm curve" into a pre-registerable cross-arm endpoint.

**Semantic audit.** `scripts/diamond_curate.py:205-401` has the 5-dimension rubric
(`semantic_fidelity`, `invariant_quality`, `completeness`, `tla_idiom`, `training_value`,
1–5 each). It is currently a *data-curation* filter and no eval driver consumes it. If it
becomes an eval metric it must be: arm labels stripped, sample order randomised, judge
model from neither family under test, and the rubric frozen before any generation. Note it
is run out-of-process by subagents (`export_judge_prompts:330`), so blinding is a
mechanical change to the prompt batcher, not a new system.

### The minimum valid measurement — and its power limit

Pre-registered (`PLAN.md:558-560`): frozen 30-spec holdout, pass@1 **and** pass@k,
semantic-audited, both arms reported separately. Minimum to make that valid:

1. **Hash-pin the holdout before any generation.**
   `data/processed/diamond_eval_holdout.jsonl` (30 rows, verified) has **no** `.summary.json`
   and **no** checksum, unlike `sany_tlc_pass_eval_v1.jsonl` which carries
   `jsonl_sha256: 6c0da974d2…`. Worse, the source it was carved from
   (`outputs/diamond_gen/diamond_generated.jsonl`, per `carve_diamond_holdout.py:27`) is
   **absent from the worktree**, so the split is not currently re-derivable. The 30-row
   file is the artifact of record and must be hashed as-is.
2. **Identical decode settings, both arms, k ≥ 8, fixed seeds.** Present harness uses
   `temperature=0.05` (`src/inference/ollama_client.py:181,222-226`) with **no seed set** —
   near-greedy and irreproducible. At T=0.05 pass@8 ≈ pass@1 and the diversity signal,
   which is the whole point, is destroyed. Needs a T≈0.8 sampling path with seeds 1..k
   plus a separate greedy pass@1 leg.
3. **No self-correction in the primary metric.** The 3-retry loops
   (`eval_3shot_tlc_tlaps.py:37`, `eval_diamond_holdout.py:237`) confound base-model
   capability with verifier-feedback-following. Run as a pre-declared secondary.
4. **pass@k does not exist and must be written.** Grepped for `pass@`, `pass_at`,
   `comb(`, `binom` across `scripts/` and `src/` — zero hits. `benchmark.py --attempts`
   is best-of-N with early break on gold, a *different* quantity. Use the standard
   unbiased estimator (Chen et al. 2021, Codex paper).
5. **Report the power limit, and pre-register the tie rule.** n=30 with a measured
   baseline diamond rate of 0.10 (`outputs/eval/holdout_v13_baseline.json`: 3/30). Paired
   McNemar over the same 30 specs: a 6-spec one-directional swing gives exact p ≈ 0.031;
   a 2–3 spec swing is indistinguishable from noise. **The frozen holdout can only resolve
   differences of ≳6 specs (20 points). Anything smaller is a tie and must be reported as
   a tie**, with the choice then falling to declared secondary criteria (throughput —
   the MoE arm is 3.6× faster per step; 40GB fit; license) rather than to a
   post-hoc reading of a null result. Add mean `partial_credit` (continuous, 6
   sub-verdicts, far more power at n=30) as a **pre-declared secondary** so it cannot be
   swapped into the primary slot after the fact.

Because of (5), **selection must not happen on the frozen 30.** Use a disjoint dev set
for choosing and keep the 30 for confirmation: `data/frs_tla_ralph_gen/dev.jsonl` (50) +
`data/benchmarks/benchmark_suite.json` (20, independently hand-crafted) = **70 items**.
Verify disjointness against the holdout modules before use.

---

## 4. The reframe: this is a model choice, not an architecture experiment

This is the load-bearing argument, so it is worth being blunt about the estimand.

**What the project needs to decide:** *which base model, fine-tuned as well as we can
afford to fine-tune it, produces the most SANY/TLC-passing, semantically-sound TLA+ per
unit of compute we will actually spend?*

**What capacity-matching answers:** *holding adapter capacity fixed, which architecture
family adapts better?*

These are different questions, and the second one is not answerable by this experiment
under any matching scheme, because **n = 1 model per arm**. Qwen3.6-27B vs gpt-oss-20b
differ in: architecture (dense-hybrid vs MoE), pretraining corpus, tokenizer (248,320 vs
201,088 vocab), chat format (chatml vs harmony), post-training recipe, parameter count,
attention mechanism (Qwen is 48/64 layers *linear* attention — a hybrid recurrent model,
not a standard dense transformer), and multimodality. Equalizing trainable parameters
nulls **one** of eight nuisance variables while leaving seven, and buys the *appearance*
of control — which, given that this project already retracted one comparison for exactly
that appearance, is the specific failure mode to avoid. A capacity-matched table would
read as more controlled than it is. That is worse than an openly uncontrolled one.

The literature norm cited for matched budgets does not transfer, and it is worth being
precise about why. The convention of aligning trainable-parameter *ratios* — LoRA r=8 at
0.47%, DoRA 0.38%, AdaLoRA avg-rank-7 0.40%, etc.
([FinLoRA](https://arxiv.org/pdf/2505.19819)) — exists for comparing **PEFT methods on a
fixed base model**, where the base is held constant and only adapter *structure* varies.
Here the adapter method is fixed and the **base model is the variable**: the roles are
exactly inverted, and the convention says nothing about this case. The same literature
also supplies the counter-warning directly: matched budgets do not imply matched
behaviour, and identical parameter counts organised as different structures can produce
opposite outcomes
([CP tensor adapters](https://arxiv.org/pdf/2606.00428),
[LoRA rank/target-module controlled study](https://arxiv.org/html/2607.25583v1)).

**So: do not close the gap. Reframe.**

The defensible design is **equal-budget best-of-arm**, which is neither "match capacity"
nor naive "best-vs-best":

1. Give each arm an **identical, pre-registered tuning budget** — same number of runs,
   same grid *expressed in arm-relative terms* (`r ∈ {8, 16}`, `alpha = 2r`, everything
   else fixed). This defuses the obvious objection to best-vs-best, which is that
   whichever arm you tuned harder wins.
2. Select each arm's config on the **dev split** (70 items) using a verifier-grounded
   metric. Frozen 30 never touched.
3. Compare the two winners **once** on the frozen 30, both arms reported separately,
   pass@1 + pass@8, blinded semantic audit.
4. Report the capacity numbers (58.4M / 0.2165% vs 92.5M / 0.4401%, or whatever the
   selected configs give) as **descriptive metadata in the methods section, not as a
   control**. Say plainly that per-matrix rank is matched and total count is not, and why.
5. Frame every claim as **"gpt-oss-20b-as-we-can-train-it vs Qwen3.6-27B-as-we-can-train-it"**.
   Never write "dense beats MoE" or vice versa; n=1 per family cannot support it.

**And retire the capacity worry empirically rather than by construction.** The `r ∈ {8,16}`
sweep in step 1 measures each arm's **sensitivity to capacity** on the dev set. That is
strictly more informative than a matched pair:

- If dense r=8 → r=16 (a 2× capacity change, spanning and exceeding the entire 1.58× gap)
  moves the dev metric by **less** than the between-arm difference, then capacity cannot
  explain the between-arm difference, and no matched leg is needed. The confound is
  retired *by measurement*.
- If it moves by **more**, capacity dominates, the base-model question is not resolvable
  at this budget, and you have learned that before spending the reserved run — which is
  worth more than a matched number would have been.
- And the sweep incidentally contains the fraction-matched cell (dense r=16 = 0.4321% ≈
  MoE r=8 = 0.4401%), so the matched comparison is available for free if a reviewer asks.

Keep one conditional leg, pre-registered by *sign of result*, so it cannot be a post-hoc
rescue: **if the MoE arm wins**, run dense r=13 α=26 (94.8M, +2.6% over MoE's 92.5M) to
rule out "it just had more knobs." If the **dense arm wins at r=8**, it won with 37% fewer
trainable parameters and 58.4M vs 92.5M is an *a fortiori* argument in its favour — no
extra leg needed. Cost of the conditional leg: ~4.5 node-hours.

---

## 5. Prioritized run plan

Cost model, from job 170815's measured 52.0 s/step (dense) and 14.5 s/step (MoE) at
4 procs × batch 1 × accum 8 (global batch 32). At the ~5,000-row cross-family corpus
(PLAN.md Amendment 20 floor): 157 steps/epoch, **314 steps at the 2-epoch cap**.

| | steps | wall | node-hours |
|---|---|---|---|
| dense train, 2 epochs | 314 | 4.54 h | **4.54** |
| MoE train, 2 epochs | 314 | 1.26 h | **1.26** |

**The headline: GPU budget is not the constraint.** The entire plan below is ~35 node-hours
against ~1,900 available — under 2%. The binding constraints are (a) the one-shot
credibility of the reserved run, and (b) Stage 0 harness gaps, one of which would silently
invalidate the MoE arm at *eval* time. Plan accordingly: spend generously on Stage 0 and
Stage 2, and treat "we can't afford the control" as a non-argument.

### Stage 0 — harness fixes. No cluster. Blocks everything. (~1–2 days)

**0a. `merge_lora.py` silently discards every MoE expert adapter. Fix first.**
`src/training/merge_lora.py:106-111` loads the base with only `torch_dtype`/`device_map`/
`trust_remote_code` — **no `Mxfp4Config(dequantize=True)`** (`grep 'Mxfp4\|dequantize'`
returns nothing), while `train.py:256` does pass it. Per `lora_config.yaml:41-50`, without
dequantize the experts remain packed as `gate_up_proj_blocks`/`_scales` and are
unmatchable by name, so PEFT emits `"target_parameters … no parameter matched"` — a
`RuntimeWarning`, verified at `tuners_utils.py:1039-1043` — and drops all 96 expert
tensors. **Exit code 0.** This is the *identical bug class* that `land/lora-resolver-onto-main`
just fixed on the training side, still live on the eval side: it would evaluate the MoE
arm as attention-only (4.3% of its adapter) and hand back a "gpt-oss is bad at TLA+"
result. `scripts/eval_prover_checkpoint.py:67-72` has the same omission. Add the
dequantize config, plus a post-merge assertion that merged weights differ from base and
that the adapter's declared `target_parameters` all attached. PEFT itself is not the
blocker — `ParamWrapper.merge` at `lora/layer.py:2379` and recursive unload at `:2430`
handle packed 3D correctly once the params are visible.

**0b. Write the pass@k sampler + unbiased estimator.** Does not exist (§3.4).

**0c. Seed and parameterise decode.** `ollama_client.py:222-226` sets no seed; add one,
and add a T≈0.8 sampling path for pass@k alongside the greedy pass@1 leg.

**0d. Freeze the sets.** sha256 `diamond_eval_holdout.jsonl` into a `.summary.json`;
assemble and pin the 70-item dev set; verify module-level disjointness from the holdout.

**0e. Make the coverage check r-independent** (§2): expected-count assertion + exact
architecture-derived tensor counts, promoted out of `preflight_120b.py` into
`report_coverage`. Keep the 0.1% floor.

**0f. Guard the dense load path.** Add `exclude_modules=["visual\\..*", "mtp\\..*"]`
and assert at attach time that no `visual.` module is trainable. Currently safe only
because `AutoModelForCausalLM` happens to resolve to the text-only class (§0).

Also worth knowing before the reserved run, both from the eval-harness survey:
`data/processed/prover_eval.jsonl` is **missing** while `eval_prover_checkpoint.py:33`
and `train.py:119` both reference it; and `tests/` contains only stale `__pycache__` —
the eval-corpus builder/comparator tests were lost in revert `9724cef` and are
recoverable from `origin/codex/tla-prover-artifacts-and-gates`.

### Stage 1 — calibration, not science. 2 jobs, ~2 node-hours.

Re-measure s/step at the batch size and sequence length the real run will use, on the
real corpus, both arms, 20 steps. Two things need confirming: the 52.0 / 14.5 figures
were taken at per-device batch 1, a debug setting; and **PLAN.md:258's venue assumption
is wrong** — it presumes Sophia single-node 8×80GB, whereas `sophia-gpu-12` served all
four jobs on 2026-08-03 as **4×A100-40GB**, which is why Qwen at 56GB bf16 needs the
4-way shard. Confirm the allocation shape before sizing anything else.

### Stage 2 — equal-budget config selection on dev. 4 jobs, ~14 node-hours.

Grid, identical per arm: `r ∈ {8, 16}`, `alpha = 2r`, dropout 0 (forced — `ParamWrapper`
forbids otherwise), 2-epoch cap, matched optimizer steps, same seed, same corpus.
Within-arm entropy floor 0.68 as a **stopping guard only**, never as a cross-arm number.

| cell | trainable | fraction | node-h |
|---|---|---|---|
| dense r=8 α=16 | 58,363,904 | 0.2165% | 4.54 |
| dense r=16 α=32 | 116,727,808 | 0.4321% | 4.54 |
| MoE r=8 α=16 | 92,454,912 | 0.4401% | 1.26 |
| MoE r=16 α=32 | 184,909,824 | 0.8764% | 1.26 |

= 11.6 node-h train + ~2 node-h generation. Evaluate all four on the **70-item dev set**,
pass@1 and pass@8, verifier metrics only. Outputs: (i) each arm's selected config,
(ii) each arm's capacity-sensitivity curve — the control that actually matters (§4),
(iii) the fraction-matched cell (dense r=16 vs MoE r=8) for free.

Note the cross-rank caveat honestly in the writeup: `alpha = 2r` holds the initial update
scale but not the gradient scale, per rsLoRA. It applies *within* each arm's sensitivity
curve, not to the primary between-arm contrast, which is same-`r`.

### Stage 3 — the reserved pre-registered run. 2 jobs, ~6 node-hours + CPU validation.

Both arms at their Stage-2-selected configs, identical corpus / steps / seed / decode.
Evaluate **once** on the frozen, hash-pinned 30. Pre-register before submitting:
primary endpoint (diamond pass@1 and pass@8), `k`, temperature, seeds, the blinded
semantic-audit protocol, mean `partial_credit` as declared secondary, the **≥6-spec
resolution threshold**, and the tie-break criteria (throughput, 40GB fit, license).
Register the conditional dense-r=13 leg by sign of result (§4).

### Stage 4 — conditional, ~4.5 node-hours. Only if the MoE arm wins.

Dense r=13 α=26 (94,841,344, +2.6% over MoE's 92,454,912), count-matched, evaluated on
the frozen 30 as a declared robustness leg.

**Total GPU: ~35 node-hours of ~1,900 (< 2%).**

**The real schedule risk is CPU, not GPU.** The diamond gate runs TLC with mutation
testing at up to 90 s per invocation. 70 dev specs × 8 samples × ~4 TLC invocations
approaches ~50 h single-threaded; `harness/adequacy.py`'s measured 3.2× throughput at
`--workers 4` brings that to ~15 h wall. Place validation on a CPU allocation or run it
locally — it consumes no GPU node-hours, but it will dominate turnaround and should be
started as soon as generations land.

---

## 6. What I could not verify

- **The 5,000-row corpus size** used in the cost model is PLAN.md Amendment 20's proposed
  floor (4,512 at time of writing). The in-repo SFT file is
  `sft_harmony_v2.jsonl` at 260 rows. Step counts scale linearly — 260 rows at global
  batch 32 is 18 steps, so a 2-epoch run is minutes, not hours. Re-derive Stage 1–3 costs
  from the actual corpus.
- **The 52.0 / 14.5 s/step figures** are single-measurement, 8 steps, per-device batch 1,
  under LR warmup, on a 4×A100-40GB allocation. Not re-measured here (no cluster access
  used). Stage 1 exists to confirm them.
- **`AutoModelForCausalLM` → text-only for Qwen3.6-27B** is inferred from a byte-exact
  parameter-count match (26,895,998,464 derived vs measured), not from observing the load.
  Extremely strong but indirect; a one-line `named_modules()` check on the next dense job
  would settle it, and 0f makes it moot either way.
- **The exact `nn.Linear` inventory of the Qwen vision tower** is read from the
  safetensors index, so `visual.blocks.N.attn.qkv/proj` and `mlp.linear_fc1/fc2` are
  confirmed present *in the checkpoint*. Whether PEFT would target them depends on the
  load path, which is the point of 0f.
- **`rank_pattern` applying to `target_parameters`** is established from source reading
  (`lora/model.py:205-208` + the `current_key` construction at `tuners_utils.py:1105-1140`
  + the suffix matcher at `utils/other.py:1435-1443`), not from an executed test. Nothing
  in the recommended plan depends on it; it is recorded only as an available escape hatch
  (e.g. experts r=5 / attention r=8) if a future reviewer demands count-matching without
  touching attention.
- **Whether the 70-item dev set is truly disjoint** from the frozen 30 at module level.
  `carve_diamond_holdout.py:35-55` excludes modules already in `train.jsonl`, and
  `frs_tla_ralph_gen` is a separately generated corpus, but this needs an explicit check
  (0d) before any selection decision rests on it.
- **PEFT version on Sophia.** All source verification here is against **0.19.1** from
  `.venv311-repair` locally. Job 170815 ran in Sophia's `frs` conda env, whose PEFT
  version I could not inspect. `ParamWrapper` nesting for two params on one module
  (`lora/model.py:249-250`) is version-sensitive, and the 96-expert-tensor observation is
  only consistent with a version that has it — so 0.19.x-or-later is implied by the
  measurement, but pin and record it before the reserved run.
