# Decode Provenance — making run-to-run variance attributable

**Goal:** Make every model call in the harness carry a recorded, *recomputable* decoder
seed plus a hash of the request body actually sent, and add a `replay` command that
re-executes a single stored row and diffs the result. After this, "the same model gave a
different answer" is a measurement with a reproduction command attached, not an anecdote.

**Why now:** `tools/rowlevel_power.py:8-11` ledgers spec 30 going **5 passes → 1 pass**
between `gate2-w4dg-120b-A` and `gate2-w4dg-120b-A3` — same model, byte-identical prompt
(`prompt_sha256` matched). That pair exists as a negative control precisely because the
variance cannot currently be attributed: no `seed` is sent on any request. The request
body is built in exactly two places, `harness/repair.py:96-99` (Anthropic) and
`harness/repair.py:168-172` (OpenAI-compatible), and both send only `model`, `max_tokens`,
`temperature`, `messages`. `harness/repair.py:62` already concedes the gap in prose —
reproducibility is claimed only "from (model id, prompt hash, *seed semantics of the
provider*)". The provider's seed semantics are, at present, unrecorded and unprobed.

**What this does not do:** It does not reduce sampled-arm variance. Diversity at
`TEMPERATURE = 0.8` is load-bearing for pass@k and stays exactly as it is. This changes
zero verdicts on zero existing rows.

**Non-goal — grammar-constrained decoding.** Amendment 19 (2026-07-18) already closed this
on both sides and the reasoning holds: the proof-side guided run
(`results/runs/w32-guided-120b`) scored 0/20 with tlapm failures merely moving one level
down into step-internal syntax, and the spec side was closed by a pre-registered offline
bound — the structural grammar rejects only 10/505 (2%) of actual failed candidates. The
`.ebnf` files are consumed only by `tools/smoke/grammar_check.py:14` as an offline xgrammar
lint, and the dev vLLM's structured-outputs path killed the engine twice (jobs 165652,
165692). Nothing here reopens that; this design changes no decoding *constraint*, only what
is recorded about decoding.

**Architecture:** One new module (`harness/decoding.py`) owning seed derivation and
request-body hashing; one API extension on the existing `Model` ABC in `harness/repair.py`;
additive-only fields on `gen_eval` rows; one new CLI subcommand; one preflight probe.
No changes to scoring, extraction, temperature, sample counts, or the resume ledger's key.

**Tech stack:** existing `harness.repair`, `harness.gen_eval`, `harness.runner`; stdlib
`hashlib`/`json` only. No new dependencies.

---

## Global constraints

- **Append-only ledgers are untouched (Rule 8).** No existing row in `results/runs/` is
  rewritten. New fields appear only on rows written after this lands.
- **Extraction semantics are frozen.** See "Landmine 2" below. The two extractors keep
  their current, divergent behavior; divergence is *recorded*, not resolved.
- **`gate_check` stays green.** `harness/gate_check.py` reads rows by key and computes
  from `verdict` / `sample`; additive fields cannot trip its thresholds. A test asserts
  `gate_check()` returns an identical report for a row set with and without the new fields.
- **No credentials in the ledger.** `OPENAI_BASE_URL` may embed routing detail; only its
  sha256 is recorded, never the URL, and never the bearer token.
- **Amendment 12's frozen budget is not silently altered.** Adding a decoder seed changes
  the realized sample, so it gets a ledger row and a sign-off (Task 6).

---

## Landmines found while reading

### Landmine 1 — the `seed` row key is already taken

`harness/gen_eval.py:634` writes `"seed": seed` on every Framing-B row. That is the
**mutation corruption seed** threaded in from `gen_eval_spec_framing_b(..., seed, ...)`,
identifying which deterministic `harness.mutation` swap produced the corrupted input. It is
not a decoder seed and has nothing to do with sampling.

Writing a decoder seed to `seed` would silently overwrite it and corrupt every Framing-B
analysis that joins on the mutation. **The decoder seed field is `decode_seed`.** A
regression test pins this: construct a Framing-B row, assert `row["seed"]` still equals the
mutation seed and `row["decode_seed"]` is a distinct value.

### Landmine 2 — the two extractors differ in more than first-vs-last

| | `harness/gen_eval.py:196` | `harness/repair.py:522` |
|---|---|---|
| pattern | `^-{4,}\s*MODULE\b.*?^={4,}` | `(-{4,}\s*MODULE\s+\w+\s*-{4,}.*?^={4,})` |
| match taken | **first** (`.search`) | **last** (`.findall`, `m[-1]`) |
| module name | not required | `\w+` required |
| trailing dashes after name | not required | required |
| line-anchored opener | yes (`re.M`, `^`) | no |

So a reply containing `---- MODULE ----` with no name extracts under `gen_eval` and
returns `None` under `repair`; a reply with a discussion draft followed by a final module
extracts the *draft* under `gen_eval` and the *final* under `repair`. These are two
different functions, not one function called two ways.

Unifying them would change extraction for some fraction of already-scored rows and
retroactively invalidate every ledger in `results/runs/` — a Rule 8 violation and a
much larger blast radius than the problem justifies. **Neither extractor changes.**
Instead each row records `extractor` (which one ran) and `extract_divergent` (whether the
other one would have produced different text). That converts an unknown into a measured
rate, which is what decides whether unifying them is worth an amendment later.

**MEASURED, 2026-08-08 (`tools/extractor_divergence.py`).** Over all 1,079 raw replies
persisted across 35 run dirs, the two extractors disagree on **0** of them — every one is a
case where *neither* parses. Unification would recover zero rows, so the divergence is
theoretical rather than empirical, and the frozen-extractor call now rests on evidence
rather than caution. Decomposing that same population turned up something more useful:
41.3% (446) are empty replies, 36.2% (391) never attempt a module, 21.3% (230) are
`max_tokens` truncations cut off before the `====`, and 3 use a malformed
`==== MODULE X ====` header. Two fifths of `no_module_extracted` is the endpoint returning
nothing and a fifth is a budget artifact — neither is model incapacity, though both
currently score as model failure. Ledgered in Amendment 23; deliberately not corrected here.

Scope limit on that number: `_persist_candidate` keeps the raw reply only when extraction
*failed*, so this cannot see replies both extractors parsed but parsed differently.
Measuring that direction needs raw replies persisted on success too — a separate change.

### Landmine 3 — `OPENAI_EXTRA_BODY` merges last and can silently win

`harness/repair.py:172` does `body.update(json.loads(os.environ.get("OPENAI_EXTRA_BODY", "{}")))`
*after* the base body is built. A stale `OPENAI_EXTRA_BODY` containing `seed` would
override the harness's seed with no warning, and the row would record a seed that was
never sent. Mitigation: `decode_params_sha256` hashes the **post-merge** body, and
`generate_traced` returns the effective seed read back out of the merged body — not the
seed that was requested.

---

## Components

### 1. `harness/decoding.py` (new)

```python
def derive_seed(run_id: str, spec: str, framing: str, sample_id) -> int
```
`int.from_bytes(sha256(f"{run_id}\x00{spec}\x00{framing}\x00{sample_id}".encode()).digest()[:4], "big") & 0x7FFFFFFF`.

Seeds are **derived, not stored-and-hoped-for**: replay recomputes the seed from the run
identity, so a truncated or lost `rows.jsonl` line does not make a sample unreproducible.
Range is clamped to signed-32-bit-positive because that is the intersection of what vLLM,
OpenAI, and the ALCF router all accept.

```python
def effective_params_sha256(body: dict) -> str
```
sha256 over `json.dumps({k: v for k, v in body.items() if k != "messages"}, sort_keys=True)`.
`messages` is excluded because `prompt_sha256` already covers it and including it would
make the params hash useless for grouping. This is the field that catches Landmine 3: two
runs that believe they used the same budget but differ in `reasoning_effort` or a stray
`top_p` will show different `decode_params_sha256`.

### 2. `Model` API extension (`harness/repair.py`)

The ABC keeps `generate` abstract exactly as it is today (`repair.py:66`) and adds a
`generate_traced` whose **default adapts a `generate`-only subclass**:

```python
class Model:
    def generate(self, prompt, n, temperature, max_tokens, seed=None) -> list[str]:
        raise NotImplementedError

    def generate_traced(self, prompt, n, temperature, max_tokens, seed=None
                        ) -> list[tuple[str, dict]]:
        """Default: adapt a generate-only implementation. Subclasses that
        implement generate_traced natively MUST also override generate (see
        the recursion hazard below)."""
        return [(t, {}) for t in
                self.generate(prompt, n, temperature, max_tokens, seed)]
```

Real subclasses implement `generate_traced` natively and override `generate` as a
two-line projection:

```python
    def generate(self, prompt, n, temperature, max_tokens, seed=None):
        return [t for t, _ in self.generate_traced(
            prompt, n, temperature, max_tokens, seed)]
```

**Recursion hazard — the reason for that duplication.** The first draft of this design had
the ABC define `generate` in terms of `generate_traced` *and* `generate_traced` in terms of
`generate`. A subclass overriding neither would recurse until the stack blew. Direction must
be fixed per class, so each of the two one-line projections is written explicitly at exactly
one level: the ABC adapts `generate` → `generate_traced`, and each real subclass projects
`generate_traced` → `generate`. A test instantiates a bare `Model()` subclass overriding
neither method and asserts `NotImplementedError`, not `RecursionError`.

Why this shape:
- All ten existing `model.generate(...)` call sites keep working with no edit
  (`gen_eval.py:51`, `repair.py:631`, `repair.py:661`, `w2_loop.py:355`, `w2_loop.py:670`,
  `proof_gen.py:209`, `repair_harvest.py:158`, `w4_difficulty.py:333`, `w4_scenarios.py:134`,
  and `w27_scaffold.py:380` via `w2_loop`).
- Every fake `Model` in the test suite (`gen_eval.py:848`, `w2_loop.py:768`,
  `w4_difficulty.py:284`, `w4_verify_cell.py:30`, `smoke_e2e.py:52`) overrides `generate`
  only, and keeps working untouched — the ABC's default `generate_traced` adapts them,
  yielding an empty meta dict. `gen_eval` must therefore treat a missing meta key as
  `null` provenance rather than assuming the keys exist.
- `seed` is added as a trailing defaulted parameter on both, so positional calls at every
  existing site remain valid.
- **No `self.last_request` mutable state.** `GEN_EVAL_CONCURRENCY > 1` runs
  `_prefetch_replies` through a `ThreadPoolExecutor` (`gen_eval.py:57`) sharing one `Model`
  instance; per-call provenance on the instance would race. Meta rides back with its own
  completion instead. (`self.usage` at `repair.py:148` is an accumulator and is
  race-tolerant in a way per-request provenance is not.)

The returned meta dict carries `decode_seed` (post-merge effective value, or `None`),
`decode_params_sha256`, `provider_seed_echo`, `backend_sha256`, and `seed_supported`.

Per-subclass behavior:

- **`OpenAICompatModel`** — puts `seed` in the body before the `OPENAI_EXTRA_BODY` merge
  (preserving the existing "extra body wins" precedence), then reads the effective seed
  back out of the merged body for the meta. Captures the provider's echoed `seed` from the
  response when present. `backend_sha256 = sha256(self.url)`.
- **`AnthropicModel`** — the Messages API has no `seed` parameter. It records
  `seed_supported: False` and `decode_seed: None`. Recording a seed the provider cannot
  honor is **false provenance**, which is strictly worse than recording none: it makes an
  irreproducible row look reproducible.
- **`LocalStub`** — already deterministic; records `seed_supported: True`, echoes the seed.

### 3. Row provenance (`harness/gen_eval.py`)

`_prefetch_replies` derives the seed per sample and returns meta alongside the reply, so
its return type becomes `{sample_id: (reply, model_s, meta)}`. `run_id` and `framing` must
reach it — they are already in scope at both call sites
(`gen_eval_spec_framing_a`, `gen_eval_spec_framing_b`).

Fields added to the `base` dict in both framings:

| field | meaning |
|---|---|
| `decode_seed` | effective decoder seed, or `null` if unsupported |
| `decode_params_sha256` | hash of the request body actually sent, minus `messages` |
| `provider_seed_echo` | seed the provider reported back, or `null` |
| `seed_supported` | whether the backend can honor a seed at all |
| `backend_sha256` | sha256 of the endpoint URL (never the URL, never the key) |
| `extractor` | `"gen_eval.first"` or `"repair.last"` |
| `extract_divergent` | `true` if the other extractor yields a different result |

`extract_divergent` compares `gen_eval.extract_module(reply)` against
`repair.extract_candidate(reply)` after stripping trailing whitespace. It is `true` when
the two strings differ **or when exactly one of them is `None`** — a reply that only one
extractor can parse is the most interesting divergence case, not an exclusion from it. Both
`None` is `false`, and the row's verdict is already `no_module_extracted` in that case.
The comparison is pure string work on an in-memory reply: no extra API call, no extra
SANY/TLC run.

Additive only. The existing `seed` key on Framing-B rows is untouched (Landmine 1).

### 4. `harness replay` (new subcommand)

```
python3 -m harness replay <run-dir> --spec N --sample S [--framing A|B]
```

1. Load the row from `rows.jsonl`.
2. **Rebuild the prompt** from the corpus via the same `build_generation_prompt` /
   `build_repair_prompt` path the run used.
3. **Assert the rebuilt `prompt_sha256` matches the stored one.** A mismatch means the
   corpus or prompt template drifted since the run — that is a free corpus-drift detector
   and is reported as `PROMPT_DRIFT` before any API call is made.
4. Re-request at the recorded `decode_seed`, same temperature and `max_tokens`.
5. Diff the new candidate against the stored `candidate_path`
   (persisted by `_persist_candidate`, `gen_eval.py:494-520`).

Verdicts: `IDENTICAL` / `DIVERGENT` (with a unified diff and the two sha256s) /
`PROMPT_DRIFT` / `SEED_UNSUPPORTED`.

### 5. `tools/smoke/seed_probe.py` (new preflight)

Two requests to the live endpoint, identical prompt, identical seed, `temperature=0.8`.
Then a third at a *different* seed as a negative control — if all three match, the endpoint
is ignoring temperature, not honoring the seed, and the "success" is meaningless.

Verdicts: `HONORED` (same seed identical, different seed differs) / `IGNORED` (same seed
differs) / `DEGENERATE` (all identical — suspect temperature is being dropped) /
`PARTIAL` (same-seed replies differ only past some prefix — the continuous-batching
signature).

This gates real sweeps. If ALCF's vLLM ignores `seed`, that surfaces in ~30 seconds
instead of after a 12-hour sweep that recorded provenance which was never real. Follows the
existing pattern in `tools/smoke/serve_preflight.py`.

**Expected result, stated honestly up front:** `PARTIAL` is a plausible and acceptable
outcome. vLLM under continuous batching is not bitwise deterministic even at a fixed seed,
because batch composition changes floating-point reduction order. A seed pins the sampling
RNG, not the numerics. `PARTIAL` still buys attributable provenance and a much narrower
divergence envelope; only `IGNORED` or `DEGENERATE` would mean the seed is worthless.

### 6. PLAN.md amendment entry

`gen_eval.py:28` reads "Amendment 12 frozen budget (PLAN ledger entry 12): never inline
these elsewhere." Amendment 12 froze temperature 0.8 / max_tokens 16384 / 32 samples /
pass@1 = one temp-0 greedy sample. A decoder seed does not change that distribution but it
does change the realized sample, and existing runs were unseeded — so seeded and unseeded
runs are distributional peers but not row-level peers.

A draft amendment row (matching the existing `PLAN.md:244+` table format: number, date,
change, rationale, owner) will be written for Eric's sign-off, stating: the frozen budget
values are unchanged; `decode_seed` is added as provenance; pre-amendment runs are marked
`seed_supported: null` when re-read and remain valid as distributional peers.

**The amendment is drafted, not self-signed.** Every row in that table carries an explicit
`Eric (date)` attribution.

---

## Testing

New: `harness/test_decoding.py`
- `derive_seed` is stable across processes and distinct across each of the four inputs.
- `derive_seed` output is always in `[0, 2**31)`.
- `effective_params_sha256` ignores `messages`, is order-insensitive, and differs when
  `reasoning_effort` or `top_p` differs.
- `OPENAI_EXTRA_BODY` overriding `seed` is detected: the meta reports the *override*, not
  the requested seed (Landmine 3).
- A `Model` subclass overriding neither method raises `NotImplementedError`, **not**
  `RecursionError` (the recursion hazard in Component 2).
- A `generate`-only fake works through `generate_traced` and yields an empty meta dict.

Extended: `harness/test_gen_eval.py`
- **Framing-B `seed` collision guard** (Landmine 1): mutation seed survives, `decode_seed`
  is separate.
- `extract_divergent` is `true` for a reply where first-match and last-match disagree, and
  `false` for a single clean module.
- `generate` and `generate_traced` return the same texts for the same inputs.
- `gate_check()` produces an identical report for rows with and without the new fields.

All tests run against `LocalStub` and in-process fakes. **Zero API spend, no network.**

---

## Sequencing

1. `harness/decoding.py` + `test_decoding.py` — standalone, no callers yet.
2. `Model.generate_traced` + ABC wrapper — verify the full existing suite still passes
   before any call site is touched.
3. `gen_eval` row fields + tests.
4. `harness replay`.
5. `tools/smoke/seed_probe.py`.
6. Draft the amendment row; hand to Eric.

Steps 1-5 are inert until a run is executed with them. Nothing here reruns a sweep or
spends inference budget; deciding whether to re-measure a baseline under seeds is a
separate call, made after `seed_probe` reports what the endpoint actually does.
