# Measured facts for the addendum. Every number came from a ledger re-score.
# Do not invent, re-round, or extrapolate. If a number you want is not here, it
# was not measured; say that instead.

## What was built

**Framing L.** The parent paper's evaluation, and every arm this project has run,
is OPEN-LOOP: k independent draws from one prompt, each scored by SANY/TLC,
best-of reported. The verifier is a judge, never a controller. Framing L closes
it: generate, verify, feed the diagnosis back, regenerate. 8 chains x 4 rounds =
32 model calls per spec, one FEWER than framing A's 33 (1 greedy + k=32), so the
loop cannot win on budget. Chains advance in lock step; TLC stays strictly
serialized and only network calls overlap. Round-0 prompts are byte-identical to
framing A's generation prompt (the ledger records prompt_sha256). Scoring reuses
the framing-A scorer verbatim.

Diagnosis rungs, priority order: `signature` (module omits an identifier the
fixed .cfg requires), then `sany`, then `tlc_error`, then `tlc_violation`. The
signature checker is a feedback SELECTOR, never a gate: it never skips a
verification stage.

## Headline result (base model, untuned gpt-oss-120b, 30-spec frozen holdout)

    framing L (closed loop)   18 / 16 / 18   mean 17.3   571-616 model calls
    framing A (open loop)     12 /  8 / 12   mean 10.7   960-990 model calls

Three seeds each. Ranges do not overlap: the worst framing-L seed exceeds the
best framing-A seed. Across all nine (L seed, A seed) pairings the delta is +4 to
+10, one loss total (spec 181, in two pairings), sign-test p from 0.0020 to
0.1250 depending on the pairing. gate-check clean on every run: 0 api_error rows,
0 unextracted rows.

Pre-registered analysis rule, fixed BEFORE the runs: a win requires >= +5 specs
or McNemar exact p < 0.05; anything smaller reports as null. Seed 2 alone against
the same-session control is +4, p = 0.125, NULL by that rule. Reporting seed 1
alone (+6, p = 0.031) would have been a sampling accident.

## Mechanism (seed 1, the arm with per-call provenance)

Of 18 solves, 9 came from a fresh generation within the first round of 8
independent draws and 9 came from a repair round. 5 of the 6 specs gained over
the frozen control were won on a repair round (3 entered as rung `sany`, 2 as
`tlc_error`), not on a fresh generation.

## Per-spec stability (qualifies the headline; do not omit)

Only TWO specs (13 and 15) are solved by framing L in every seed and by framing A
in none. 132 and 191 are 2/3; 32, 106, 133, 174 are 1/3. No spec is ever
open-loop-only. The defensible claim is that the loop reliably adds about five to
seven specs, the direction never reverses, but WHICH specs it adds varies by
seed: a larger reachable set, not a deterministic gain.

## Confounds closed

1. Endpoint drift. The frozen control was measured months earlier. Re-running the
   open-loop control on the same warm endpoint at a matched 32-call budget
   reproduced 12/30 exactly. Per-sample SANY across the session in run order:
   16.6%, 22.9%, 23.9%, 25.7%, 15.2%; median latency 20.3s, 23.0, 22.6, 22.7,
   20.2. The control's 8/30 third seed is spec-level sampling noise, not a
   degrading serve.
2. Single-seed accident: three seeds per arm, all reported.

## A metric that must NOT be quoted as a comparison

Framing L stops a spec on its first pass, so an easy spec contributes one passing
row while framing A banks 20+ on the same spec. Per-sample PASS rate is therefore
structurally biased AGAINST L (3.0% vs 7.5%) and is not a capability comparison.
Per-sample SANY is biased the same direction, which makes L's advantage there
conservative: 24.1% [22.2, 26.1] vs 14.1% [12.8, 15.3], bootstrap 95% CI, pooled
over 1,760 and 2,910 rows.

## Reachability ceiling (pooled over all six arms, 4,670 draws)

    draws                           4670   100%
    SANY parse                       834    18%
    + satisfies the .cfg signature   678    15%
    TLC pass                         219     5%

    specs with >= 1 parsing draw             30/30
    specs with >= 1 signature-complete draw  26/30
    specs with >= 1 TLC pass                 20/30

Spec-level SANY coverage is already 100%: every holdout spec produced at least
one parsing candidate. Worst spec is 106 at 1/174 draws; best is 181 at 101/158.

## Failure taxonomy (3,836 SANY failures across the six arms)

    grammar (module does not parse)   1967   51%
    unknown operator                  1304   34%
    other                              375   10%
    duplicate definition                97    3%
    wrong arity                         86    2%
    missing substitution / level         7    0%

Of 3,750 individual "Unknown operator" errors located in the candidate's own
module:

    invented operator (exists nowhere)         1990   53%
    M!op against an unqualified INSTANCE       1195   32%
    bound variable escaping its quantifier      385   10%
    RECURSIVE used without declaration           97    3%
    genuine forward reference                    83    2%

The INSTANCE case is one misunderstanding producing two error classes: the model
writes `INSTANCE Bakery` (unqualified, which imports every name) and then
`vars == Bakery!vars`; the qualified prefix requires a NAMED instance, and the
redefinition collides with what the unqualified INSTANCE already imported.

Most frequent offending tokens in the parse-failure population: `:` 139,
`\subseteq` 126, `,` 118, `AS` 89, `LET` 85. These correspond to
comma-separated LET bindings, `\E x \subseteq S`, `INSTANCE M AS B`, lowercase
`let ... in`, and `\Sum i \in S :`. Each is a construct borrowed from a more
popular language.

## Negative result that constrains the interpretation

A deterministic lint pass (drop declarations colliding with EXTENDS, add missing
standard-module EXTENDS, drop duplicate definitions) recovered 88 candidates
across 9 unsolved specs from fail to parse. Specs flipped to solved: ZERO. All 88
died at TLC. Forcing output to parse, on its own, buys nothing.

## Where the fine-tuning program stands, by the same rule

The best fine-tuned checkpoint in this program reaches 15/30 open-loop against a
base control of 12/30: +3, gained 5, lost 2, McNemar exact p = 0.45, NULL by the
pre-registered rule. An untuned base model in the loop (mean 17.3/30) exceeds it.
That 15/30 also decomposes: 4 of those specs are library modules scored on SANY
alone and 1 is a proof module scored on TLAPS, leaving 10 actually model-checked.

## The decode-time grammar

`tla_module_v1.ebnf` is a TLA+ expression grammar for constrained decoding.
Measured by `tools/grammar_falsereject.py`:

    known-good specs (examples corpus + 30 gold holdout)   438
    false-rejected                                           0
    measured real parse failures                          1543
    rejected by the grammar                               1338   86.7%

The grammar already in the repository before this work (`tla_module_v0.ebnf`, a
structural tier enforcing module framing and balanced brackets) false-rejects
5.0% of valid specs and catches 3.2% of real parse failures. The candidates are
already 100% well-framed, balanced and terminated, so the structural tier has
almost nothing to act on. A companion `.cfg` grammar false-rejects 0 of 230
corpus configuration files.

Constructs the corpus forced into the grammar, none guessable from the language
reference: nested junction lists under a bullet; bare `\` as set difference;
postfix `f[x]` application; `\leq` and `\geq`; operator symbols passed as
arguments (`Fold(+, 0, ...)`); tuple subscripts in `[][Next]_<<a,b>>`;
`P(Succ)!Reachable0` qualification after an application; the parenthesised infix
operators `(+)`, `(-)`, `(\X)`; the `^^ ** ++ -- // %% ## $$ ?? !!` symbolic set;
`RECURSIVE` declared inside a `LET`; nested `---- MODULE Inner ----` units;
NESTING `(* (* *) *)` block comments; subexpression labels `P0 :: expr`; and
identifiers beginning with a digit (`---- MODULE 2PCwithBTM ----` is a real
corpus spec).

Junction-list ALIGNMENT is not enforced and cannot be: it is context-sensitive,
SANY uses a custom lexer for it, and no context-free grammar expresses it.

## LIMITS. State these. Do not soften them.

1. **The grammar has not been run in a generation arm.** The 86.7% is an offline
   measurement over saved candidates: an upper bound on what decode-time
   constraint would remove, not a measured end-to-end gain. No claim about pass
   rate under constrained decoding is supported.
2. **The 2x2 is incomplete.** Framing L has been measured on the base model only.
   The tuned-model cell requires a self-hosted serve that has not yet run, so
   nothing here says what task training adds ON TOP of the loop.
3. One model family, one size (gpt-oss-120b), one 30-spec holdout.
4. Spec-level pass@k at k=32 is noisy: the open-loop control moved 12/8/12 across
   seeds while its per-sample SANY rate stayed flat.
5. The shared inference endpoint used for these arms accepts vLLM's
   `guided_grammar` and `guided_choice` with HTTP 200 and applies neither,
   verified by sending `guided_choice: ["alpha","beta"]` and receiving a
   free-form sentence. Constrained decoding requires a self-hosted serve.
6. 4 of the 30 holdout specs are library modules scored on SANY alone and 2 are
   proof modules scored on TLAPS; 24 are graded by TLC.

## Figures (already rendered, in figures/)

- `fig_seeds.pdf` -- solved specs per seed for both arms, plus mean model calls.
- `fig_funnel.pdf` -- draws, parse, signature, TLC; per draw and per spec.
- `fig_taxonomy.pdf` -- SANY failure classes and the unknown-operator breakdown.
- `fig_perspec.pdf` -- per-spec solve rate over seeds, both arms.
- `fig_grammar.pdf` -- grammar v0 against v1: false-reject rate and catch rate.
