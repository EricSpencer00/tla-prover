# W2.1 tier3-recovery lever vetting

Small-sample empirical probes for 5 proposed tier3-recovery levers, run
2026-07-09 against the frozen bounded-TLC evidence
(`results/runs/w21-tlc-20260709/tlc.jsonl`, deduped last-write-wins by path,
779 unique rows) and the current committed manifests
(`data/chattla-corpora-v2/manifest_tier1_sany_cfg.jsonl` = 697,
`manifest_tier2_sany.jsonl` = 170).

This is a **vetting pass only**. Nothing here touches PLAN.md, `corpus/`,
or the corpora-v2 manifests. All 125 probe rows are in `rows.jsonl`; sample
selection, seed, and repro commands are in `config.json`.

**Correction to the task brief's numbers**: the brief cited 33
`no_invariant_or_property_in_cfg` / 71 `only_1_distinct_states`. The actual
frozen evidence file has 43 / 119 respectively (`tier1_tier3_breakdown` /
`vacuity_reason_breakdown` in config.json). All measurements below use the
real counts.

## Lever 1: template cfg generation for tier2 (170, no cfg)

**Sample**: 25 of 170 tier2 files, seed 20260709.
**Recovered (non-vacuous pass)**: 0/25.
**Measured outcomes**: 18/25 `no_spec_or_init_next` (the static parser found
no top-level `Spec ==`, or `Init ==`/`Next ==` pair, to build SPECIFICATION
from — these are library modules instantiated elsewhere, PlusCal-translated
modules where the driving operator has a different name, or MC-wrapper
fixtures), 7/25 ran TLC and errored (`tlc_status=error`, mostly missing
CONSTANT semantics the template's naive small-set/small-int binding doesn't
satisfy, e.g. a CONSTANT that must be a specific structured value, not a
bare model-value set).

**Extrapolated tier3 yield**: ~0/170. At 0/25 in-sample, a rule-of-three
upper bound on the true recovery rate is ~3/25 ≈ 12% (95% one-sided), so a
generous ceiling is ~20/170 files recovered — but the 18/25
`no_spec_or_init_next` rate suggests the *addressable* population (files
where a template even has something to bind) is much smaller than 170 to
start with, probably closer to 170 × (7/25) ≈ 47, and even within that
subset actual runtime recovery was 0/7.

**Cost**: parser is cheap (harness/tier3_recovery.py, ~60 lines, already
unit-tested). Running it is cheap too — the bottleneck is TLC wall time
(60-90s/file), same as the existing tlc stage.

**Risk**: a template-cfg pass, if it DID recover files, would be a
materially weaker quality signal than an author-written cfg — model values
are arbitrary and bear no relationship to the module's intended semantics,
so "TLC ran without erroring" on a templated cfg only proves the module is
syntactically well-formed and has *some* reachable-state behavior, not that
the invariant tested is the one the author cared about (worse: the template
often has no invariant at all beyond a guessed TypeOK). **Recommendation if
run for real**: mark any tier3 promotion that came from a generated cfg as
`tier3_templated` (distinct tier from `tier3_authored`), and additionally
record which fields were templated (`bound_constants`) in the manifest row
so downstream consumers can filter it out of anything claiming
author-verified semantics.

**Recommendation: SKIP for now.** 0/25 recovered in-sample; the fixable
failure mode (7/25 `tlc_status=error` from bad constant instantiation) would
need a smarter constant-value inference (e.g. reading `ASSUME` clauses to
derive the actual required domain) to move the needle, which is a much
bigger investment than "templated cfg" as scoped in PLAN.md W2.1.

## Lever 2: smarter cfg pairing for tier3_tlc_fail

**Sample**: 25 of 560 `tier3_tlc_fail` files, seed 20260709.
**Recovered**: 0/25.
**Measured outcomes**: 11/25 `no_better_sibling` — and critically, of those
11, **all 11 already had `used_cfg_matches=True`** (the cfg w21_funnel used
already had every SPECIFICATION/INIT/NEXT/INVARIANT identifier resolving in
the module). 9/25 `no_matching_sibling_found` (used cfg was a genuine
mismatch, but no sibling in the directory fixed it either — these are large
shared test directories, e.g. apalache's `test/tla/` with 229-233 cfgs in
one dir, none written for this particular module). 5/25 `still_failed`
(a matching sibling was found and swapped in, TLC still errored).

**This directly contradicts the "560 errors are cfg mismatches" hypothesis
for this sample.** 44% of the sample already had a resolvable cfg and still
failed — meaning the failure mode is something else entirely: these are
overwhelmingly `apalache-mc/apalache` and `tlaplus/tlaplus` **test
fixtures**, files deliberately written to test SANY/TLC error paths (parse
errors, deliberately-buggy specs, type-annotation-only Apalache modules that
aren't meant to run under vanilla TLC at all). A cfg swap cannot fix "this
file is a negative test case by design."

**Extrapolated tier3 yield**: ~0/560 from this lever alone. The one
plausible sub-case (`no_matching_sibling_found` with a real mismatch, 9/25
= 36%) still had 0/9 recover when the best-available sibling was tried, so
even generalizing generously the ceiling is near 0.

**Cost**: cheap (already implemented, `find_matching_sibling_cfg` +
`cfg_matches_module` in harness/tier3_recovery.py, unit-tested).

**Recommendation: SKIP.** Evidence says this isn't a cfg-pairing problem
for the bulk of tier3_tlc_fail; it's a population problem (upstream test
fixtures, not "real" specs with a wrong cfg). Re-running the lever with a
larger sample is unlikely to change the conclusion given the mechanism
(0/11 already-matching, 0/9 swapped) is structural, not sampling noise.

## Lever 3: dependency staging (missing modules)

**Sample**: pre-filtered `tier3_tlc_fail` (560) to files whose `EXTENDS`
names are neither TLC-standard nor a sibling `.tla` in the same directory —
**70 candidates** found (12.5% of 560). Sampled 25 of those 70.
**Recovered**: 0/25.
**Measured outcomes**: 20/25 found and staged the missing dependency
(searched the whole containing repo, matched by declared MODULE name) but
TLC still errored; 5/25 found no dependency anywhere in the repo.

Root cause on inspection: the "missing" module in almost every case is
`Apalache` (a type-annotation-only module used by apalache-mc's own test
corpus, not runnable under vanilla TLC by design) or a CommunityModules
Java-operator module (`IOUtils`, `CSV`, `GraphViz`, `Combinatorics`) whose
implementation is a Java class, not a `.tla` file with real TLC semantics —
staging the `.tla` stub doesn't give TLC the Java backend it needs.

**Extrapolated tier3 yield**: ~0/70 (and thus ~0/560, since the other 490
`tier3_tlc_fail` files don't even have a plausible missing-EXTENDS to
stage).

**Cost**: cheap (implemented, repo-scoped `rglob` search, ~40 lines).

**Recommendation: SKIP.** The 70-file candidate population is dominated by
Apalache/CommunityModules-Java-backend test fixtures that are fundamentally
un-runnable under plain TLC regardless of staging; this isn't a
"missing sibling file" problem.

## Lever 4a: vacuity rescue — no_invariant_or_property_in_cfg (43 total)

**Sample**: 25 of 43, seed 20260709.
**Recovered (fully non-vacuous)**: 1/25 (4%).
**Partial (still vacuous, but for a DIFFERENT reason — the injected
invariant did pass, `only_1_distinct_states` remains)**: 2/25 (8%).
**No invariant-like def to inject at all**: 22/25 (88%) — most of these
`no_invariant_or_property_in_cfg` files are, again, TLC test fixtures with
no `TypeOK`/`Invariant`/`Safety`-named operator anywhere in the module (the
point of the fixture is often to exercise TLC's coverage/error-reporting
code paths, not to check an invariant).

**Extrapolated tier3 yield**: 43 × (1/25) ≈ 1-2 files recovered
non-vacuous, plus 43 × (2/25) ≈ 3-4 that improve from
"no invariant configured" vacuity to "too few states" vacuity (still
demoted, but a more informative demotion reason). 95% Wilson interval on
1/25 is roughly [0.2%, 20%], so the honest range is 0-9 files, most likely
1-2.

**Cost**: cheap, already implemented (`parse_module` invariant-name
detection + cfg injection, unit-tested).

**Recommendation: RUN, but expect single-digit yield.** It's cheap and
strictly monotonic (never makes a file worse — worst case is still
vacuous, same tier as before), so there's no downside to running it over
the full 43, just don't expect it to move tier3 materially. **Mark any
resulting promotion as `tier3_templated`**, not `tier3_authored` — the
injected invariant name is a heuristic guess (first of
`TypeOK/TypeInvariant/TypeInv/TypeOk/Invariant/Inv/Safety` that's actually
defined), not confirmed by the module's own author-written cfg.

## Lever 4b: vacuity rescue — only_1_distinct_states (119 total)

**Sample**: 25 of 119, seed 20260709, larger-constant template
(`set_size=5, int_max=6` vs the default 3/3).
**Recovered**: 0/25.
**Measured outcomes**: 24/25 still vacuous (same `only_1_distinct_states`
reason, sometimes now co-occurring with `no_invariant_or_property_in_cfg`
or `trivial_invariant:Inv` once the template overwrote a working cfg); 1/25
had no Spec/Init/Next to template at all.

Root cause on inspection: these files (predominantly
`apalache-mc/apalache/test/tlaplus-suite/*` and
`tlaplus/tlaplus/tlatools/.../test-model/*`) generate exactly 1 state
**by design** — `ASSUME`-only "solve by constant evaluation" specs, or
type-checker unit-test fixtures with no real `Next` transition relation.
Larger constant cardinality doesn't create transitions that don't exist in
the spec; `only_1_distinct_states` here isn't a constant-sizing artifact,
it's a structural property of the module.

**Extrapolated tier3 yield**: ~0/119. Rule-of-three ceiling ~3/25 → ~14/119
at the very outside, but the observed mechanism (no real Next relation)
doesn't respond to constant sizing at all, so 0 is the honest expectation.

**Cost**: cheap (reuses lever-1 template code with different params).

**Recommendation: SKIP.** The lever's premise — that under-sized constants
are suppressing state-space growth — doesn't hold for this population;
these specs have no growth to suppress.

## Lever 5: scrape widening (analysis only, no re-scrape)

**Confirmed the hypothesis directly.** `search_repositories()` in
`tla-dataset-pipeline/src/tladata/discovery/github_search.py` calls
`GET /search/repositories` with the configured queries from
`config/seeds/queries.yaml`:

```
extension:tla
extension:cfg tla
"\* PlusCal" extension:tla
"EXTENDS" "VARIABLES" extension:tla
TLAPS extension:tla
```

These are **code-search qualifiers** (`extension:`, quoted content-match
terms) — valid only against `GET /search/code`, which searches file
contents. Verified empirically via `gh api`:

| query | `/search/repositories` total_count | `/search/code` total_count |
|---|---|---|
| `extension:tla` | 8 | 64,896 |
| `extension:cfg tla` | 0 | 10,040 |
| `"\* PlusCal" extension:tla` | 0 | (not rechecked verbatim; `PlusCal extension:tla` = 1,776) |
| `"EXTENDS" "VARIABLES" extension:tla` | 0 | `EXTENDS VARIABLES extension:tla` = 7,360 |
| `TLAPS extension:tla` | 0 | 3,576 |

**4/5 queries return 0 hits against the endpoint actually called** — fully
confirmed, not a partial effect. The 1 query that returns something
(`extension:tla`, 8 repos) does so only because `/search/repositories`
happens to substring-match `tla` in repo names/descriptions/topics, which
is a coincidental, low-recall side effect, not the intended file-extension
filter.

**Repo-diversity estimate.** The current raw scrape spans **only 15 unique
repos** (2,615 files total; enumerated by top two path components under
`data/raw/`). A single page (100 items) of `GET /search/code?q=extension:tla`
alone contains **43 unique repos, 41 of which (95%) are not in the current
15-repo set** — e.g. `UWSysLab/tapir`, `ailidani/paxi`,
`Isaac-DeFrain/TLAplusFun`, `fpaxos/fpaxos-tlaplus`,
`hachikuji/kafka-specification`. `total_count=64,896` file-level hits for
that one query implies (conservatively, assuming heavy repeat-repo density
like the observed 43%) on the order of hundreds to low thousands of
additional distinct repos across all 5 (corrected) queries, an order of
magnitude beyond the current 15.

**Cost**: fixing the bug is a one-line change (call `search_code` /
`GET /search/code` instead of `search_repositories`, or add a genuinely
new `search_code()` function since the two endpoints return different
item shapes — a `/search/code` item is a file match with a `repository`
sub-object, not a repo record directly, so `fetch_repo_metadata` still
needs to run per unique repo found). Estimate: half a day including the
downstream repo-metadata dedup logic and a real GitHub API rate-limit plan
(`/search/code` is rate-limited to 10 req/min unauthenticated / higher
authenticated, tighter than `/search/repositories`'s 30/min).

**Recommendation: FIX, but scope as its own ticket, not part of this
vetting's tier3-recovery levers** — this is a scrape-time fix that would
change what gets scraped, not a post-hoc recovery lever over the existing
779-file tier1+tier2 population. It is almost certainly the single highest-
leverage change available (15 repos vs. hundreds+ addressable), but it
requires a new scrape + full funnel re-run (dedup/decontam/sany/tlc), which
is explicitly out of scope for this vetting task ("Do NOT... re-run the
scrape").

## Overall

None of levers 1-4 recover a material number of files from the existing
779-file tier1+tier2 population: measured totals were 0, 0, 0, 1(+2
partial), 0 recoveries respectively out of 125 probed files. The
population these levers target (apalache-mc test fixtures, tlaplus/tlaplus
test-model fixtures, CommunityModules unit tests) is **structurally**
unrecoverable by cfg/dependency/constant-sizing fixes — they are negative
test cases, Java-backed library shims, or zero-transition constant-solving
specs by design, not "real" specs with a fixable cfg. Extrapolated total
recovery across all 4 in-corpus levers: **roughly 1-6 files out of the
779-file tier1+tier2 population** (all from lever 4a), i.e. tier3 stays
effectively at its current 82.

Lever 5 (scrape widening) is the only lever with real leverage — the
current 15-repo raw scrape is an artifact of a code-search-syntax query
being run against the repository-search endpoint, not signal that TLA+
content is scarce on GitHub. Fixing it is out of scope here but should be
the next PLAN.md item considered, ahead of any further recovery-lever work
on the existing narrow scrape.
