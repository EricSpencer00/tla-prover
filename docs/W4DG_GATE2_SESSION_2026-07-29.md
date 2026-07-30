# W4-diamond-gold 120b — Gate-2 framing A, and the harness bug it uncovered

Session of 2026-07-29/30. Covers the merge + serve bring-up, the framing-A arm, a
harness defect found while auditing its failures, the fix, and the re-run.

**Headline: the capability numbers moved by less than the noise. The durable result
is a harness bug that had been silently corrupting every framing-A measurement the
project has recorded.**

---

## 1. Runs

| run | what | result |
|---|---|---|
| `gate2-w4dg-120b-A` | framing A, k=32, 30 specs, 990 rows | **15/30** pass@32 |
| `QUARANTINE-…-A2-declared-Nat` | re-run on a half-correct prompt fix | killed at 99 rows |
| `gate2-w4dg-120b-A3` | framing A after the corrected fix | **16/30** pass@32 |
| `gate2-w4dg-120b-B` | framing B, partial | 110/990 rows, clean ledger |

Model: W4-diamond-gold LoRA merged into gpt-oss-120b (Sophia job 169865, 233.7GB),
served with vLLM TP=8 at `--max-model-len 32768`. Backed up to
[EricSpencer00/chattla-w4dg-120b](https://huggingface.co/EricSpencer00/chattla-w4dg-120b)
(5 shards, file-level verified).

## 2. Capability comparison — nothing significant

Paired against `gate2-v2-120b-A` (11/30) and between the two arms:

| comparison | result | McNemar exact (2-sided) |
|---|---|---|
| A (15/30) vs gate2-v2 (11/30) | gained 5, lost 1 | **p = 0.22** |
| A3 (16/30) vs A (15/30) | gained 2, lost 1 | **p = 1.000** |

Neither is evidence of a capability change.

### The noise floor, measured for free

The fix changed prompts for exactly 13 specs, leaving 17 byte-identical — an
unplanned control group. Across A → A3 on those 17 unchanged prompts:

- spec-level verdicts moved by **1** (spec 95 lost)
- row-level pass counts swung much harder: spec 30 `5 → 1`, spec 5 `7 → 12`

**Single-run per-spec pass@32 is not a reliable capability signal at k=32.** Future
capability claims need multiple seeds. This applies retroactively to the 2/30
baseline, gate2-v2's 11/30, and both numbers above.

## 3. The harness bug

`required_signature()` parsed each cfg CONSTANT entry as
`re.split(r"<-|=", body)[0]` — keeping the LEFT identifier and discarding the RIGHT.

For `Nat <- NatOverride`, the prompt's authoritative REQUIRED IDENTIFIERS block said
*define Nat* and never mentioned `NatOverride`. TLC then hard-failed:

```
Error: The configuration file substitutes for Nat with the undefined identifier NatOverride.
```

Verified rather than inferred: framing-A prompts were rebuilt for specs 181/158/13
from `<corpus>/descriptions/<num>.json` and their `prompt_sha256` matched the frozen
run's rows exactly. In those verified prompts the RHS operators appear nowhere.

**Blast radius:** 13/30 holdout specs use `<-`; 12 were among the 15 unsolved.

A second bug in the same parser: several entries on one cfg line lost all but the
first (spec 158's `CONSTANTS a1=a1 a2=a2 a3=a3 v1=v1 v2=v2` yielded only `a1`).
`SYMMETRY` was unhandled.

This is **not** the oracle-side issue already closed in
`corpus/configs/SIBLING_WRAPPERS.md`: that supplies the real wrapper module when
checking a corpus spec, which cannot help framing A, where the *model* is what has
to produce the wrapper.

## 4. The fix, in two passes

Substitution LHS names are two different things needing opposite instructions:

- **inherited from a standard module** (`Nat` in 13/14/121/181, `Seq` in
  128/132/133/135/141) — must NOT be declared; the cfg overrides the inherited
  definition. Reported as `sig["builtin_overrides"]`.
- **the spec's own constant** (`Node` 55, `CalculateHash` 148,
  `Acceptor`/`Value`/`Quorum`/`Ballot` 158, `NumActors` 168) — declared as a
  constant AND the RHS operator must be defined.

The first pass got only half of this: it named `NatOverride` (working — 31/33
candidates defined it, up from 0/33) but left `Nat` in CONSTANTS, so the model
declared a name it inherits and all 33 died on `Multiply-defined symbol 'Nat'`.
Caught at 99 rows by the A2 run and quarantined.

Values are parsed with a brace-depth scanner (`_split_cfg_assignments`), not a
regex, because cfg values nest: `Offers = {{matches, paper}, {matches, tobacco}}`.
Two earlier regex attempts harvested set *elements* as required constants
(`participants = {p1, p2, p3}` → `p2`, `p3`) and would have corrupted prompts for 8
specs with no substitutions at all.

Verification: prompts differ from the pre-fix run for **exactly** the 13
substitution specs, byte-identical for the other 17, every RHS appears in its
prompt, no builtin LHS appears in constants. 332 tests pass.

## 5. What the fix bought: necessary, not sufficient

| | A | A3 |
|---|---|---|
| control (17 identical prompts) | 14/17 | 13/17 |
| changed (13 fixed prompts) | 1/13 | **3/13** |

Specs 13 (`0 → 8/33`) and 181 flipped. **Ten of thirteen stayed at zero** — removing
the prompt blocker only exposed the next one. The earlier estimate that the fix
could unlock ~12 specs, and that framing A's ceiling was ~18/30, was wrong.

Independent blockers found behind the substitution bug:

- **spec 55** — model omits `EXTENDS FiniteSets` → `Unknown operator: Cardinality`
- **spec 14** — defines `NatOverride == {0 .. (MaxNat-1)}`, a set *of sets* rather
  than a range → `Attempted to compare integer 0 with non-integer`. A genuine
  modeling error, and a healthy sign: pre-fix this spec could not even attempt.
- **spec 121** — cfg is `Nat <- [ZSequences]CharacterSet`, a *module-qualified*
  substitution. Framing A asks for one self-contained module, so this spec is
  **structurally unsuited to the framing**, not merely under-specified. Excluding it
  from a frozen holdout is a goalpost decision — flagged, not acted on.

## 6. Failure profile

| | A | A3 |
|---|---|---|
| `sany=fail` | 76.2% | **67.7%** |
| genuine semantic failures (invariant/liveness/deadlock) | 2.2% | 2.1% |

Both arms are dominated by mechanical failures, not modeling errors. Roughly 2% of
990 attempts fail because the model got the *system* wrong.

### Framing B is the contrast that matters

Specs 13 and 14 score **0/33 in framing A** both before and after the fix, but
**29/33 and 9/11 in framing B**, where the input already contains `NatOverride`.
Same weights, same specs.

## 7. Negative result: the lint idea

`tools/lint_repair_probe.py` + `tools/lint_repair_tlc.py`. A deterministic lint
(drop builtin-colliding declarations, add missing `EXTENDS`, dedupe definitions)
made **88 of 454** sany-failed candidates in unsolved specs parse, across 9 specs —
and flipped **zero** specs to solved. They all then hit the substitution error.

Parse-recovery is not pass-recovery. Dropping the `Nat` declaration is in fact
*wrong*: the cfg needs `Nat` present to substitute against. Retains value as a
diagnostic; retracted as a proposed lever.

## 8. Deliberately not done

Adding `NatOverride == 0 .. MaxNat` as a prompt example would likely flip specs
13/14/181 — it is the canonical answer. That converts the benchmark from a
capability measure into a hint-following measure. **Any further prompt wording
change needs explicit sign-off.**

## 9. Open items

- [ ] **Amendment ledger entry** — framing-A prompts changed for 13 specs; pass@32
      is not comparable across the fix for those. A3 is a new baseline.
- [ ] **Decide spec 121's disposition** (denominator exclusion vs. leave failing).
- [ ] **Finish framing B** — resumes from row 110, needs a serve.
- [ ] **Multi-seed protocol** before any future capability claim.

## 10. Operational traps recorded

- `GEN_EVAL_CONCURRENCY` defaults to **1**; the previous B re-run burned 11.2h of
  its 12.2h wall on serial calls. Set it to match `--max-num-seqs`.
- `ssh -N -L` exits 0 immediately under ALCF's ControlMaster auto-mux and the
  forward never listens. Use `ssh -O forward`.
- Read the serve port from the PBS script (it was 8321, not 8000). A wrong port
  gives curl exit 56, indistinguishable from a dead server.
- PBS hooks rewrite the resource request — verify `Resource_List` after submission,
  not the script.
- A monitor whose `pgrep` pattern matches its own command line goes silently blind
  to the crash it is watching for. Track by PID.
