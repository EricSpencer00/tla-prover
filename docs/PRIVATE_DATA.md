# The Gate-2 answer key is not in this repo

`EricSpencer00/tla-prover` is public. The FormaLLM corpus it evaluates lives in
`LUC-AI4FM/tla_benchmark`. Together those two repos used to say which 30 specs
Gate 2 scores *and* what a correct output for them looks like. Anyone could
train on the holdout and then report a Gate-2 number.

## What was removed

| Path | Why |
|---|---|
| `corpus/holdout_30.json` | the 30 frozen Gate-2 spec numbers |
| `corpus/configs/drafts/` | hand-authored `.cfg` for 71 specs, 14 of them holdout |
| `corpus/configs/overrides/` | hand-authored `.cfg` that replaces a broken original, 3 holdout |
| `corpus/configs/patches/` | hand-authored `.tla` corpus-defect fixes, 1 holdout |
| `corpus/configs/wrappers/` | hand-authored MC wrapper modules |
| `corpus/configs/apalache-annotated/` | type-annotated specs, 1 holdout |

`corpus/configs/policy.json`, `populations.json`, `repair_budget.json` and the
`.md` notes stay. They are operational settings and prose findings, not answers.

## Where it went

`harness/private_data.py` resolves each path from `$TLA_PROVER_PRIVATE`,
defaulting to `./private/` (gitignored). Callers keep the old repo-relative
spelling, so `policy.json` wrapper entries and archived run configs still read
correctly. On a checkout that still has the files, nothing changes.

To restore a working checkout:

    TLA_PROVER_PRIVATE=/path/to/private/root python3 -m harness ...

`private/` mirrors the repo layout: `private/corpus/holdout_30.json`,
`private/corpus/configs/patches/`, and so on.

## What this does NOT do

Two gaps, both needing a decision that is outside this change.

1. **Git history still has every file.** They were public from commit `ce1dd5c`
   onward. Deleting them at HEAD does not remove them from the public mirror --
   `git log` still serves them. Closing that needs a history rewrite and a force
   push to `origin/main`.

2. **The Gate-2 run ledgers still enumerate the holdout.** Every
   `results/runs/*/config.json` and `summary.csv` for a Gate-2 or E2.c run lists
   exactly the 30 spec numbers, as does `corpus/e2c_baseline.json` (29 of 30) and
   `results/analysis/holdout_family_tags.jsonl`. `tools/check_holdout_leak.py`
   finds 51 such files. They hold *measured results*, not the answer key, and
   they are the evidence behind the published numbers -- so they are listed in
   that tool's `KNOWN_MEMBERSHIP_LEAKS` rather than deleted. Removing them trades
   reproducibility of the reported results for holdout secrecy.

Privatizing `LUC-AI4FM/tla_benchmark` is the control that matters most: without
the corpus text, the holdout spec *numbers* are not enough to train on.
