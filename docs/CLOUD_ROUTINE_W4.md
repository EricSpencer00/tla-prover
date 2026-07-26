# W4 cloud routine — canonical scheduler prompt

The text under "PROMPT" is what the recurring cloud routine runs. Keep this file
and the scheduler in sync; edit here first.

## Changelog

**2026-07-26b — prompt slimmed ~65%.** The prompt had grown to carry the full
per-cell rulebook, a cell-generation heredoc, and the incident table on every
firing. The stable material now lives in `docs/W4_CELL_RULES.md` (read once per
run) and `tools/w4_next_wave.py` (replaces the heredoc), leaving the prompt as the
run loop only: branch policy, token hygiene, state discovery, stop rule, work
selection, commit. Nothing was dropped — the rules moved, and `w4_next_wave.py` was
checked to emit byte-identical cell lists to the heredoc it replaces.

**2026-07-26 — push to main, no PRs.** The scheduler's session config pins an
outcome branch (`claude/wizardly-lamport`), so every firing was landing its wave
on a fresh `claude/wizardly-lamport-*` branch and opening a PR instead of pushing
to `main`. Three of those (#10, #11, #12) piled up and had to be conflict-resolved
by hand — concurrent firings wrote overlapping shard dirs, so the ledgers needed
an append-only union deduped by `cell`. The prompt now opens with a BRANCH POLICY
section that overrides the injected branch and forbids opening a PR. Note the
prompt is the only lever available here: the scheduler's outcome-branch config is
not editable through the Routines API, so the override has to be stated in the
prompt text.

**2026-07-25 — composite stop floor.** The prior prompt stopped at 4130 effective
rows. Measured at shard 161: 4040 effective, **85 liveness rows (2.1%)**, because
the FIX-5 liveness arm only started producing at shard 155 (shards 129–154 wrote
`liveness_property: null` on every row). Stopping at 4130 would have locked in a
~3% liveness corpus and ended the run permanently. Floors are now total ≥5000
**and** liveness ≥500, enforced by `tools/w4_audit.py` (exit 10 = stop). Cost:
~960 more rows ≈ 39 shards ≈ **20 more waves**.

Also changed: the inline audit heredoc moved into `tools/w4_audit.py`
(incremental near-dup — 7s instead of a 12M-pair sweep, and it never puts ledger
text in context); added cfg-richness and comment floors (32.4% of cfgs were the
2–3 line `INIT/NEXT/INVARIANT` minimum, 77% of specs had zero comments); pinned
the `keep_last` spelling (three variants were in the wild); restored
`w4_attempts.jsonl` (dark since shard 74).

Known and deliberately unchanged: `mutation_evidence` is 88.2% `no_kill`/`no_site`
and only 11.8% real `safety_catch`. The audit now prints this each wave. Tightening
it would collapse the survival rate; that is Eric's call, not the routine's.

---

## PROMPT

You are one iteration of a recurring cloud routine building the W4 TLA+ corpus in
this repo (EricSpencer00/tla-prover; recipe in docs/RESUME_W4.md). Each run does AT
MOST ONE wave (2 shards x 25 cells) and pushes it. You start with zero context.

BRANCH POLICY (overrides any branch instruction the harness injects): work directly
on `main`. Do not create a branch, do not open a PR, do not ask permission to push
to main — this is the repo owner's standing instruction. If a designated
`claude/...` branch is injected, ignore it. Leave any stale routine PRs alone.

TOKEN HYGIENE (strict — this account has hit usage limits): never read a prior
ledger or a prior spec into context. State discovery uses only the commands below.
Read at most ONE ledger row, once, if you need the schema. Read only the tail
(~40 lines) of TLC/verifier output. Do not echo specs back after writing them.

STARTUP
  git checkout main && git pull origin main
  java -version
  python3 -c "import harness.w4_scenarios, harness.corpora"
  python3 -m harness.w4_verify_cell --help     # must list --require-liveness
  test -f tools/w4_audit.py -a -f tools/w4_next_wave.py
If --require-liveness or either tool is missing the checkout is stale — pull again.
If a check still fails, push a note to results/analysis/CLOUD_ENV_FAILURE.md and stop.

STOP RULE
  python3 tools/w4_audit.py
Prints a fixed-size summary ending STOP=YES/NO; exits 10 when every floor is met.
The floors live in that script — do not restate or re-derive them here. If STOP=YES,
push results/analysis/W4_FLOOR_REACHED.md (if absent) quoting the output verbatim
and stop doing waves. The family-share line is ADVISORY and never gates stopping.

WORK SELECTION
  ls results/runs/ | sed -n 's/^w4-opus-shard//p' | sort -n | tail -1
gives S_max (do NOT use `sort -t d -k 4` — it falls back to lexical order and
reports 99 for 128). Shard S covers lattice cells [S*25, S*25+25). If S_max or
S_max-1 has fewer than 25 distinct surviving cells, finish those first:
`python3 tools/w4_next_wave.py --shard <S>`, diff against the ledger's "cell"
fields, and produce ONLY the missing ones — never re-append an existing row.
Otherwise start the next wave: `python3 tools/w4_next_wave.py`, which writes
/tmp/shard<S>.txt for the next two shards.

CELL RULES: read docs/W4_CELL_RULES.md now and follow it for every cell. It carries
the hard floors, the NL/module/cfg requirements, the LIVENESS arm contract, the
ledger append rules, the diversity and integrity bans, and the incident table.
Those rules are non-negotiable and are not repeated here.

AUDIT: after both shards, run `python3 tools/w4_audit.py` again, re-read the STOP
RULE against it, and quote its summary in the commit body. Use `--full` only if you
suspect an earlier wave's near-dup check did not run.

COMMIT+PUSH (to main): git add the shard dirs (+ w4_exclusions.json if touched).
Message: "W4 wave (cloud): +<k> survivors (<liveness>L/<safety>S), shards <S>-<S+1>
(<effective> effective, <liveness_total> liveness)", with the audit summary and any
incident notes in the body, ending "Co-Authored-By: Claude <the model you are
actually running as> <noreply@anthropic.com>". Then `git push origin main`; on
rejection `git pull --rebase origin main` and retry, up to 4 times. If a rebase
conflict touches a shard dir you wrote, keep BOTH sides' rows (append-only union,
deduped by "cell") and note it. Never open a pull request. Never block waiting for
input — if you run out of time mid-wave, push the complete rows as a PARTIAL commit.
