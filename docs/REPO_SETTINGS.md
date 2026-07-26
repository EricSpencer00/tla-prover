# Repository settings that are not in version control

Three things this repo's workflow depends on live in GitHub settings, not in files,
so they are invisible to `git` and easy to lose. Recorded here with the reasoning.

## 1. Actions must be able to run jobs (BLOCKING as of 2026-07-26)

`.github/workflows/ci.yml` is committed and correct, but jobs are failing **at
dispatch** — before the first step. Signature, across three runs and nine job
attempts:

- every job fails in ~4 seconds
- **no logs are produced at all** (`HTTP 404` on the logs endpoint)
- `check_run.output` title, summary, and text are all empty
- this includes `frozen artifacts still parse`, a 4-line `json.loads` over five
  committed files with nothing to install — it cannot fail that way if it ran

All three jobs pass locally on the same tree (`319 passed, 1 skipped`;
`w4_audit.py` exit 0; export/audit agreement OK).

Most likely cause: **private-repo Actions minutes are metered**, and an exhausted
allowance or a $0 spending limit makes queued jobs fail instantly with no logs.
Second candidate: Actions disabled or restricted for the repo.

Where to look: account Billing → Plans and usage → Actions minutes and spending
limit; and Settings → Actions → General → "Allow all actions" (the workflow needs
`actions/checkout` and `actions/setup-python`).

**Going public fixes this for free.** Public repositories get unlimited Actions
minutes on standard runners, so if publication is near, that is a legitimate
resolution rather than a billing change.

## 2. Auto-merge — Settings → General → Pull Requests → "Allow auto-merge"

Currently **OFF**. It cannot be enabled through the API by a non-admin
integration, so a human has to tick it once; after that, auto-merge can be turned
on per-PR and this stays done.

**Order matters, and getting it wrong looks like a hang.** Auto-merge fires only
when every *required* check passes. So:

- Enabling auto-merge **while item 1 is unresolved** means PRs never merge. They
  sit indefinitely waiting on checks that fail at dispatch. This is strictly worse
  than the status quo, where a PR can simply be merged.
- With **no branch protection** — the current state — auto-merge is also moot: a
  PR is immediately mergeable (`mergeable_state: "unstable"` means "mergeable,
  with failing non-required checks"), so there is nothing to queue behind.

So auto-merge only becomes meaningful once item 1 is fixed AND item 3 marks the
checks required.

## 3. Branch protection on `main` — the checks that should be required

Not configured. Once Actions runs, require these three (the exact job names from
`ci.yml`):

- `harness test suite`
- `corpus export/audit agreement`
- `frozen artifacts still parse`

Recommended alongside: require a pull request before merging, and require branches
to be up to date before merging.

The reason to require the second one specifically: the SFT export and the wave
audit have drifted **twice** — once in row counts, once in the `arm`/`tier_name`
fields the Gate-2 eval stratifies on — and both drifts were silent, changing no
exit code. `tools/check_corpus_consistency.py` is the standing guard, and a guard
that isn't required is a guard that gets merged past.

## Recommended order

1. Fix Actions dispatch (billing/limits, or go public).
2. Confirm CI is green on a PR.
3. Tick "Allow auto-merge".
4. Add branch protection requiring the three checks.

Doing 3 or 4 before 1 blocks every PR.
