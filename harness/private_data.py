"""Corpus artifacts that must not ship in the public mirror (ticket #11).

The frozen Gate-2 holdout manifest and the hand-authored corpus configs
(overrides, patches, MC wrappers, Apalache annotations, draft cfgs) are the
evaluation answer key: together with the FormaLLM corpus they say which 30
specs Gate 2 scores and what a correct output for them looks like. They are
stripped from `EricSpencer00/tla-prover` and live in a private root instead.

`resolve()` keeps the old repo-relative spelling working. Callers and stored
paths (policy.json wrapper entries, run configs, PLAN references) are
unchanged; on a checkout that still has the files nothing moves at all.

Set TLA_PROVER_PRIVATE to point the private root somewhere else.
"""
import json
import os
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PRIVATE = Path(os.environ.get("TLA_PROVER_PRIVATE") or (REPO / "private"))

# Repo-relative paths stripped from the public mirror. Also the strip list
# tools/check_holdout_leak.py enforces -- keep the two in step.
STRIPPED = (
    "corpus/holdout_30.json",
    "corpus/configs/apalache-annotated",
    "corpus/configs/drafts",
    "corpus/configs/overrides",
    "corpus/configs/patches",
    "corpus/configs/wrappers",
)


def resolve(rel) -> Path:
    """Repo path when the artifact is present, else the private copy.

    Returns a path either way; the caller does its own .exists() check, as it
    did when these files were in the repo."""
    p = REPO / rel
    return p if p.exists() else PRIVATE / rel


HOLDOUT_FILE = resolve("corpus/holdout_30.json")


def holdout_specs() -> list:
    """The 30 frozen Gate-2 spec numbers, or [] when the private root is not
    mounted. Callers that need the holdout must fail loudly themselves --
    silently scoring an empty holdout is worse than crashing."""
    if not HOLDOUT_FILE.exists():
        return []
    return json.loads(HOLDOUT_FILE.read_text()).get("holdout_specs", [])


def require_holdout() -> list:
    specs = holdout_specs()
    if not specs:
        raise SystemExit(
            f"holdout manifest not found at {HOLDOUT_FILE}. It is stripped from the "
            f"public mirror (ticket #11); set TLA_PROVER_PRIVATE to the private root.")
    return specs
