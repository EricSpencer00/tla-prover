#!/bin/bash
# Build a user-owned, hash-pinned XGrammar closure for the Polaris CPython 3.12 runtime.
# This never modifies the shared ChatTLA virtual environment.
set -euo pipefail

ROOT=${1:?usage: $0 USER_OWNED_TARGET GRAMMAR_FILE}
GRAMMAR=${2:?usage: $0 USER_OWNED_TARGET GRAMMAR_FILE}
PYTHON=${PYTHON:-/home/eric-spencer/ChatTLA/.venv/bin/python}
HERE=$(cd "$(dirname "$0")" && pwd)

if [ -e "$ROOT" ]; then
  echo "refusing to overwrite existing dependency closure: $ROOT" >&2
  exit 2
fi
STAGING=$(mktemp -d "${ROOT}.staging.XXXXXX")
"$PYTHON" -m pip install --no-deps --require-hashes --target "$STAGING" \
  -r "$HERE/protected_checkpoint_xgrammar_requirements.txt"
"$PYTHON" -u "$HERE/protected_checkpoint_preflight.py" \
  --dependency-only --grammar "$GRAMMAR" --xgrammar-site "$STAGING"
mv "$STAGING" "$ROOT"
