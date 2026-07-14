#!/bin/bash
# Toy end-to-end pipeline smoke: proves EVERY stage of the RFT pipeline
# mechanically in ~2-5 min local wall time (plus one-time venv/model setup),
# so config-class bugs (like the ctx-4096 truncation that invalidated Gate-2
# framing B, 2026-07-14) die here instead of after an 8-12h Sophia run.
#
# Stages:
#   A  generation loop (scripted model, REAL SANY/TLC/mutation gates)
#   B  corpus -> harmony SFT jsonl (channel-discipline asserted)
#   C  REAL LoRA train + merge on SmolLM2-135M (loss must drop; merged loads)
#   D  OpenAI-compatible serve (canned canonical-spec mode)
#   E  gen-eval (2 specs, k=2) -> must pass >=1 spec; resume must skip all
#   F  gate-check on E -> OK
#   G  ctx-bug regression: serve at --max-model-len 512, rerun gen-eval,
#      gate-check MUST fail (exit 1) on api_error rate
#
# Usage: tools/smoke/run_e2e.sh  (from repo root)
set -uo pipefail
export PYTHONUNBUFFERED=1
# HPC login nodes (ALCF) export http_proxy; both curl and the harness's
# urllib client would route localhost through the site proxy (503s).
export no_proxy=localhost,127.0.0.1 NO_PROXY=localhost,127.0.0.1
cd "$(dirname "$0")/../.."

VENV=tools/smoke/e2e/.venv
CORPUS=${CORPUS:-/Users/eric/GitHub/tla_benchmark/data}
PORT=${PORT:-8399}
RUN=results/runs/smoke-e2e
SPECS=${SPECS:-5,37}          # 37 = deterministic pass path; 5 = fail path (dup module name)
# SMOKE_PY: interpreter that already has torch/transformers/peft/fastapi
# (e.g. Sophia's conda base). If unset, a local venv is created.
SMOKE_PY=${SMOKE_PY:-}
export OPENAI_BASE_URL=http://localhost:$PORT/v1 OPENAI_API_KEY=dummy OPENAI_RPM=600

fail() { echo "SMOKE FAIL at stage $1"; pkill -f serve_toy.py 2>/dev/null; exit 1; }

if [ -n "$SMOKE_PY" ]; then
  MLPY=$SMOKE_PY
else
  if [ ! -x "$VENV/bin/python" ]; then
    echo "== one-time setup: venv =="
    python3 -m venv "$VENV" && "$VENV/bin/pip" install -q -r tools/smoke/e2e/requirements.txt || fail setup
  fi
  MLPY=$VENV/bin/python
fi

rm -rf "$RUN" results/runs/smoke-e2e-eval-A results/runs/smoke-e2e-ctxbug
pkill -f serve_toy.py 2>/dev/null; sleep 1

echo "== stages A+B: gen loop + corpus (real TLC gates) =="
python3 -m harness.smoke_e2e "$RUN" || fail A/B

echo "== stage C: toy LoRA train + merge =="
"$MLPY" tools/smoke/e2e/train_toy.py --sft "$RUN/sft_smoke.jsonl" --out "$RUN" || fail C

echo "== stage D: serve (canned canonical mode) =="
"$MLPY" tools/smoke/e2e/serve_toy.py --port "$PORT" \
  --canned-corpus "$CORPUS" --max-model-len 32768 > "$RUN/serve.log" 2>&1 &
SERVE_PID=$!
# cold imports on HPC shared filesystems can take >90s; poll long, die fast if the proc dies
for i in $(seq 1 180); do
  curl -sf localhost:$PORT/v1/models >/dev/null && break
  kill -0 $SERVE_PID 2>/dev/null || { cat "$RUN/serve.log"; fail D; }
  sleep 1
done
curl -sf localhost:$PORT/v1/models >/dev/null || { cat "$RUN/serve.log"; fail D; }

echo "== stage E: gen-eval (specs $SPECS, k=2) =="
python3 -m harness gen-eval --framing A --model openai:toy \
  --run-id smoke-e2e-eval-A --k 2 --specs "$SPECS" --corpus-data "$CORPUS" || fail E
# resume must be a no-op (0 new calls)
python3 -m harness gen-eval --framing A --model openai:toy \
  --run-id smoke-e2e-eval-A --k 2 --specs "$SPECS" --corpus-data "$CORPUS" 2>&1 | tee /tmp/smoke_resume.log
grep -q "resumed 3 skipped" /tmp/smoke_resume.log || fail "E-resume"

echo "== stage F: gate-check (must be OK, must show >=1 pass) =="
python3 -m harness gate-check results/runs/smoke-e2e-eval-A || fail F
python3 -m harness gate-check results/runs/smoke-e2e-eval-A | grep -q "pass@k = [1-9]" || fail "F-passpath"

echo "== stage G: ctx-bug regression (gate-check MUST fail) =="
pkill -f serve_toy.py; sleep 1
"$MLPY" tools/smoke/e2e/serve_toy.py --port "$PORT" \
  --canned-corpus "$CORPUS" --max-model-len 512 > "$RUN/serve_ctxbug.log" 2>&1 &
SERVE_PID=$!
for i in $(seq 1 180); do
  curl -sf localhost:$PORT/v1/models >/dev/null && break
  kill -0 $SERVE_PID 2>/dev/null || { cat "$RUN/serve_ctxbug.log"; fail G-serve; }
  sleep 1
done
python3 -m harness gen-eval --framing A --model openai:toy \
  --run-id smoke-e2e-ctxbug --k 2 --specs "$SPECS" --corpus-data "$CORPUS" || fail G-eval
if python3 -m harness gate-check results/runs/smoke-e2e-ctxbug; then
  echo "gate-check ACCEPTED a ctx-broken run -- the 2026-07-14 bug class is NOT caught"
  fail G
fi

pkill -f serve_toy.py 2>/dev/null
echo
echo "=================================================="
echo "SMOKE E2E: ALL STAGES OK (A B C D E F G)"
echo "=================================================="
