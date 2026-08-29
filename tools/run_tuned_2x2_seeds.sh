#!/usr/bin/env bash
# Close the tuned half of the loop-vs-open 2x2 at 3 seeds per cell.
#
# The base model already has 3 seeds in each cell (loop 18/16/18, open 12/8/12).
# The tuned model has 1 seed in each (loop 12/30, open 16/30), and the program's
# own measured seed spread on this endpoint is +-4 specs, so one seed cannot
# carry the loop-hurts-the-tuned-model reading. This runs the two missing seeds
# in each cell.
#
# Seeds are derived from run_id (harness/decoding.py:36), so a new --run-id is a
# new seed. There is no --seed flag and none is needed.
#
# Arm 5 is the grammar arm. It runs ONLY if the endpoint is proven to enforce
# structured outputs, because vLLM 0.22 accepts the legacy guided_* names with
# HTTP 200 and silently ignores them (docs/addendum limitations).
set -uo pipefail
cd "$(dirname "$0")/.."

JOB=${JOB:?set JOB to the qsub id, e.g. JOB=177470}
PORT=${PORT:-8321}
MODEL=chattla-w4dgm-120b
LOG=results/runs/autorun_tuned_seeds.log
exec > >(tee -a "$LOG") 2>&1
ts() { date +"[%H:%M:%S]"; }

echo "$(ts) waiting for job $JOB to start"
while :; do
  st=$(ssh sophia "qstat -f $JOB 2>/dev/null | awk '/job_state/{print \$3}'")
  [ "$st" = "R" ] && break
  [ -z "$st" ] && { echo "$(ts) job $JOB gone from queue -- aborting"; exit 1; }
  sleep 60
done
HOST=$(ssh sophia 'cat ~/vllm_serve_host_w4dgm_sn.txt')
echo "$(ts) job R on $HOST; waiting for vLLM to answer"

pkill -f "ssh -fN -L $PORT:" 2>/dev/null
ssh -fN -L "$PORT:$HOST:$PORT" sophia
export OPENAI_BASE_URL="http://localhost:$PORT/v1"
export OPENAI_API_KEY=dummy

for i in $(seq 1 90); do
  curl -sf "$OPENAI_BASE_URL/models" >/dev/null && break
  sleep 60
done

echo "$(ts) serve_preflight"
python3 tools/smoke/serve_preflight.py --model "$MODEL" || { echo "$(ts) PREFLIGHT FAILED -- not launching"; exit 1; }

# Two-request enforcement check. A server that ignores the parameter returns
# free-form prose; one that enforces it returns exactly one of the choices.
echo "$(ts) structured-outputs enforcement check"
probe() {
  curl -s "$OPENAI_BASE_URL/chat/completions" -H 'content-type: application/json' \
    -d "{\"model\":\"$MODEL\",\"max_tokens\":24,\"messages\":[{\"role\":\"user\",\"content\":\"The sky is clear and the temperature is\"}]$1}" \
    | python3 -c 'import json,sys; print(json.load(sys.stdin)["choices"][0]["message"]["content"].strip())'
}
LEGACY=$(probe ',"guided_choice":["alpha","beta"]')
CURRENT=$(probe ',"structured_outputs":{"choice":["alpha","beta"]}')
echo "$(ts)   legacy guided_choice  -> ${LEGACY:0:60}"
echo "$(ts)   structured_outputs    -> ${CURRENT:0:60}"
GRAMMAR_OK=0
case "$CURRENT" in alpha|beta) GRAMMAR_OK=1;; esac
echo "$(ts) structured outputs enforced: $GRAMMAR_OK"

run() {  # run <arm-label> <run-id> <cmd...>
  local label=$1 rid=$2; shift 2
  echo "$(ts) ==== $label : $rid ===="
  "$@" && python3 -m harness gate-check "results/runs/$rid" \
    || echo "$(ts) $label FAILED (continuing to next arm)"
}

run "A1 loop seed2" loop-w4dgm-120b-seed2 \
  python3 -m harness loop-eval --model "openai:$MODEL" --run-id loop-w4dgm-120b-seed2 --chains 8 --rounds 4
run "A2 loop seed3" loop-w4dgm-120b-seed3 \
  python3 -m harness loop-eval --model "openai:$MODEL" --run-id loop-w4dgm-120b-seed3 --chains 8 --rounds 4
run "A3 open seed2" open-w4dgm-120b-seed2 \
  python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id open-w4dgm-120b-seed2 --k 31
run "A4 open seed3" open-w4dgm-120b-seed3 \
  python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id open-w4dgm-120b-seed3 --k 31

if [ "$GRAMMAR_OK" = 1 ]; then
  export TLA_GUIDED_GRAMMAR=harness/grammars/tla_module_v1.ebnf
  run "A5 grammar" grammar-w4dgm-120b \
    python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id grammar-w4dgm-120b --k 31
  unset TLA_GUIDED_GRAMMAR
else
  echo "$(ts) A5 SKIPPED -- endpoint does not enforce structured outputs"
fi

echo "$(ts) ==== pooled 2x2 ===="
python3 tools/loop_multiseed.py \
  --loop results/runs/loop-w4dgm-120b results/runs/loop-w4dgm-120b-seed2 results/runs/loop-w4dgm-120b-seed3 \
  --open results/runs/open-w4dgm-120b-samesession results/runs/open-w4dgm-120b-seed2 results/runs/open-w4dgm-120b-seed3
echo "$(ts) ALL ARMS COMPLETE"
