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
# Connection resilience (2026-08-30): the clusters bounced overnight and the
# original script had two holes. (1) A transient ssh failure made the qstat
# wait-loop read "job gone" and abort. (2) A serve/tunnel drop mid-arm wrote
# verdict=api_error rows that resume then refused to retry. The second is fixed
# in the harness (load_existing_rows skips api_error; gate_check dedup prefers
# the scored retry), so the recipe here is: health-check before every arm,
# reconnect on failure, and re-run a failed arm once -- resume only redoes the
# missing and errored pairs.
#
# Arm 5 is the grammar arm. It runs ONLY if the endpoint is proven to enforce
# structured outputs, because vLLM 0.22 accepts the legacy guided_* names with
# HTTP 200 and silently ignores them (docs/addendum limitations).
set -uo pipefail
cd "$(dirname "$0")/.."

JOB=${JOB:?set JOB to the qsub id, e.g. JOB=177470}
PORT=${PORT:-8321}
MODEL=chattla-w4dgm-120b
SERVE_PBS='~/serve_vllm_w4dgm_sn.pbs'
HOSTFILE='~/vllm_serve_host_w4dgm_sn.txt'
LOG=results/runs/autorun_tuned_seeds.log
RESUBMITS=0
# The nine arms need ~20.5h of serve at measured rates (loop ~1.3h, gen ~2.9h,
# 2026-08-31 it23) and a window is 12h walltime, so the sequence spans at least
# two windows. A budget of 2 leaves no slack once a resubmit is also spent
# clearing a system-hold, and the arms that would be starved are A7-A9, the
# newest and most informative ones. 4 covers the sequence plus two losses.
MAX_RESUBMITS=4
exec > >(tee -a "$LOG") 2>&1
ts() { date +"[%H:%M:%S]"; }

# job_state <id> -> R/Q/F/H/... on stdout, rc 0. rc 1 = ssh itself failed
# (cluster unreachable -- NOT the same as the job being gone). rc 2 = ssh ok,
# job unknown to PBS.
#
# A system hold (Hold_Types=s, "too many failed attempts to run") is reported
# as SHOLD, not H. PBS sets it after 21 failed launches and only an admin can
# qrls it, so the job will never run: it is terminal, not a wait state. Waiting
# on one costs a whole night (2026-08-31).
job_state() {
  local out
  out=$(timeout 40 ssh -o ConnectTimeout=20 -o BatchMode=yes sophia \
        "qstat -xf $1 2>/dev/null | awk '/job_state/{s=\$3} /Hold_Types/{h=\$3} \
         END{if (s==\"H\" && h ~ /s/) print \"SHOLD\"; else print s}'") || return 1
  [ -n "$out" ] || return 2
  echo "$out"
}

# True once a schedulable node (gpu-01..09) has all 8 GPUs free. gpu-10..22 are
# idle but the scheduler will not place on them, so they must not count.
free_node() {
  timeout 60 ssh -o ConnectTimeout=20 -o BatchMode=yes sophia '
    pbsnodes -av 2>/dev/null | awk "
      /^sophia-gpu-/{ if (n && ok && tag && asg==0 && sched) print n
                      n=\$1; ok=0; tag=0; asg=-1
                      sched=(n ~ /gpu-0[1-9]\$/) }
      /resources_available.queue_tags = prod/{tag=1}
      /resources_available.ngpus = 8/{ok=1}
      /resources_assigned.ngpus = /{asg=\$3+0}
      END{ if (n && ok && tag && asg==0 && sched) print n }
    "' 2>/dev/null | head -1
}

wait_for_capacity() {
  local n
  while :; do
    # free_node returns empty BOTH when no node is free and when ssh fails, so
    # check reachability first. Otherwise an expired ControlMaster stalls the
    # run behind a message that reads like ordinary waiting (2026-08-31 it70).
    if ! timeout 40 ssh -o ConnectTimeout=20 -o BatchMode=yes sophia true 2>/dev/null; then
      echo "$(ts) cannot reach sophia (OTP login needed?); retrying in 5 min"
      sleep 300; continue
    fi
    n=$(free_node)
    [ -n "$n" ] && { echo "$(ts) capacity: $n has 8 free GPUs"; return 0; }
    echo "$(ts) no schedulable node with 8 free GPUs; waiting 10 min"
    sleep 600
  done
}

# Block until $JOB is running, riding out unreachable-cluster stretches.
# A finished/vanished job is resubmitted (bounded), updating $JOB.
wait_for_job() {
  while :; do
    local st rc=0
    st=$(job_state "$JOB") || rc=$?
    case "$rc:$st" in
      0:R) echo "$(ts) job $JOB running"; return 0 ;;
      0:Q|0:H) sleep 120 ;;
      1:*) echo "$(ts) cluster unreachable, retrying in 5 min"; sleep 300 ;;
      0:SHOLD)
        # Held by the scheduler after repeated launch failures. Delete it; the
        # next pass reads the job as gone and takes the resubmit branch. If the
        # cause is facility-side the new job holds too, and the resubmit budget
        # ends the run instead of hanging on a job that can never start.
        echo "$(ts) job $JOB system-held (launch failures); deleting"
        timeout 60 ssh sophia "qdel $JOB" 2>/dev/null
        sleep 10 ;;
      *)  # ssh fine but job finished or unknown -> serve died or was purged
        if [ "$RESUBMITS" -ge "$MAX_RESUBMITS" ]; then
          echo "$(ts) job $JOB gone and resubmit budget spent -- aborting"
          return 1
        fi
        RESUBMITS=$((RESUBMITS + 1))
        echo "$(ts) job $JOB gone (state='$st'); resubmitting ($RESUBMITS/$MAX_RESUBMITS)"
        # Wait for a SCHEDULABLE node with 8 free GPUs first. Submitting while
        # gpu-01..09 are full lands the job on an idle-but-unschedulable node,
        # where it fails to launch 21 times and is system-held -- which would
        # spend the whole resubmit budget in minutes (2026-08-31 it50/it54).
        wait_for_capacity
        JOB=$(timeout 60 ssh sophia "qsub $SERVE_PBS" | cut -d. -f1) || {
          echo "$(ts) resubmit failed, retrying in 5 min"; sleep 300; }
        [ -n "$JOB" ] && echo "$(ts) new serve job $JOB"
        sleep 120 ;;
    esac
  done
}

serve_ok() { curl -sf --max-time 15 "http://localhost:$PORT/v1/models" >/dev/null; }

# The connection test Eric asked for: cheap check first; on failure walk the
# whole chain back up -- job state, host file, mux forward, vLLM readiness.
ensure_serve() {
  serve_ok && return 0
  echo "$(ts) serve check FAILED -- reconnecting"
  wait_for_job || return 1
  local host
  host=$(timeout 40 ssh sophia "cat $HOSTFILE") || {
    echo "$(ts) cannot read host file"; return 1; }
  # The mux (ControlMaster) holds forwards; cancel any stale one for this port
  # regardless of which node it pointed at, then add the current one.
  ssh -O cancel -L "$PORT:$host:$PORT" sophia 2>/dev/null || true
  ssh -O cancel -L "$PORT:$LAST_HOST:$PORT" sophia 2>/dev/null || true
  ssh -fN -L "$PORT:$host:$PORT" sophia || return 1
  LAST_HOST=$host
  echo "$(ts) tunnel -> $host; waiting for vLLM"
  local i
  for i in $(seq 1 60); do
    serve_ok && { echo "$(ts) serve healthy"; return 0; }
    # If the job died while we waited, go back around the whole loop.
    if [ $((i % 10)) -eq 0 ]; then
      st=$(job_state "$JOB") || st=""
      [ "$st" = "R" ] || { echo "$(ts) job left R while waiting"; ensure_serve; return $?; }
    fi
    sleep 60
  done
  echo "$(ts) vLLM never answered"; return 1
}

LAST_HOST=none
export OPENAI_BASE_URL="http://localhost:$PORT/v1"
export OPENAI_API_KEY=dummy
export GEN_EVAL_CONCURRENCY=16

echo "$(ts) waiting for job $JOB"
wait_for_job || exit 1
ensure_serve || { echo "$(ts) no serve -- aborting"; exit 1; }

echo "$(ts) serve_preflight"
python3 tools/smoke/serve_preflight.py --model "$MODEL" || {
  echo "$(ts) PREFLIGHT FAILED -- not launching"; exit 1; }

# Two-request enforcement check. A server that ignores the parameter returns
# free-form prose; one that enforces it returns exactly one of the choices.
echo "$(ts) structured-outputs enforcement check"
# max_tokens must be generous and the prompt must invite a SHORT answer. This
# is a harmony/reasoning model: it emits a `reasoning` field first and only then
# `content`. With the old 24-token budget every token went to reasoning, content
# came back null, the probe read empty, GRAMMAR_OK stayed 0 and A5 -- the
# grammar arm -- was silently skipped. Verified on a live 20b serve, 2026-08-31
# it73: 24 tokens -> content null; 300 tokens -> content exactly "alpha".
probe() {
  curl -s --max-time 180 "$OPENAI_BASE_URL/chat/completions" -H 'content-type: application/json' \
    -d "{\"model\":\"$MODEL\",\"max_tokens\":300,\"messages\":[{\"role\":\"user\",\"content\":\"Reply with exactly one word.\"}]$1}" \
    | python3 -c 'import json,sys; m=json.load(sys.stdin)["choices"][0]["message"]; print((m.get("content") or "").strip())' 2>/dev/null
}
LEGACY=$(probe ',"guided_choice":["alpha","beta"]')
CURRENT=$(probe ',"structured_outputs":{"choice":["alpha","beta"]}')
echo "$(ts)   legacy guided_choice  -> ${LEGACY:0:60}"
echo "$(ts)   structured_outputs    -> ${CURRENT:0:60}"
GRAMMAR_OK=0
case "$CURRENT" in alpha|beta) GRAMMAR_OK=1;; esac
echo "$(ts) structured outputs enforced: $GRAMMAR_OK"

# run <label> <run-id> <cmd...>: health-check, run, gate-check; on any failure
# reconnect and re-run ONCE (resume redoes only missing/api_error pairs).
run() {
  local label=$1 rid=$2; shift 2
  local attempt
  for attempt in 1 2; do
    ensure_serve || { echo "$(ts) $label: no serve, skipping"; return 1; }
    echo "$(ts) ==== $label : $rid (attempt $attempt) ===="
    if "$@" && python3 -m harness gate-check "results/runs/$rid"; then
      return 0
    fi
    echo "$(ts) $label attempt $attempt FAILED"
  done
  echo "$(ts) $label FAILED twice (continuing to next arm)"
  return 1
}

run "A1 loop seed2" loop-w4dgm-120b-seed2 \
  python3 -m harness loop-eval --model "openai:$MODEL" --run-id loop-w4dgm-120b-seed2 --chains 8 --rounds 4
run "A2 loop seed3" loop-w4dgm-120b-seed3 \
  python3 -m harness loop-eval --model "openai:$MODEL" --run-id loop-w4dgm-120b-seed3 --chains 8 --rounds 4
run "A3 open seed2" open-w4dgm-120b-seed2 \
  python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id open-w4dgm-120b-seed2 --k 31
run "A4 open seed3" open-w4dgm-120b-seed3 \
  python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id open-w4dgm-120b-seed3 --k 31

# Arm ORDER is by measured target size, not arm number (it48). The nine
# arms need ~20.5h against a 12h window, so whatever runs late may be
# starved; the largest targets go first. A8 51% of TLC failures, A7 27%
# of SANY-fail rows, A5 48% parse at 78% catch, A9 13% + the 190-row
# wrapper bug, A6 last with the smallest target (11 init-violation rows).
# A8: the .cfg interface contract (docs/RALPH_STAIRCASE.md it16). 55% of the
# TLC failures on SANY-clean generations are arity mismatches, undefined
# substitution targets, or a module the cfg names and the output lacks. Same
# gen-eval shape, so A3/A4 are its control and it is comparable to A5 and A7.
export TLA_PROMPT_ARITY=1
run "A8 arity contract" arity-w4dgm-120b \
  python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id arity-w4dgm-120b --k 31
unset TLA_PROMPT_ARITY

# A7: the no-redefinition prompt block (docs/RALPH_STAIRCASE.md it10). A
# gen-eval arm with the same shape as A3/A4/A5, so A3/A4 are its control and it
# is directly comparable to the grammar arm. Redefinition is 27% of frontier
# SANY failures and 12% carry only that; it targets spec 55, which the grammar
# helps least.
export TLA_PROMPT_NO_REDEF=1
run "A7 no-redef prompt" norediff-w4dgm-120b \
  python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id norediff-w4dgm-120b --k 31
unset TLA_PROMPT_NO_REDEF

if [ "$GRAMMAR_OK" = 1 ]; then
  export TLA_GUIDED_GRAMMAR=harness/grammars/tla_module_v1.ebnf
  run "A5 grammar" grammar-w4dgm-120b \
    python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id grammar-w4dgm-120b --k 31
  unset TLA_GUIDED_GRAMMAR
else
  echo "$(ts) A5 SKIPPED -- endpoint does not enforce structured outputs"
fi

# A9: wrapper-aware signature (docs/RALPH_STAIRCASE.md it20/it21). The prompt
# demands 17 names across the 5 wrapper specs that the wrapper already
# provides, costing 190 rows to duplicate definitions. Flag-gated because
# fixing the default would change prompt_sha256 for every wrapper spec.
export TLA_PROMPT_WRAPPER_AWARE=1
run "A9 wrapper-aware" wrapaware-w4dgm-120b \
  python3 -m harness gen-eval --framing A --model "openai:$MODEL" --run-id wrapaware-w4dgm-120b --k 31
unset TLA_PROMPT_WRAPPER_AWARE

# A6: the init-violation hint (docs/RALPH_STAIRCASE.md it3/it7). Validated
# offline on the 13 recorded init-violation rows -- fires 13/13 with the flag,
# 0/13 without, and the unflagged evidence stays a prefix of the flagged one,
# so A1/A2 above remain the honest control. Runs LAST so no frozen arm sees it.
export TLA_LOOP_INIT_HINT=1
run "A6 init-hint loop" loop-w4dgm-120b-hint \
  python3 -m harness loop-eval --model "openai:$MODEL" --run-id loop-w4dgm-120b-hint --chains 8 --rounds 4
unset TLA_LOOP_INIT_HINT

echo "$(ts) ==== pooled 2x2 ===="
python3 tools/loop_multiseed.py \
  --loop results/runs/loop-w4dgm-120b results/runs/loop-w4dgm-120b-seed2 results/runs/loop-w4dgm-120b-seed3 \
  --open results/runs/open-w4dgm-120b-samesession results/runs/open-w4dgm-120b-seed2 results/runs/open-w4dgm-120b-seed3
echo "$(ts) ALL ARMS COMPLETE"
