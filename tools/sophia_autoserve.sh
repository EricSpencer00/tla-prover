#!/usr/bin/env bash
# Submit the 8-GPU bf16 serve the moment Sophia can actually run it.
#
# Why this exists (2026-08-31, it50/it51): Sophia is split in two. gpu-01..09
# are schedulable and currently full; gpu-10..22 are idle but NOT schedulable
# (a job pinned to gpu-12 queues with "Insufficient amount of resource:
# queue_tags" while the identical job on gpu-07 runs). An 8-GPU job submitted
# while that holds gets placed on an unusable node, fails to launch 21 times,
# and is system-held -- and only an admin can qrls a system hold.
#
# So do not submit and wait. Wait, then submit: poll until a SCHEDULABLE node
# has all 8 GPUs free, and only then qsub. That converts an unrecoverable hold
# into an ordinary queue wait.
#
# Prints one line when it submits, and one if the submitted job holds anyway.
set -uo pipefail
INTERVAL=${INTERVAL:-600}
PBS=${PBS:-'~/serve_vllm_w4dgm_sn.pbs'}
LOG=${LOG:-results/runs/sophia_autoserve.log}
LOCK=${LOCK:-results/runs/.runner.lock}
mkdir -p "$(dirname "$LOG")"
say() { echo "[$(date +%F_%H:%M:%S)] $*" >> "$LOG"; }
say "autoserve start (interval ${INTERVAL}s, pbs $PBS)"

while :; do
  # A node qualifies only if it is free, prod-tagged, has 8 GPUs and none
  # assigned. gpu-10..22 are excluded by the scheduler, not by us, so we also
  # require the node to be one the scheduler has actually used: it must not be
  # in the idle-but-unusable set, which we detect as "0 assigned for a long
  # time". Simplest robust proxy: only consider nodes 01-09.
  free=$(timeout 60 ssh -o BatchMode=yes -o ConnectTimeout=20 sophia '
    pbsnodes -av 2>/dev/null | awk "
      # Reset on EVERY node header. Matching only 0[1-9] left nodes 10-22
      # attributed to the previous node, so their idle records reported
      # gpu-09 as free while it was job-exclusive.
      /^sophia-gpu-/{ if (n && ok && tag && asg==0 && sched) print n
                      n=\$1; ok=0; tag=0; asg=-1
                      sched=(n ~ /gpu-0[1-9]\$/) }
      /resources_available.queue_tags = prod/{tag=1}
      /resources_available.ngpus = 8/{ok=1}
      /resources_assigned.ngpus = /{asg=\$3+0}
      END{ if (n && ok && tag && asg==0 && sched) print n }
    "' 2>/dev/null | head -1)

  if [ -n "$free" ]; then
    say "schedulable node with 8 free GPUs: $free -- submitting"
    J=$(timeout 60 ssh -o BatchMode=yes sophia "qsub $PBS" 2>&1 | tail -1)
    J=${J%%.*}
    say "submitted $J"
    echo "SOPHIA CAPACITY FREE -- submitted 8-GPU serve job $J on $free"
    sleep 90
    st=$(timeout 40 ssh -o BatchMode=yes sophia "qstat -xf $J 2>/dev/null | awk '/job_state/{s=\$3} /Hold_Types/{h=\$3} END{if (s==\"H\" && h ~ /s/) print \"HELD\"; else print s}'" 2>/dev/null | tr -d '[:space:]')
    say "job $J state=$st"
    if [ "$st" = "HELD" ]; then
      echo "job $J was system-held anyway (capacity check was not sufficient)"
      timeout 40 ssh -o BatchMode=yes sophia "qdel $J" 2>/dev/null
      say "deleted held $J; continuing to watch"
    else
      # Hand straight off to the runner rather than printing instructions: the
      # runner already waits for the job to reach R, opens the tunnel, runs
      # preflight and the enforcement probe, and resumes A1 from its 400 rows.
      # A lockfile stops a second watcher (or a re-run) starting a duplicate.
      if [ -e "$LOCK" ] || pgrep -f run_tuned_2x2_seeds.sh >/dev/null; then
        say "runner already active; not starting another"
        echo "job $J is $st, but a runner is already active -- not starting a second"
      else
        : > "$LOCK"
        say "launching runner with JOB=$J"
        JOB="$J" PORT=8321 nohup bash tools/run_tuned_2x2_seeds.sh \
             >> results/runs/autorun_tuned_seeds.log 2>&1 &
        echo "job $J is $st -- runner launched (JOB=$J, PORT=8321)"
      fi
      exit 0
    fi
  else
    say "no schedulable node with 8 free GPUs"
  fi
  sleep "$INTERVAL"
done
