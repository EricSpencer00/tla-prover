#!/usr/bin/env bash
# Detect when Sophia can start our jobs again.
#
# Since the 2026-08-31 maintenance PBS places our jobs, fails to launch them 21
# times, and system-holds them (Hold_Types=s). That is facility-side: a minimal
# script reproduces it and the allocation is healthy. This submits one short
# job every INTERVAL seconds and prints a line ONLY when the state changes, so
# the fix is caught without anyone watching.
#
# A held job never runs, so a probe costs no node hours. Each probe is deleted
# after it is read, to keep the queue clean.
set -uo pipefail
INTERVAL=${INTERVAL:-1800}
PBS=probe_can_start.pbs
last=""

ssh -o BatchMode=yes sophia "cat > ~/$PBS" <<'EOF'
#!/bin/bash
#PBS -l select=1:ngpus=8:ncpus=256:mem=960gb
#PBS -l walltime=00:05:00
#PBS -l filesystems=home
#PBS -q single-node
#PBS -A EVITA
#PBS -N probe-can-start
echo PROBE-RAN
EOF

while :; do
  out=$(timeout 120 ssh -o BatchMode=yes -o ConnectTimeout=20 sophia "
      J=\$(qsub ~/$PBS 2>&1) || { echo SUBMIT-FAIL; exit 0; }
      J=\${J%%.*}
      sleep 45
      qstat -xf \$J 2>/dev/null | awk '
        /job_state/{s=\$3} /Hold_Types/{h=\$3}
        END{ if (s==\"H\" && h ~ /s/) print \"HELD\"; else print s }'
      qdel \$J 2>/dev/null" 2>/dev/null) || out="SSH-FAIL"
  state=$(echo "$out" | tail -1 | tr -d '[:space:]')
  case "$state" in
    HELD|SSH-FAIL|SUBMIT-FAIL|"") ;;                 # still broken; stay quiet
    *) echo "SOPHIA CAN START JOBS AGAIN (probe state=$state)"; exit 0 ;;
  esac
  [ "$state" != "$last" ] && [ -n "$last" ] && echo "probe state changed: $last -> $state"
  last=$state
  sleep "$INTERVAL"
done
