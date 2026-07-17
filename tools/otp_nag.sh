#!/bin/bash
# Ping Eric on Discord every 60s until the SSH ControlMaster for $1 is alive.
# Usage: tools/otp_nag.sh <sophia|polaris> [context-message]
# Eric supplies the OTP by pasting it into the Claude session (which runs
# `expect` to feed it to ssh); this script only handles the nagging.
HOST=${1:?host}
CTX=${2:-"prove-TLA autonomous loop"}
set -a; source ~/.hermes/.env 2>/dev/null; set +a
N=0
while ! ssh -O check "$HOST" >/dev/null 2>&1; do
  N=$((N+1))
  ~/.local/bin/hermes send --to "discord:$DISCORD_HOME_CHANNEL" \
    "@everyone [$N] NEED ALCF OTP for $HOST — $CTX. Paste the 8-digit key into the Claude session. (VPN on first.)" \
    >/dev/null 2>&1
  sleep 60
done
echo "master for $HOST alive after $N ping(s)"
