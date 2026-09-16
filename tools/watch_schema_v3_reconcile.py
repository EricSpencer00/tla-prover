"""Reconcile the already-submitted schema-v3 Polaris job when SSH returns.

This is a non-inference recovery helper.  It never submits, cancels, edits, or
requeues a remote job.  It only waits for a BatchMode SSH command to succeed,
checks the pinned job/result namespace, retrieves a complete receipt, and runs
the repository's independent SANY audit once.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import time


JOB = "7627237.polaris-pbs-01.hsn.cm.polaris.alcf.anl.gov"
REMOTE_ROOT = "/home/eric-spencer/tla-fullmodule-schema-grounded-sft-20260916-v3"
LOCAL_ROOT = Path("results/runs/tla-fullmodule-schema-grounded-sft-20260916-v1")
RESULT_NAME = "schema-v3-result.7627237"


def stamp():
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def run(command, timeout):
    return subprocess.run(command, capture_output=True, text=True,
                          timeout=timeout, check=False)


def log(path, event, **fields):
    record = dict(observed_utc=stamp(), event=event, **fields)
    with path.open("a", encoding="utf-8") as stream:
        stream.write(json.dumps(record, sort_keys=True) + "\n")
    print(json.dumps(record, sort_keys=True), flush=True)


def remote_status():
    command = [
        "ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10", "polaris",
        "qstat -x -f " + JOB + " 2>/dev/null || true; "
        "printf '\\nRESULT\\n'; "
        "test -f " + REMOTE_ROOT + "/result.7627237/receipt.json && echo receipt_present || true; "
        "find " + REMOTE_ROOT + "/result.7627237 -maxdepth 1 -type f -printf '%f\\n' 2>/dev/null | sort",
    ]
    return run(command, 25)


def state(output):
    for line in output.splitlines():
        if "job_state =" in line:
            return line.split("=", 1)[1].strip()
    return "unknown"


def retrieve(local_root, log_path):
    result_dir = local_root / RESULT_NAME
    result_dir.mkdir(parents=True, exist_ok=True)
    remote_result = f"polaris:{REMOTE_ROOT}/result.7627237/"
    copied = run(["rsync", "-a", remote_result, str(result_dir) + "/"], 180)
    if copied.returncode != 0:
        log(log_path, "retrieve_failed", command="rsync", stderr=copied.stderr[-1000:])
        return False
    for filename in ("train.stdout",):
        copied = run(["scp", f"polaris:{REMOTE_ROOT}/{filename}",
                      str(local_root / "schema-v3-train.stdout")], 60)
        if copied.returncode != 0:
            log(log_path, "retrieve_failed", command="scp", file=filename,
                stderr=copied.stderr[-1000:])
            return False
    qstat = run(["ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=10",
                 "polaris", "qstat -x -f " + JOB], 30)
    (local_root / "schema-v3-job.7627237-qstat-terminal.txt").write_text(
        qstat.stdout + qstat.stderr, encoding="utf-8")
    receipt = result_dir / "receipt.json"
    if not receipt.is_file():
        log(log_path, "receipt_not_complete", result=str(result_dir))
        return False
    audit = local_root / "schema-v3-independent-sany-v1"
    if audit.exists():
        log(log_path, "audit_already_present", result=str(result_dir))
        return True
    command = [
        "python3", "tools/fullmodule_independent_sany_audit.py",
        "--receipt", str(receipt),
        "--packet", "results/stages/tla-fullmodule-schema-grounded-sft-20260916-v3/packet.json",
        "--output", str(audit),
    ]
    audited = run(command, 180)
    log(log_path, "independent_audit_finished", returncode=audited.returncode,
        stdout=audited.stdout[-2000:], stderr=audited.stderr[-2000:])
    return audited.returncode == 0 and (audit / "summary.json").is_file()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--interval", type=int, default=60)
    parser.add_argument("--once", action="store_true")
    parser.add_argument("--local-root", type=Path, default=LOCAL_ROOT)
    args = parser.parse_args()
    if args.interval < 1:
        parser.error("--interval must be positive")
    local_root = args.local_root
    local_root.mkdir(parents=True, exist_ok=True)
    log_path = local_root / "schema-v3-reconcile-watch.jsonl"
    while True:
        if (local_root / RESULT_NAME / "receipt.json").is_file():
            log(log_path, "receipt_already_retrieved")
            return 0
        try:
            checked = remote_status()
        except subprocess.TimeoutExpired:
            log(log_path, "ssh_timeout")
            checked = None
        if checked is None or checked.returncode != 0:
            log(log_path, "ssh_unavailable", returncode=None if checked is None else checked.returncode)
        else:
            current = state(checked.stdout)
            present = "receipt_present" in checked.stdout
            log(log_path, "remote_observed", pbs_state=current,
                receipt_present=present)
            if present or current in {"F", "E", "C"}:
                if retrieve(local_root, log_path):
                    log(log_path, "reconciliation_complete", job=JOB)
                    return 0
        if args.once:
            return 2
        time.sleep(args.interval)


if __name__ == "__main__":
    raise SystemExit(main())
