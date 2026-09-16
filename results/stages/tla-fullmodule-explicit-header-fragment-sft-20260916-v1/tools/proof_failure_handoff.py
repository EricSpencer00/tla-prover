"""Persist a failure for the existing Codex recovery automation."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import socket


def record(root, phase, code, line):
    queue = Path(root) / 'results/recovery/pending'
    queue.mkdir(parents=True, exist_ok=True)
    event = dict(schema=1, phase=phase, exit_code=code, line=line,
                 hostname=socket.gethostname(), job_id=os.environ.get('PBS_JOBID'),
                 created_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                 preflight_receipt=os.environ.get('PREFLIGHT_RECEIPT'),
                 run_directory=os.environ.get('OUT'), status='needs_diagnosis')
    event['signature'] = hashlib.sha256(f'{phase}:{code}:{line}'.encode()).hexdigest()
    path = queue / (event['signature'] + '-' + str(os.getpid()) + '.json')
    with path.open('x') as stream:
        json.dump(event, stream, indent=2)
    return path


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--root', required=True)
    p.add_argument('--phase', required=True)
    p.add_argument('--code', required=True, type=int)
    p.add_argument('--line', required=True, type=int)
    a = p.parse_args()
    print(record(a.root, a.phase, a.code, a.line))
