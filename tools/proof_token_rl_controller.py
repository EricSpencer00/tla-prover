#!/usr/bin/env python3
"""One bounded local reward delivery to the already-submitted fixed Polaris job."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from tools.proof_token_rl_rewards import rewards, REQUEST_SHA
from tools.proof_token_rl_packet import POLICY_SHA

REMOTE_ROOT = '/grand/EVITA/eric-spencer/prove-tla-token-rl-20260906-v1'
REMOTE = REMOTE_ROOT+'/results/cycle/training'
SECONDS = 3300


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def dump(path, data):
    Path(path).write_text(json.dumps(data, indent=2)+'\n')


def validate_target(remote_root, job_id):
    if not re.fullmatch(r'/grand/EVITA/eric-spencer/prove-tla-token-rl-20260906-v[1-9][0-9]*',remote_root) or not re.fullmatch(r'[0-9]+(?:\.[A-Za-z0-9_-]+)?', job_id):
        raise ValueError('Only fixed remote root and numeric PBS job ID permitted')


def job_state(result):
    if result.returncode:
        if result.returncode != 255 and re.search(r'Unknown Job Id|Unknown Job ID|Unknown job id', result.stdout+result.stderr):
            return 'missing'
        raise RuntimeError('qstat transport/query failed; job state unknown')
    states = re.findall(r'^\s*job_state\s*=\s*([A-Z])\s*$', result.stdout, re.M)
    if len(states) != 1 or states[0] not in {'Q', 'R', 'H', 'W', 'T', 'S', 'E', 'B', 'F', 'C', 'M'}:
        raise ValueError('Unrecognized qstat job state')
    return states[0]


def run(remote_root, job_id, requests, controls, output, *, execute=subprocess.run,
        bridge=rewards, clock=time.monotonic, sleep=time.sleep):
    validate_target(remote_root, job_id)
    remote=remote_root+'/results/cycle/training'
    requests = Path(requests).resolve(); controls = Path(controls).resolve(); output = Path(output).resolve()
    if sha(requests.read_bytes()) != REQUEST_SHA:
        raise ValueError('Pinned requests bytes required')
    output.mkdir(parents=True, exist_ok=False)
    started = clock()
    dump(output/'config.json', dict(remote_root=remote_root, job_id=job_id,
        seconds=SECONDS, command_timeout=30, requests_sha256=REQUEST_SHA, policy_sha256=POLICY_SHA,
        controls=str(controls), controller_sha256=sha(Path(__file__).read_bytes()),
        job_submission=False, training_authorized=False,
        scope='Deliver SANY-partial rewards to one already-submitted job; no job lifecycle ownership'))

    def log(event, **fields):
        with (output/'events.jsonl').open('a') as stream:
            stream.write(json.dumps(dict(event=event, utc=datetime.now(timezone.utc).isoformat(),
                elapsed_seconds=clock()-started, **fields))+'\n')

    def remaining():
        value = SECONDS-(clock()-started)
        if value <= 0:
            raise TimeoutError('Controller deadline exhausted')
        return value

    def command(args):
        limit = min(30, remaining())
        log('command_started', argv=args, timeout=limit)
        try:
            result = execute(args, capture_output=True, text=True, timeout=limit, check=False)
        except subprocess.TimeoutExpired:
            log('command_timeout', argv=args)
            raise TimeoutError('Transport command timed out')
        log('command_finished', argv=args, returncode=result.returncode,
            stdout=result.stdout, stderr=result.stderr)
        return result

    def ssh(cmd):
        return command(['ssh', '-oBatchMode=yes', '-oConnectTimeout=15', 'polaris', cmd])

    def require_live():
        state = job_state(ssh('qstat -xf '+job_id))
        log('job_state', state=state)
        return state not in {'F', 'C', 'E', 'M', 'missing'}

    def ready():
        result = ssh('if test -f '+remote+'/rollouts_ready.json; then cat '+remote+'/rollouts_ready.json; else exit 44; fi')
        if result.returncode == 44:
            return None
        if result.returncode:
            raise RuntimeError('Readiness transport failed')
        raw = result.stdout.encode()
        (output/'rollouts_ready.json').write_bytes(raw)
        record = json.loads(raw)
        if (set(record) != {'requests_sha256', 'rollouts_sha256', 'rows', 'policy_sha256'}
                or record['rows'] != 32 or type(record['rows']) is not int
                or record['requests_sha256'] != REQUEST_SHA or record['policy_sha256'] != POLICY_SHA
                or not isinstance(record['rollouts_sha256'], str)
                or re.fullmatch('[0-9a-f]{64}', record['rollouts_sha256']) is None):
            raise ValueError('Invalid full32 rollout readiness identity')
        return record

    def scp(source, dest):
        result = command(['scp', '-oBatchMode=yes', '-oConnectTimeout=15', source, dest])
        if result.returncode:
            raise RuntimeError('SCP transfer failed')

    def deliver(path, name):
        remaining()
        expected = sha(path.read_bytes())
        scp(str(path), 'polaris:'+remote+'/'+name+'.tmp')
        result = ssh('sha256sum '+remote+'/'+name+'.tmp')
        if result.returncode or result.stdout.split()[:1] != [expected]:
            raise ValueError('Remote temporary delivery SHA mismatch')
        if not require_live():
            raise RuntimeError('Job terminal before delivery commit')
        result = ssh('test ! -e '+remote+'/'+name+' && mv '+remote+'/'+name+'.tmp '+remote+'/'+name)
        if result.returncode:
            raise RuntimeError('Atomic delivery failed or destination already exists')
        log('file_delivered', name=name, sha256=expected)

    try:
        log('started')
        while True:
            remaining()
            live = require_live()
            record = ready()  # Inspect available readiness even for an exited job.
            if not live:
                raise RuntimeError('Job terminal or missing before reward delivery')
            if record is not None:
                break
            log('awaiting_rollouts')
            sleep(min(10, remaining()))
        local = output/'rollouts.jsonl'
        scp('polaris:'+remote+'/rollouts.jsonl', str(local))
        raw = local.read_bytes()
        if sha(raw) != record['rollouts_sha256'] or len(raw.splitlines()) != 32:
            raise ValueError('Collected rollout bytes/count differ from readiness')
        if not require_live():
            raise RuntimeError('Job terminal before local reward bridge')
        remaining(); log('bridge_started')
        bridge(requests, local, controls, output/'reward_bridge')
        remaining(); log('bridge_finished')
        reward_path = output/'reward_bridge/rewards.json'
        receipt_path = output/'reward_bridge/rewards.receipt.json'
        reward_raw = reward_path.read_bytes(); receipt_raw = receipt_path.read_bytes()
        reward = json.loads(reward_raw); receipt = json.loads(receipt_raw)
        if (sha(local.read_bytes()) != record['rollouts_sha256']
                or sha(requests.read_bytes()) != REQUEST_SHA
                or reward.get('complete') is not True or reward.get('reward_stage') != 'sany_partial'
                or len(reward.get('rows', [])) != 32 or reward.get('policy_sha256') != POLICY_SHA
                or any(r.get('requests_sha256') != REQUEST_SHA or r.get('rollouts_sha256') != record['rollouts_sha256']
                       for r in (reward, receipt))
                or receipt.get('rewards_sha256') != sha(reward_raw)
                or receipt.get('provenance_verified') is not True):
            raise ValueError('Bridge reward/receipt binding mismatch')
        deliver(reward_path, 'rewards.json')
        # Receipt is the worker's release signal; publish it strictly last.
        if reward_path.read_bytes() != reward_raw or receipt_path.read_bytes() != receipt_raw:
            raise ValueError('Local reward artifacts changed during delivery')
        deliver(receipt_path, 'rewards.receipt.json')
        summary = dict(status='delivered', job_id=job_id, elapsed_seconds=clock()-started,
            rollouts_sha256=record['rollouts_sha256'], rewards_sha256=sha(reward_raw),
            receipt_sha256=sha(receipt_raw), job_completion_verified=False)
        dump(output/'summary.json', summary); log('delivered')
        return summary
    except BaseException as exc:
        failure = dict(status='failed', error=type(exc).__name__+': '+str(exc),
                       elapsed_seconds=clock()-started, job_id=job_id, delivered=False)
        dump(output/'failure.json', failure); log('failed', error=failure['error'])
        raise


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--remote-root', required=True); p.add_argument('--job-id', required=True)
    p.add_argument('--requests', type=Path, required=True); p.add_argument('--controls', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(run(a.remote_root, a.job_id, a.requests, a.controls, a.output)))


if __name__ == '__main__':
    main()
