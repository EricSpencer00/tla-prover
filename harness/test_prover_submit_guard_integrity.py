import hashlib
import json
import subprocess
import sys


def run_guard(state, identity):
    return subprocess.run([sys.executable, 'tools/prover_submit_guard.py', str(state), identity],
                          capture_output=True, text=True)


def claim_path(state, identity):
    return state / f"{hashlib.sha256(identity.encode()).hexdigest()}.json"


def test_malformed_existing_claim_fails_closed(tmp_path):
    identity = 'sequence-v3:manifest-b57735df:pbs-f771fe3f'
    claim_path(tmp_path, identity).write_text(json.dumps([]) + '\n')

    result = run_guard(tmp_path, identity)

    assert result.returncode == 2
    assert 'claim exists but is malformed' in result.stderr


def test_incomplete_existing_claim_fails_closed(tmp_path):
    identity = 'sequence-v3:manifest-b57735df:pbs-f771fe3f'
    claim_path(tmp_path, identity).write_text(json.dumps({
        'identity': identity,
        'identity_sha256': hashlib.sha256(identity.encode()).hexdigest(),
    }) + '\n')

    result = run_guard(tmp_path, identity)

    assert result.returncode == 2
    assert 'claim exists but is incomplete' in result.stderr
