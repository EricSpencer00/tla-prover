import json
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor


def run_guard(state, identity):
    return subprocess.run([sys.executable, 'tools/prover_submit_guard.py', str(state), identity],
                          capture_output=True, text=True)


def test_concurrent_same_identity_has_one_claim(tmp_path):
    with ThreadPoolExecutor(max_workers=8) as pool:
        results = list(pool.map(lambda _: run_guard(tmp_path, 'syntax-v3:manifest-8b7a:launcher-e910'), range(8)))
    assert all(result.returncode == 0 for result in results)
    statuses = [json.loads(result.stdout)['status'] for result in results]
    assert statuses.count('claimed') == 1
    assert statuses.count('existing') == 7
    assert len(list(tmp_path.glob('*.json'))) == 1


def test_different_identity_gets_distinct_claim(tmp_path):
    first = run_guard(tmp_path, 'syntax-v3:manifest-8b7a:launcher-e910')
    second = run_guard(tmp_path, 'syntax-v3:manifest-8b7a:launcher-other')
    assert first.returncode == second.returncode == 0
    assert len(list(tmp_path.glob('*.json'))) == 2
