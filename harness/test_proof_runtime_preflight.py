from tools import proof_runtime_preflight as p
import json
import pytest
import os
import subprocess
import shutil
from pathlib import Path
from tools.proof_failure_handoff import record


@pytest.mark.parametrize('rc,output,expected', [
    (3, 'Assertion failed schedule.ml:113', False),
    (1, 'No such file or directory', False),
    (None, 'timeout', False),
    (0, 'All 0 obligations proved.', True),
    (3, 'All 1 obligations proved.', True),
    (0, 'All 1 obligations proved.\nerror', True),
])
def test_infrastructure_never_admits(rc, output, expected):
    assert not p.control_passed(rc, output, expected)


def test_real_summary_contracts():
    assert p.control_passed(0, '[INFO]: All 1 obligations proved.', True)
    assert p.control_passed(0, 'Zenon error: exhausted search space\n[INFO]: All 1 obligations proved.', True)
    assert p.control_passed(1, '[ERROR]: 1/1 obligation failed.\n[ERROR]: Could not prove or check:', False)
    assert p.control_passed(3, '[ERROR]: 1/2 obligations failed.\n[ERROR]: Could not prove or check:', False)
    assert p.control_passed(10, '[ERROR]: 1/2 obligations failed.\n[ERROR]: Could not prove or check:', False)


def test_failure_handoff_retains_context(tmp_path, monkeypatch):
    monkeypatch.setenv('PBS_JOBID', '123.sophia')
    event = json.loads(record(tmp_path, 'runtime_preflight', 1, 30).read_text())
    assert event['job_id'] == '123.sophia'
    assert event['exit_code'] == 1
    assert event['status'] == 'needs_diagnosis'
    assert len(event['signature']) == 64


def test_launcher_stops_and_records_environment_failure(tmp_path):
    root = Path(__file__).resolve().parents[1]
    (tmp_path / 'tools').mkdir()
    shutil.copy(root / 'tools/proof_failure_handoff.py', tmp_path / 'tools')
    startup = tmp_path / 'bashenv'
    startup.write_text('module() { return 42; }\n')
    result = subprocess.run(['bash', str(root / 'tools/proof_candidate_rl_sophia.pbs')],
        env={**os.environ, 'PROVE_TLA_ROOT': str(tmp_path), 'BASH_ENV': str(startup)},
        capture_output=True, text=True, timeout=10)
    assert result.returncode == 42
    events = list((tmp_path / 'results/recovery/pending').glob('*.json'))
    assert len(events) == 1
    event = json.loads(events[0].read_text())
    assert event['phase'] == 'environment'
    assert event['exit_code'] == 42


def test_controls_are_distinct_and_fail_closed():
    assert '1 + 1 = 2' in p.GOOD
    assert '1 = 2' in p.BAD
    assert p.GOOD != p.BAD


def test_bad_control_cannot_be_accepted_as_good():
    assert not ('All ' in p.BAD and 'obligations proved' in p.BAD)
