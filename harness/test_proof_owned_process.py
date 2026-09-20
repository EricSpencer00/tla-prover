"""Own synthetic trees only; every directly launched process is reaped."""
import os
import json
from pathlib import Path
import signal
import subprocess
import sys
import time
from types import SimpleNamespace

import psutil
import pytest

from harness import proof_owned_process as owned


def command(parent_sleep):
    child='import os,time;print("CHILD",os.getpid(),flush=True);time.sleep(60)'
    parent=('import subprocess,sys,time,os;'
            'p=subprocess.Popen([sys.executable,"-c",'+repr(child)+'],start_new_session=True);'
            'print("ROOT",os.getpid(),flush=True);time.sleep('+str(parent_sleep)+')')
    return [sys.executable,'-u','-c',parent]


def assert_gone(result):
    # A detached process can briefly remain an init-owned zombie on macOS.
    for row in result['owned_processes']:
        process=owned.same_process(row['pid'],row['created'])
        assert process is None or process.status()==psutil.STATUS_ZOMBIE,result


def emergency_cleanup(result):
    # Only exact PID+creation-time identities returned for this test's tree.
    for row in result.get('owned_processes',[]):
        process=owned.same_process(row['pid'],row['created'])
        if process is not None:
            try:process.kill()
            except psutil.NoSuchProcess:pass


def run_logged(command,path,timeout,**kwargs):
    result=owned.run_owned(command,path,timeout,**kwargs)
    (path/'owned-process-evidence.json').write_text(json.dumps(result,indent=2))
    return result


def test_detached_child_after_normal_exit_is_owned_and_stopped(tmp_path):
    result={}
    try:
        result=run_logged(command(.35),tmp_path,3)
        assert result['returncode']==0 and result['execution_complete'],result
        assert 'CHILD' in result['output'] and 'ROOT' in result['output']
        assert len(result['owned_processes'])>=2
        assert len({r['pgid'] for r in result['owned_processes']})>=2
        assert result['cleanup_complete'] and result['output_complete']
        assert_gone(result)
    finally:emergency_cleanup(result)


def test_timeout_cleans_detached_child_and_pipe(tmp_path):
    result={}
    try:
        result=run_logged(command(60),tmp_path,1.5)
        assert result['timed_out'] and result['cleanup_complete'],result
        assert result['output_complete'] and len(result['owned_processes'])>=2
        assert result['seconds']<2
        assert owned.as_runner_tuple(result)[0]==-1
        assert_gone(result)
    finally:emergency_cleanup(result)


def test_unrelated_process_survives(tmp_path):
    unrelated=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)'],start_new_session=True)
    result={}
    try:
        result=run_logged(command(.3),tmp_path,3)
        assert unrelated.poll() is None
        assert unrelated.pid not in {r['pid'] for r in result['owned_processes']}
        assert result['cleanup_complete']
    finally:
        emergency_cleanup(result)
        unrelated.kill();unrelated.wait(timeout=5)


def test_output_limit_is_not_success(tmp_path):
    result=run_logged([sys.executable,'-c','print("x"*100000)'],tmp_path,2,max_output_bytes=64)
    assert result['output_limit'] and not result['execution_complete']
    assert len(result['output'])==64 and owned.as_runner_tuple(result)[0]==-1
    assert_gone(result)


def test_nonzero_returncode_preserved(tmp_path):
    result=run_logged([sys.executable,'-c','print("failure");raise SystemExit(10)'],tmp_path,2)
    assert result['execution_complete'] and owned.as_runner_tuple(result)[0]==10
    assert owned.as_runner_tuple(result)[3] is False
    assert_gone(result)


def test_pid_reuse_never_signalled(monkeypatch):
    calls=[]
    fake=SimpleNamespace(create_time=lambda:2.,is_running=lambda:True,
                         send_signal=lambda s:calls.append(s))
    monkeypatch.setattr(owned.psutil,'Process',lambda pid:fake)
    assert owned.same_process(123,1.) is None
    tracker=object.__new__(owned.Ownership);tracker.owned={123:1.};tracker.groups={};tracker.errors=[];tracker.signals=[]
    tracker.terminate()
    assert not calls and not tracker.signals


def test_permission_failure_recorded_no_broad_fallback(monkeypatch):
    def denied(sig):raise psutil.AccessDenied(123)
    fake=SimpleNamespace(create_time=lambda:1.,is_running=lambda:True,status=lambda:'running',
                         children=lambda recursive:[],send_signal=denied)
    monkeypatch.setattr(owned.psutil,'Process',lambda pid:fake)
    monkeypatch.setattr(owned.os,'getpgid',lambda pid:123)
    tracker=object.__new__(owned.Ownership);tracker.owned={123:1.};tracker.groups={};tracker.errors=[];tracker.signals=[]
    tracker.terminate()
    assert tracker.errors==['signal_denied:123'] and tracker.alive()==[(123,1.)]


@pytest.mark.parametrize('field',['cleanup_complete','output_complete','execution_complete'])
def test_adapter_cannot_represent_incomplete_as_success(field):
    result=dict(returncode=0,output='All obligations proved',seconds=1.,timed_out=False,
                cleanup_complete=True,output_complete=True,execution_complete=True)
    result[field]=False
    assert owned.as_runner_tuple(result)[0]==-1 and owned.as_runner_tuple(result)[3]


@pytest.mark.parametrize('timeout',[0,-1,float('nan'),float('inf')])
def test_invalid_budget_starts_nothing(tmp_path,timeout):
    with pytest.raises(ValueError):owned.run_owned(['must-not-exist'],tmp_path,timeout)


def test_initial_ownership_race_is_unmeasured_and_root_reaped(tmp_path,monkeypatch):
    def missing(pid):raise psutil.NoSuchProcess(pid)
    monkeypatch.setattr(owned,'Ownership',missing)
    result=run_logged([sys.executable,'-c','pass'],tmp_path,2)
    assert not result['execution_complete'] and not result['cleanup_complete']
    assert result['root_reaped'] and result['errors'][0].startswith('ownership_initialization_failed:')
    assert owned.as_runner_tuple(result)[0]==-1


def test_cleanup_overrun_cannot_report_complete(tmp_path,monkeypatch):
    real=owned.time.monotonic;offset=[0.];original=owned.Ownership.alive
    def later(self):
        rows=original(self)
        if not rows:offset[0]=10.
        return rows
    monkeypatch.setattr(owned.Ownership,'alive',later)
    monkeypatch.setattr(owned.time,'monotonic',lambda:real()+offset[0])
    result=run_logged([sys.executable,'-c','pass'],tmp_path,2)
    assert result['seconds']>2 and result['timed_out'] and not result['execution_complete']
    assert owned.as_runner_tuple(result)[0]==-1
