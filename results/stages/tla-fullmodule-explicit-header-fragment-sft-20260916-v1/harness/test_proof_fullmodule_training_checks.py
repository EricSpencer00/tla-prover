from types import SimpleNamespace
from unittest.mock import patch
import pytest
from tools import proof_fullmodule_training_checks as c


@pytest.fixture(scope='module')
def source_rows():return c.inputs(c.AUDIT_ROOT)


@pytest.fixture
def staged(source_rows,tmp_path):
    tasks=c.staged_tasks(source_rows,tmp_path,write=True);c.dump(tmp_path/'tasks.json',tasks)
    return SimpleNamespace(output=tmp_path,audit_root=c.AUDIT_ROOT),tasks


def fake_runtime(tasks):return dict(tasks=c.digest(tasks),java='mock-java')


def fake_check(task,candidate,work,current,timeout=30):
    negative=c.common.NEGATIVE_NAME in candidate
    module=c.common.gen_eval.extract_module(candidate)
    line=next((i+1 for i,s in enumerate(module.splitlines()) if c.common.NEGATIVE_NAME in s),0)
    return dict(sany=0 if negative else 1,status='model_sany_reject' if negative else 'pass',
        process=dict(output='***Parse Error***\nEncountered ")" at line '+str(line)+', column 42.',
            execution_complete=True,cleanup_complete=True,output_complete=True))


def test_actual128_source_and_blocked_binding(staged):
    a,tasks=staged
    assert len(tasks)==128 and len(c.blank(tasks))==256
    assert [t['index'] for t in tasks]==c.preparation.indices()
    blocked=[t for t in tasks if t['training_blocked']]
    assert len(blocked)==1 and blocked[0]['index']==1735
    assert all(t['dependencies']=={} for t in tasks)
    assert c.staged_tasks(c.inputs(c.AUDIT_ROOT),a.output)==tasks


def test_raw_source_drift_rejected(staged):
    a,tasks=staged
    from pathlib import Path
    Path(tasks[0]['source']['path']).write_text('changed')
    with pytest.raises(ValueError):c.staged_tasks(c.inputs(c.AUDIT_ROOT),a.output)


def test_protected_reconstruction_is_never_called(source_rows):
    with patch.object(c.preparation,'protected',side_effect=AssertionError('protected access')):
        assert c.inputs(c.AUDIT_ROOT)==source_rows


def test_unadmitted_dependency_fails_before_checker(source_rows,tmp_path):
    import copy
    rows=copy.deepcopy(source_rows);rows[0]['raw']['spec_text']=rows[0]['raw']['spec_text'].replace('EXTENDS','EXTENDS HiddenProtectedModule,',1)
    with pytest.raises(ValueError):c.staged_tasks(rows,tmp_path,write=True)


def test_negative_requires_intended_parse_location(staged):
    a,tasks=staged;task=tasks[0];text=c.common.checked(task['source']['path'],task['source']['sha256']).decode()
    candidate=c.common.negative(text);value=fake_check(task,candidate,None,None)
    assert c.negative_accepted(task,candidate,value)
    value['process']['output']='***Parse Error***\nEncountered ")" at line 99999, column 42.'
    assert not c.negative_accepted(task,candidate,value)


@pytest.mark.parametrize('defect',['cleanup','output','execution','unknown','generic_reject','nonparse'])
def test_incomplete_negative_never_accepted(staged,defect):
    a,tasks=staged;task=tasks[0];candidate=c.common.negative(c.common.checked(task['source']['path'],task['source']['sha256']).decode())
    value=fake_check(task,candidate,None,None)
    if defect in ('cleanup','output','execution'):value['process'][defect+'_complete']=False
    elif defect=='unknown':value['sany']=None
    elif defect=='generic_reject':value['status']='unmeasured_process'
    else:value['process']['output']='Semantic error: unknown operator'
    assert not c.negative_accepted(task,candidate,value)


def test_worker_all256_execution_and_unknown_stays_training_blocked(staged):
    a,tasks=staged
    summary=c.worker(a,checker=fake_check,raw_audit=lambda *args:None,runtime=fake_runtime)
    assert summary['complete'] and summary['target_sany_pass']==128 and summary['intended_negative_controls']==128
    assert len(summary['blocked_candidate_ids'])==1 and summary['training_ready'] is False
    assert len(c.load(a.output/'rows.json'))==256


def test_incomplete_batch_preserves_all256(staged):
    a,tasks=staged
    summary=c.worker(a,checker=lambda *args,**kw:pytest.fail('must not check after budget'),raw_audit=lambda *a:None,
        runtime=fake_runtime,clock=iter([0,1700,1701,1702]).__next__)
    assert not summary['complete'] and summary['unknown_controls']==256 and summary['accounted_controls']==256


def test_identity_drift_invalidates_completion(staged):
    a,tasks=staged;identities=iter([{'version':1},{'version':2}])
    summary=c.worker(a,checker=fake_check,raw_audit=lambda *args:None,runtime=lambda tasks:next(identities))
    assert not summary['complete'] and not summary['identity_stable']


def test_raw_auditor_error_not_model_failure(staged):
    a,tasks=staged
    with pytest.raises(ValueError,match='raw changed'):
        c.worker(a,checker=fake_check,raw_audit=lambda *args:(_ for _ in ()).throw(ValueError('raw changed')),runtime=fake_runtime)
    assert len(c.load(a.output/'rows.json'))==256


def test_process_audit_and_failed_cleanup(staged):
    a,tasks=staged;c.worker(a,checker=fake_check,raw_audit=lambda *args:None,runtime=fake_runtime)
    process=dict(command=c.command(a),cwd=str(c.ROOT),returncode=0,output='',seconds=1,timed_out=False,
        execution_complete=True,cleanup_complete=True,output_complete=True)
    c.dump(a.output/'process.json',process)
    with patch.object(c.common,'audit'):
        assert c.audit(a,runtime=fake_runtime)['complete']
        process['cleanup_complete']=False;c.dump(a.output/'process.json',process)
        with pytest.raises(ValueError):c.audit(a,runtime=fake_runtime)


def test_order_denominator_and_nonfinite_budget(staged):
    a,tasks=staged;rows=c.blank(tasks)
    with pytest.raises(ValueError):c.summarize(tasks,rows[:-1],1,True,True)
    assert not c.summarize(tasks,rows,float('nan'),True,True)['complete']


def test_mode_default_is_not_implicit_run():
    assert c.WORKER_SECONDS<c.SECONDS and c.CHECK_SECONDS==30
    assert 'choices=[\'run\',\'worker\',\'audit\']' in (c.ROOT/'tools/proof_fullmodule_training_checks.py').read_text()


def test_failed_audit_cli_is_read_only(tmp_path,monkeypatch):
    import sys
    before=set(tmp_path.iterdir())
    monkeypatch.setattr(sys,'argv',['checks','audit','--output',str(tmp_path)])
    with patch.object(c,'audit',side_effect=ValueError('read-only failure')):
        with pytest.raises(ValueError):c.main()
    assert set(tmp_path.iterdir())==before


def test_failed_outer_audit_keeps_explicit_unadmitted_receipt(source_rows,tmp_path):
    a=SimpleNamespace(output=tmp_path/'run',audit_root=c.AUDIT_ROOT)
    with patch.object(c,'run_owned',return_value=dict(execution_complete=False)),patch.object(c,'audit',side_effect=ValueError('cleanup failed')):
        with pytest.raises(ValueError):c.run(a)
    assert c.load(a.output/'receipt.json')['complete'] is False
    assert len(c.load(a.output/'rows.json'))==256
