"""Synthetic fresh-evaluation admission tests; never executes TLAPS."""
import copy
import json

import pytest

from tools import proof_fresh_controls as fresh


@pytest.fixture
def selection():
    tasks=[]
    for i in range(14):
        prefix='---- MODULE M ----\nTHEOREM T == ASSUME NEW x, x = 1 PROVE x = 1\n'
        tasks.append(dict(id='fresh-'+str(i),split='fresh_evaluation',prefix=prefix,
            reference_fragment='BY SMT',suffix='\n====\n',theorem_name='T',dependencies=[],dependency_sha256={},
            goal_offsets=[prefix.index(' ASSUME'),len(prefix)],rejection_reasons=[],
            assembled_sha256=fresh.sha((prefix+'BY SMT\n====\n').encode())))
    return dict(tasks=tasks,requested_evaluation=14,training_authorized=False)


def checker(prefix,fragment,suffix,**kwargs):
    bad='PROVE FALSE' in prefix
    return dict(contract_version='full-proof-fragment-v1',certified=not bad,status='verifier_reject' if bad else 'pass',
        returncode=10 if bad else 0,timed_out=False,proved=0 if bad else 1,total=0 if bad else 1,
        output='PROVE FALSE\n[ERROR]: 1/1 obligations failed.\n' if bad else '[INFO]: All 1 obligations proved.\n',
        sha256=fresh.sha((prefix+fragment+suffix).encode()),dependency_sha256={},command=['tlapm','--strict','--nofp','M.tla'])


def identity(selection):
    return lambda:dict(runtime='pinned',fresh_selection_sha256=fresh.selection_digest(selection))


def read(path,name):return json.loads((path/name).read_text())


def test_complete14_not_train(selection,tmp_path):
    interim=[]
    def check(*args,**kwargs):
        interim.append(read(tmp_path,'summary.json'))
        return checker(*args,**kwargs)
    result=fresh.controls(selection,tmp_path,checker=check,identity=identity(selection))
    assert result['evaluation_authorized'] and result['verification_complete']
    assert result['ledgered_controls']==28 and result['completed_controls']==28
    assert result['admitted_evaluation']==14 and not result['training_authorized']
    assert all(r['status']=='running' and not r['verification_complete'] and not r['evaluation_authorized'] for r in interim)
    manifest=read(tmp_path,'manifest.json')
    assert manifest['tasks']==selection['tasks'] and manifest['training_authorized'] is False
    assert len(read(tmp_path,'outcomes.json'))==14


@pytest.mark.parametrize('change',[
    lambda r:r.update(returncode=3),lambda r:r.update(output='Parse error'),
    lambda r:r.update(output='PROVE FALSE\n[ERROR]: 2/3 obligations failed.\n'),
    lambda r:r.update(timed_out=True),lambda r:r.update(sha256='a'*64),
    lambda r:r.update(dependency_sha256={'Injected.tla':'a'*64}),lambda r:r.update(command=['tlapm']),
])
def test_one_bad_control_never_admits_subset(selection,tmp_path,change):
    calls=0
    def check(*args,**kwargs):
        nonlocal calls
        calls+=1;row=checker(*args,**kwargs)
        if calls==2:change(row)
        return row
    result=fresh.controls(selection,tmp_path,checker=check,identity=identity(selection))
    assert result['verification_complete'] and not result['evaluation_authorized']
    assert result['admitted_evaluation']==13 and result['ledgered_controls']==28
    assert not (tmp_path/'manifest.json').exists()


def test_selection_rejection_fully_accounted(selection,tmp_path):
    selection['tasks'][0]['rejection_reasons']=['overlap']
    result=fresh.controls(selection,tmp_path,checker=checker,identity=identity(selection))
    assert result['completed_controls']==26 and result['ledgered_controls']==28
    assert [r['status'] for r in read(tmp_path,'controls.json')[:2]]==['selection_reject']*2
    assert result['verification_complete'] and not result['evaluation_authorized']


def test_budget_exhaustion_fully_accounted(selection,tmp_path,monkeypatch):
    monkeypatch.setattr(fresh.time,'monotonic',lambda:100)
    result=fresh.controls(selection,tmp_path,seconds=.5,checker=checker,identity=identity(selection))
    assert result['completed_controls']==0 and result['ledgered_controls']==28
    assert result['verification_complete'] and not result['evaluation_authorized']
    assert {r['status'] for r in read(tmp_path,'controls.json')}=={'unmeasured_budget'}


@pytest.mark.parametrize('where',['before','after','drift','missing','mismatch'])
def test_identity_failure_is_fail_closed(selection,tmp_path,where):
    calls=0
    def attest():
        nonlocal calls
        calls+=1
        if where=='before' and calls==1 or where=='after' and calls==2:raise RuntimeError('unavailable')
        result=identity(selection)()
        if where=='drift' and calls==2:result['runtime']='changed'
        if where=='missing':result.pop('fresh_selection_sha256')
        if where=='mismatch':result['fresh_selection_sha256']='a'*64
        return result
    result=fresh.controls(selection,tmp_path,checker=checker,identity=attest)
    assert not result['evaluation_authorized'] and not result['verification_complete']
    assert not result['training_authorized'] and result['ledgered_controls']==28
    assert len(read(tmp_path,'outcomes.json'))==14 and not (tmp_path/'manifest.json').exists()


def test_checker_exception_keeps_all28(selection,tmp_path):
    def broken(*args,**kwargs):raise RuntimeError('backend disappeared')
    result=fresh.controls(selection,tmp_path,checker=broken,identity=identity(selection))
    assert result['verification_complete'] and not result['evaluation_authorized']
    assert result['ledgered_controls']==28 and result['completed_controls']==0
    assert {r['status'] for r in read(tmp_path,'controls.json')}=={'control_error'}


@pytest.mark.parametrize('mutation',[
    lambda s:s['tasks'].pop(),lambda s:s['tasks'][0].update(split='train'),
    lambda s:s.update(training_authorized=True),lambda s:s.update(requested_evaluation=13),
    lambda s:s['tasks'][0].update(id=s['tasks'][1]['id']),
])
def test_no_population_or_split_relaxation(selection,tmp_path,mutation):
    mutation(selection)
    with pytest.raises(ValueError):fresh.controls(selection,tmp_path,checker=checker,identity=identity(selection))


def test_identity_callback_required(selection,tmp_path):
    with pytest.raises(TypeError):fresh.controls(selection,tmp_path,checker=checker)


@pytest.mark.parametrize('seconds,timeout',[(1001,30),(1000,31),(float('nan'),30),(1000,0)])
def test_bounded_budgets(selection,tmp_path,seconds,timeout):
    with pytest.raises(ValueError):fresh.controls(selection,tmp_path,seconds,timeout,checker,identity=identity(selection))


def test_output_not_reused(selection,tmp_path):
    fresh.controls(selection,tmp_path,checker=checker,identity=identity(selection))
    with pytest.raises(ValueError):fresh.controls(selection,tmp_path,checker=checker,identity=identity(selection))
