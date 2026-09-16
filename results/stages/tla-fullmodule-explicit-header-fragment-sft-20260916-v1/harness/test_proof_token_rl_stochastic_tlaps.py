"""Synthetic execution tests; no real model or TLAPS success evidence."""
import copy
import json
from pathlib import Path

import pytest

from tools import proof_token_rl_stochastic_tlaps as s
from tools import proof_token_rl_packet as p
from harness.test_proof_token_rl_packet import row


@pytest.fixture
def prepared():
    tasks={f't{i}':dict(id=f't{i}',prefix='---- MODULE Example ----\nTHEOREM Goal == TRUE\n',
        suffix='\n====',theorem_name='Goal',dependency_sha256={}) for i in range(8)}
    arms={}
    for arm in ('parent','child'):
        arms[arm]=[dict(request=dict(task_id=t,attempt=i,sample_id=f'{t}:{i}',
            policy_sha256=p.POLICY_SHA if arm=='parent' else s.policy.CHILD_SHA),
            extraction={'fragment':'OBVIOUS'},finish_reason='eos',sany_status='pass',
            sany_pass=True,measured_sany=True,rollout_sha256='a'*64) for t in tasks for i in range(4)]
    return tasks,arms


def passing(*args):
    return dict(certified=True,measured_model_outcome=True,classification='proof_success')


def test_all_attempts_separate_arms_not_union(prepared,tmp_path):
    tasks,arms=prepared;calls=[]
    def checker(task,fragment,work,timeout):
        calls.append((task['id'],fragment,timeout));return passing()
    result=s.evaluate(tasks,arms,tmp_path/'run',checker=checker,attest=lambda tasks:{'v':1})
    assert len(calls)==64 and all(timeout==30 for _,_,timeout in calls)
    for arm in ('parent','child'):
        assert result['per_arm'][arm]['certified_samples']==32
        assert result['per_arm'][arm]['pass_at4_tasks']==8
        assert result['per_arm'][arm]['stochastic_sample0_pass_tasks']==8
    assert not result['generalization_claim']


def test_incomplete_and_false_remain_distinct(prepared,tmp_path):
    tasks,arms=prepared
    arms['parent'][0].update(finish_reason='token_limit',sany_pass=False,measured_sany=False)
    arms['child'][0].update(sany_pass=False,measured_sany=True,sany_status='model_sany_reject')
    result=s.evaluate(tasks,arms,tmp_path/'run',checker=passing,attest=lambda t:{})
    assert result['per_arm']['parent']['unknown_samples']==1
    assert result['per_arm']['parent']['measured_rejections']==0
    assert result['per_arm']['child']['measured_rejections']==1
    assert result['per_arm']['child']['unknown_samples']==0
    assert result['per_arm']['parent']['pass_at4_tasks']==8
    assert result['per_arm']['parent']['stochastic_sample0_pass_tasks']==7


def test_arm_deadline_keeps32_each(prepared,tmp_path):
    tasks,arms=prepared
    ticks=iter([0]+[1001]*32+[2000]+[3001]*32)
    result=s.evaluate(tasks,arms,tmp_path/'run',checker=lambda *a:pytest.fail('late checker'),
        attest=lambda t:{},clock=lambda:next(ticks))
    assert all(v['accounted_samples']==v['unknown_samples']==32 for v in result['per_arm'].values())


@pytest.mark.parametrize('mutation',['missing','order','policy'])
def test_exact_population_and_policy(prepared,tmp_path,mutation):
    tasks,arms=prepared
    if mutation=='missing':arms['child'].pop()
    elif mutation=='order':arms['child'][0],arms['child'][1]=arms['child'][1],arms['child'][0]
    else:arms['child'][0]['request']['policy_sha256']=p.POLICY_SHA
    with pytest.raises(ValueError):s.evaluate(tasks,arms,tmp_path/'run',checker=passing,attest=lambda t:{})
    assert not (tmp_path/'run').exists()


def test_verifier_drift_never_completes(prepared,tmp_path):
    tasks,arms=prepared;identity=iter([{'source':'a'},{'source':'b'}])
    with pytest.raises(ValueError,match='source drift'):
        s.evaluate(tasks,arms,tmp_path/'run',checker=passing,attest=lambda t:next(identity))
    summary=json.loads((tmp_path/'run/summary.json').read_text())
    assert summary['complete'] is False and summary['per_arm']['parent']['certified_samples']==0


def test_scaffold_mutation_invalidates_completed_claim(prepared,tmp_path):
    tasks,arms=prepared
    def change(task,*args):task['prefix']='THEOREM Goal == TRUE';return passing()
    with pytest.raises(ValueError,match='source drift'):
        s.evaluate(tasks,arms,tmp_path/'run',checker=change,attest=lambda t:{})


def test_pinned_bytes_reject_mismatch(tmp_path):
    path=tmp_path/'rows';path.write_bytes(b'wrong')
    with pytest.raises(ValueError,match='hash mismatch'):s.checked(path,'a'*64)


@pytest.fixture
def sany_case(monkeypatch):
    parent=p.load_requests(s.REQUESTS.read_bytes(),s.policy.worker.REQUESTS_SHA)
    tasks={t['id']:dict(t,theorem_name='Goal') for t in parent['tasks']}
    rows=[row(r) for r in parent['requests']]
    extraction=dict(fragment='OBVIOUS',raw_sha256=p.sha(b''))
    records=[dict(sample_id=r['sample_id'],task_id=r['task_id'],finish_reason='eos',reward=1,
        status='pass',evidence=dict(extraction=extraction,sany=dict(status='pass',reward=1))) for r in rows]
    monkeypatch.setattr(s.bridge,'encode_prompt',lambda *a:{k:rows[0][k] for k in
        ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256')})
    monkeypatch.setattr(s.bridge,'decode_reply',lambda *a:'')
    monkeypatch.setattr(s.bridge,'extract',lambda *a:extraction)
    calls=[];monkeypatch.setattr(s.bridge,'audit_check',lambda *a:calls.append(a))
    return parent,tasks,rows,records,calls


def test_raw_sany_audit_all32(sany_case):
    parent,tasks,rows,records,calls=sany_case
    result=s.audit_sany(parent,tasks,None,rows,records,{},child=False)
    assert len(result)==len(calls)==32


@pytest.mark.parametrize('mutation',['tokens','decode','extraction','record_order','goal_policy'])
def test_raw_sany_binding_mutations(sany_case,monkeypatch,mutation):
    parent,tasks,rows,records,calls=sany_case
    if mutation=='tokens':rows[0]['input_token_ids']=[99];rows[0]['input_token_ids_sha256']=p.digest([99]);rows[0]['input_tokens']=1
    elif mutation=='decode':monkeypatch.setattr(s.bridge,'decode_reply',lambda *a:'changed')
    elif mutation=='extraction':records[0]['evidence']=dict(extraction={'fragment':'BY TRUE'})
    elif mutation=='record_order':records[0],records[1]=records[1],records[0]
    else:rows[0]['policy_sha256']=s.policy.CHILD_SHA
    with pytest.raises(ValueError):s.audit_sany(parent,tasks,None,rows,records,{},child=False)


def test_contract_disallows_weakened_goal_or_theorem_dependency():
    prefix='---- MODULE Example ----\nTHEOREM Goal == FALSE\n'
    with pytest.raises(ValueError):s.full.validate_fragment(prefix,'THEOREM Goal == TRUE\nOBVIOUS','\n====','Goal')


def test_worker_runner_adapter_is_scoped_and_strict(tmp_path,monkeypatch):
    source=tmp_path/'Example.tla';source.write_bytes(b'original')
    task=dict(prefix='P',suffix='S',theorem_name='Goal',source_path=str(source),
        source_sha256=p.sha(b'original'),dependency_sha256={})
    input_path=tmp_path/'input.json';s.dump(input_path,dict(task=task,fragment='F',timeout=28.5))
    original=s.runner.run_cmd;seen=[]
    def fake(prefix,fragment,suffix,**kw):
        assert s.runner.run_cmd is not original
        seen.append((prefix,fragment,suffix,kw));return {'test':'synthetic'}
    monkeypatch.setattr(s.full,'certify_fragment',fake)
    s.worker(input_path,tmp_path/'worker')
    assert s.runner.run_cmd is original and seen[0][:3]==('P','F','S')
    assert seen[0][3]['theorem_name']=='Goal' and seen[0][3]['timeout']==28.5


def test_worker_dependency_hash_mismatch_before_checker(tmp_path,monkeypatch):
    dep=tmp_path/'Dep.tla';dep.write_bytes(b'changed')
    payload=dict(task=dict(dependency_sha256={str(dep):'a'*64}),fragment='F',timeout=28)
    path=tmp_path/'input.json';s.dump(path,payload)
    monkeypatch.setattr(s.full,'certify_fragment',lambda *a,**kw:pytest.fail('unchecked dependency'))
    with pytest.raises(ValueError,match='hash mismatch'):s.worker(path,tmp_path/'worker')


def process(cmd,cwd):
    return dict(command=cmd,cwd=str(cwd),returncode=0,output='All 1 obligations proved.\n',seconds=.1,
        execution_complete=True,cleanup_complete=True,output_complete=True,timed_out=False,output_limit=False)


@pytest.mark.parametrize('flag',['cleanup_complete','execution_complete','output_complete'])
def test_outer_incomplete_never_certifies(tmp_path,monkeypatch,flag):
    def incomplete(cmd,cwd,timeout):
        result=process(cmd,cwd);result[flag]=False;return result
    monkeypatch.setattr(s,'run_owned',incomplete)
    result=s.check({},'OBVIOUS',tmp_path/'check',30)
    assert not result['certified'] and not result['measured_model_outcome']
    assert json.loads((tmp_path/'check/process.json').read_text())==result['process']


def test_outer_persisted_evidence_change_rejected(tmp_path,monkeypatch):
    monkeypatch.setattr(s,'run_owned',lambda cmd,cwd,timeout:process(cmd,cwd))
    original=s.dump
    def tamper(path,value):
        if path.name=='process.json':value=dict(value,returncode=7)
        original(path,value)
    monkeypatch.setattr(s,'dump',tamper)
    with pytest.raises(ValueError,match='Persisted dedicated process'):
        s.check({},'OBVIOUS',tmp_path/'check',30)


@pytest.mark.parametrize('cleanup',[True,False])
def test_inner_owned_cleanup_is_bound_to_strict_result(tmp_path,monkeypatch,cleanup):
    task=dict(prefix='---- MODULE Example ----\nTHEOREM Goal == TRUE\n',suffix='\n====',
        theorem_name='Goal',dependency_sha256={})
    def command(cmd,cwd,timeout):
        evidence=process(cmd,cwd);evidence['cleanup_complete']=cleanup
        s.dump(Path(cwd)/'owned_process.json',evidence)
        return s.as_runner_tuple(evidence)
    monkeypatch.setattr(s.runner,'run_cmd',command)
    record=s.full.certify_fragment(task['prefix'],'OBVIOUS',task['suffix'],theorem_name='Goal',
        work_root=tmp_path/'strict',timeout=28.5)
    diagnostic=s.audit_strict(task,'OBVIOUS',record)
    assert (diagnostic['classification']=='proof_success') is cleanup
    assert diagnostic['measured_model_outcome'] is cleanup


def test_strict_raw_process_mutation_rejected(tmp_path,monkeypatch):
    task=dict(prefix='---- MODULE Example ----\nTHEOREM Goal == TRUE\n',suffix='\n====',
        theorem_name='Goal',dependency_sha256={})
    def command(cmd,cwd,timeout):
        evidence=process(cmd,cwd);s.dump(Path(cwd)/'owned_process.json',dict(evidence,output='altered'))
        return s.as_runner_tuple(evidence)
    monkeypatch.setattr(s.runner,'run_cmd',command)
    record=s.full.certify_fragment(task['prefix'],'OBVIOUS',task['suffix'],theorem_name='Goal',
        work_root=tmp_path/'strict',timeout=28.5)
    with pytest.raises(ValueError,match='process evidence mismatch'):s.audit_strict(task,'OBVIOUS',record)
