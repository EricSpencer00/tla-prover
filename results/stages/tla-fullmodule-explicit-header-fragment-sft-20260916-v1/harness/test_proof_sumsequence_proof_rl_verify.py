import argparse
from copy import deepcopy
import json
from pathlib import Path
import pytest
from tools import proof_sumsequence_proof_rl_verify as verify


def fixture():
    tasks=[dict(id=f't{i}',split='development' if 32<=i<36 else 'train') for i in range(40)]
    arms={arm:[dict(id=t['id'],finish_reason='eos',raw_reply='BY DEF Test') for t in tasks]
          for arm in ('parent','child')}
    return tasks,arms


def test_full80_population_and_paired_known_only_transitions(tmp_path):
    tasks,arms=fixture();arms['parent'][0]['finish_reason']='token_limit';arms['child'][2]['finish_reason']='time_limit'
    calls=[]
    def checker(task,reply,work,current):
        calls.append((work.parent.name,task['id']))
        return dict(sany=1,proof=int((work.parent.name=='parent')!=(task['id']=='t1')),status='measured')
    rows,summary=verify.evaluate(tasks,arms,{},tmp_path,checker=checker)
    assert len(rows)==80 and len(calls)==78 and summary['complete']
    assert summary['arms']['parent']['requested']==40 and summary['arms']['child']['requested']==40
    assert summary['arms']['parent']['per_population']['original_train']['requested']==32
    assert summary['arms']['child']['per_population']['original_development']['requested']==4
    assert summary['arms']['child']['per_population']['new_train']['requested']==4
    assert 't0' in summary['paired']['proof']['unknown'] and 't0' not in summary['paired']['proof']['gains']
    assert summary['paired']['proof']['gains']==['t1']
    assert all(r['original_generation_role']=='child' for r in rows)
    assert json.loads((tmp_path/'rows.json').read_bytes())==rows


def test_budget_keeps_all80_unknown_no_silent_denominator_shrink(tmp_path):
    tasks,arms=fixture();ticks=iter([0]+[2500]*40+[2500]+[2500]+[5000]*41)
    def forbidden(*a,**k):raise AssertionError('No check beyond phase budget')
    rows,summary=verify.evaluate(tasks,arms,{},tmp_path,checker=forbidden,clock=lambda:next(ticks))
    assert len(rows)==80 and not summary['complete']
    assert all(r['status']=='unmeasured_budget' and r['proof'] is None for r in rows)
    assert summary['arms']['parent']['proof_unknown']==40 and summary['arms']['child']['proof_unknown']==40


def test_reordered_or_missing_population_refused(tmp_path):
    tasks,arms=fixture();arms['child'].reverse()
    with pytest.raises(ValueError,match='ordered40'):verify.evaluate(tasks,arms,{},tmp_path)


@pytest.mark.parametrize('value',[0,-1,float('nan'),float('inf'),1001,True])
def test_finite_bounds(value):
    with pytest.raises(ValueError):verify.finite_budget(value,1000)


def test_process_cleanup_and_exact_command_binding():
    command=['python','worker'];process=dict(command=command,cwd='/scope',returncode=0,output='',seconds=1.,
        execution_complete=True,cleanup_complete=True,output_complete=True,timed_out=False,output_limit=False)
    verify.audit_process(process,command,'/scope',30)
    for key in ('execution_complete','cleanup_complete','output_complete'):
        bad=dict(process,**{key:False})
        with pytest.raises(ValueError):verify.audit_process(bad,command,'/scope',30)
    with pytest.raises(ValueError):verify.audit_process(process,['python','other'],'/scope',30)


def test_exact_remote_manifest_fields(tmp_path):
    path=tmp_path/'remote.json';paths={key:'/observed/'+key for key in verify.REMOTE_KEYS}
    path.write_text(json.dumps(paths));a=argparse.Namespace(remote_paths=path)
    assert verify.remote_paths(a)==paths
    paths['evaluation_root']='relative';path.write_text(json.dumps(paths))
    with pytest.raises(ValueError):verify.remote_paths(a)


def test_target_admission_pin_rejects_before_model_or_remote_admit(tmp_path,monkeypatch):
    path=tmp_path/'receipt.json';path.write_text('{}')
    a=argparse.Namespace(target_admission=path,target_admission_sha256='0'*64)
    def forbidden(*a,**k):raise AssertionError('Must not rerun remote-only model admission')
    monkeypatch.setattr(verify.evaluation,'admit',forbidden)
    monkeypatch.setattr(verify.evaluation.training,'admit',forbidden)
    with pytest.raises(ValueError,match='authentic'):verify.target_admission(a,{},None)


def test_final_raw_extraction_and_unknown_audit(tmp_path,monkeypatch):
    tasks,arms=fixture();arms['child'][0]['finish_reason']='token_limit'
    extraction=dict(fragment=None,extractor='fixture')
    monkeypatch.setattr(verify.checks,'extract',lambda task,reply:extraction)
    def checker(task,reply,work,current):
        return dict(sany=0,proof=0,status='model_extraction',extraction=extraction,
                    raw_reply_sha256=verify.checks.sha(reply.encode()),evidence=None)
    rows,summary=verify.evaluate(tasks,arms,{},tmp_path,checker=checker)
    verify.audit_rows(tasks,arms,rows,{},tmp_path)
    rows[40]['proof']=1
    with pytest.raises(ValueError,match='Incomplete'):verify.audit_rows(tasks,arms,rows,{},tmp_path)
    rows[40]['proof']=None;rows[1]['raw_row_sha256']='0'*64
    with pytest.raises(ValueError,match='provenance'):verify.audit_rows(tasks,arms,rows,{},tmp_path)
