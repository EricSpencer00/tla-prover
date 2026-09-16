import copy
import json
from pathlib import Path
from types import SimpleNamespace
import pytest
from tools import proof_fullmodule_holdout_verify as module


@pytest.fixture
def population():
    tasks=[dict(id=i,population='state_machine') for i in module.packet.IDS]
    raws=[dict(id=i,arm=arm,finish_reason='eos',raw_reply='module '+i)
          for arm in module.evaluation.ARMS for i in module.packet.IDS]
    return tasks,raws


def test_all60_separate_counts_and_explicit_claim_boundaries(tmp_path,population):
    tasks,raws=population;calls=[]
    def checker(task,raw,path,current,timeout):
        calls.append((task['id'],path,timeout));return dict(sany=1,status='pass')
    rows,summary=module.evaluate(tasks,raws,{},tmp_path,checker=checker)
    assert len(calls)==60 and all(c[2]==30 for c in calls)
    assert summary['complete'] and summary['arms']['parent']['sany_pass']==30 and summary['arms']['child']['sany_pass']==30
    assert summary['protected_outputs_never_train'] and summary['syntax_only']
    assert not any(summary[k] for k in ('training_authorized','pooled_score','tlc_claim','non_vacuity_claim','tlaps_claim','gate2_claim','generalization_claim'))


def test_caps_timeouts_and_infrastructure_stay_unknown(tmp_path,population):
    tasks,raws=population;raws[0]['finish_reason']='token_limit';raws[31]['finish_reason']='time_limit';calls=[]
    def checker(task,raw,path,current,timeout):
        calls.append(task['id']);return dict(sany=None,status='unmeasured_infrastructure')
    rows,summary=module.evaluate(tasks,raws,{},tmp_path,checker=checker)
    assert len(calls)==58
    assert all(r['sany'] is None for r in rows)
    assert summary['arms']['parent']['sany_unknown']==30 and summary['arms']['child']['sany_unknown']==30
    assert summary['arms']['parent']['generation_caps']==1 and summary['arms']['child']['generation_timeouts']==1


def test_budget_retains_full60_unknown(tmp_path,population):
    tasks,raws=population;time_values=iter([0]+[901]*30+[901]+[902]+[1803]*30+[1803])
    rows,summary=module.evaluate(tasks,raws,{},tmp_path,
        checker=lambda *args,**kwargs:pytest.fail('No checker after budget exhausted'),clock=lambda:next(time_values))
    assert len(rows)==60 and all(r['status']=='unmeasured_budget' for r in rows)
    assert not summary['complete']


@pytest.mark.parametrize('change',[
    lambda t,r:r.pop(),lambda t,r:r.reverse(),lambda t,r:t.reverse(),
    lambda t,r:r[0].update(id='foreign'),lambda t,r:r[0].update(arm='third'),
])
def test_wrong_population_never_admitted(population,change):
    tasks,raws=population;change(tasks,raws)
    with pytest.raises(ValueError):module.validate_inputs(tasks,raws)


def test_cap_cannot_be_relabelled_negative(tmp_path,population):
    tasks,raws=population
    for raw in raws:raw['finish_reason']='token_limit'
    rows,_=module.evaluate(tasks,raws,{},tmp_path)
    module.audit_rows(tasks,raws,rows,{},tmp_path)
    rows[0]['sany']=0
    with pytest.raises(ValueError,match='Incomplete generation'):module.audit_rows(tasks,raws,rows,{},tmp_path)


def test_raw_checker_audited_before_accepted_model_outcome(tmp_path,population,monkeypatch):
    tasks,raws=population
    rows,_=module.evaluate(tasks,raws,{},tmp_path,checker=lambda *a,**k:dict(sany=0,status='model_sany_reject'))
    calls=[];monkeypatch.setattr(module.checks,'audit',lambda *args:calls.append(args))
    module.audit_rows(tasks,raws,rows,{},tmp_path);assert len(calls)==60
    rows[0]['sany']=1
    with pytest.raises(ValueError,match='Raw syntax result'):module.audit_rows(tasks,raws,rows,{},tmp_path)


def test_local_admission_never_calls_target_only_model_admission():
    source=Path(module.__file__).read_text()
    assert 'evaluation.paired_admit(' not in source and 'evaluation.validate_output(' not in source
    assert 'learning.admit(' not in source and 'learning.validate_output(' in source
    assert 'checks.admit_controls(tasks,a.controls)' in source


def test_exact_remote_manifest(tmp_path):
    path=tmp_path/'remote.json';value={k:'/remote/'+k for k in module.REMOTE_KEYS};module.dump(path,value)
    assert module.remote_paths(path)==value
    value['checkpoint']='/remote/../other';module.dump(path,value)
    with pytest.raises(ValueError):module.remote_paths(path)


@pytest.fixture
def generation(tmp_path,monkeypatch):
    remote={k:'/remote/'+k for k in module.REMOTE_KEYS}
    a=SimpleNamespace(generations=tmp_path,expected_packet_sha256='a'*64,target_admission_sha256='b'*64)
    rows=[dict(id=i) for i in range(60)]
    monkeypatch.setattr(module.evaluation,'validate_worker',lambda frozen,output,tokenizer:rows)
    pre=10;post=module.evaluation.reserve(pre);seconds=3000-pre-post
    worker=dict(elapsed_seconds=100,worker_seconds=seconds,complete=True)
    module.dump(tmp_path/'worker_summary.json',worker)
    command=[module.prior.common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_fullmodule_holdout_eval.py'),'worker']
    for name in module.evaluation.PATHS:command+=['--'+name.replace('_','-'),remote[name]]
    command+=['--expected-packet-sha256','a'*64,'--admission',str(Path(remote['output'])/'admission.json'),
        '--output',remote['output'],'--worker-seconds',str(seconds)]
    process=dict(command=command,cwd=remote['evaluation_root'],returncode=0,output='',seconds=101,
        timed_out=False,execution_complete=True,cleanup_complete=True,output_complete=True)
    module.dump(tmp_path/'process.json',process)
    summary=dict(worker,total_seconds=140,supervisor_pre_admission_seconds=pre,
        supervisor_post_admission_reserve_seconds=post,worker_timeout_seconds=seconds,
        process_sha256=module.file_sha(tmp_path/'process.json'),admission_sha256='b'*64)
    module.dump(tmp_path/'summary.json',summary)
    return a,remote,rows


def test_actual_observed_remote_worker_command(generation):
    a,remote,rows=generation
    assert module.generation_rows(a,{},remote,None)==rows
    with pytest.raises(ValueError,match='owned process'):
        module.generation_rows(a,{},dict(remote,checkpoint='/foreign/child.pt'),None)


@pytest.mark.parametrize('field',['execution_complete','cleanup_complete','output_complete'])
def test_incomplete_owned_generation_never_admitted(generation,field):
    a,remote,_=generation
    path=a.generations/'process.json';value=module.load(path);value[field]=False;module.dump(path,value)
    summary=module.load(a.generations/'summary.json');summary['process_sha256']=module.file_sha(path);module.dump(a.generations/'summary.json',summary)
    with pytest.raises(ValueError,match='owned process'):module.generation_rows(a,{},remote,None)


def test_identity_drift_during_admission_blocks_scoring(tmp_path,population,monkeypatch):
    tasks,raws=population;a=SimpleNamespace(output=tmp_path/'output')
    for name in module.LOCAL_PATHS:
        path=tmp_path/(name+'.json');path.write_text('{}');setattr(a,name,path)
    monkeypatch.setattr(module,'admitted_packet',lambda a:tasks)
    identities=iter([{'first':1},{'second':2}]);monkeypatch.setattr(module,'identity',lambda *a:next(identities))
    monkeypatch.setattr(module,'prepare',lambda a:(tasks,raws,{},{}))
    monkeypatch.setattr(module,'evaluate',lambda *a:pytest.fail('No scoring after identity drift'))
    with pytest.raises(ValueError,match='during local admission'):module.verify(a)
    assert module.load(a.output/'summary.json')['complete'] is False
