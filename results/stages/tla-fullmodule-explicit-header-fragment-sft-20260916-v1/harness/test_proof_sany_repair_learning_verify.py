import copy
import inspect
import json
from pathlib import Path
from types import SimpleNamespace
import pytest
from tools import proof_sany_repair_learning_verify as module


def test_remote_paths_exact_absolute_inventory(tmp_path):
    path=tmp_path/'paths.json';value={k:'/remote/'+k for k in module.REMOTE_KEYS}
    module.dump(path,value);assert module.remote_paths(path)==value
    for key,replacement in [('model_path','relative'),('checkpoint','/a/../b'),('output','/a//b')]:
        bad=dict(value);bad[key]=replacement;module.dump(path,bad)
        with pytest.raises(ValueError):module.remote_paths(path)
    module.dump(path,dict(value,foreign='/elsewhere'))
    with pytest.raises(ValueError):module.remote_paths(path)


def test_authentic_receipt_hash_required(tmp_path):
    path=tmp_path/'receipt.json';module.dump(path,dict(complete=True))
    assert module.authenticated(path,module.file_sha(path))==dict(complete=True)
    with pytest.raises(ValueError,match='Authentic'):module.authenticated(path,'0'*64)


def test_local_adapter_never_calls_target_only_admission():
    text=Path(module.__file__).read_text()
    for forbidden in ('evaluation.admit(', 'evaluation.prospective_admit(', 'evaluation.validate_output(', 'learning.admit('):
        assert forbidden not in text
    assert 'learning.validate_output(' in text
    assert 'evaluation.validate_worker(' in text


@pytest.fixture
def generation(tmp_path,monkeypatch):
    remote={key:'/remote/'+key for key in module.REMOTE_KEYS}
    a=SimpleNamespace(generations=tmp_path,target_admission_sha256='a'*64)
    frozen=dict(training_admission=dict(input_sha256='b'*64))
    rows=dict(greedy40=[dict(id=str(i)) for i in range(40)],repair2=[dict(id=str(i)) for i in range(2)])
    monkeypatch.setattr(module.evaluation,'validate_worker',lambda f,p:rows)
    validated=[]
    monkeypatch.setattr(module.evaluation,'validate_rows',lambda f,phase,r,t:validated.append((phase,r,t)))
    worker=dict(elapsed_seconds=200,complete=True)
    module.dump(tmp_path/'worker_summary.json',worker)
    pre=10;post=module.evaluation.reserve(pre);seconds=module.evaluation.SECONDS-pre-post
    command=[module.common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_sany_repair_learning_eval.py'),'worker']
    for key in module.evaluation.PATHS:command+=['--'+key.replace('_','-'),remote[key]]
    command+=['--expected-input-sha256','b'*64,'--prospective',remote['prospective'],
        '--admission',str(Path(remote['output'])/'admission.json'),'--output',remote['output'],'--worker-seconds',str(seconds)]
    process=dict(command=command,cwd=remote['evaluation_root'],returncode=0,output='',seconds=201,
        timed_out=False,execution_complete=True,cleanup_complete=True,output_complete=True)
    module.dump(tmp_path/'process.json',process)
    summary=dict(worker,total_seconds=250,process_sha256=module.file_sha(tmp_path/'process.json'),
        admission_sha256='a'*64,supervisor_pre_admission_seconds=pre,
        supervisor_post_admission_reserve_seconds=post,worker_timeout_seconds=seconds)
    module.dump(tmp_path/'summary.json',summary)
    return a,frozen,remote,rows,validated


def test_actual_remote_command_audit_and_each_phase_decoder(generation):
    a,frozen,remote,rows,validated=generation
    assert module.generation_rows(a,frozen,remote,'tokenizer')==rows
    assert validated==[('greedy40',rows['greedy40'],'tokenizer'),('repair2',rows['repair2'],'tokenizer')]


@pytest.mark.parametrize('field',['execution_complete','cleanup_complete','output_complete'])
def test_incomplete_owned_process_rejected(generation,field):
    a,frozen,remote,_,_=generation
    path=a.generations/'process.json';value=module.load(path);value[field]=False;module.dump(path,value)
    summary=module.load(a.generations/'summary.json');summary['process_sha256']=module.file_sha(path)
    module.dump(a.generations/'summary.json',summary)
    with pytest.raises(ValueError,match='owned process'):module.generation_rows(a,frozen,remote,None)


def test_remote_command_cannot_be_relabelled_to_local_path(generation):
    a,frozen,remote,_,_=generation
    changed=dict(remote,checkpoint='/different/policy_optimizer.pt')
    with pytest.raises(ValueError,match='owned process'):module.generation_rows(a,frozen,changed,None)


@pytest.mark.parametrize('change',[
    lambda s:s.update(admission_sha256='0'*64),
    lambda s:s.update(supervisor_post_admission_reserve_seconds=0),
    lambda s:s.update(worker_timeout_seconds=3000),
    lambda s:s.update(total_seconds=3001),
    lambda s:s.update(elapsed_seconds=999),
])
def test_supervisor_receipt_mutation_rejected(generation,change):
    a,frozen,remote,_,_=generation
    summary=module.load(a.generations/'summary.json');change(summary);module.dump(a.generations/'summary.json',summary)
    with pytest.raises(ValueError):module.generation_rows(a,frozen,remote,None)


def test_wrong_old_rl_receipt_cannot_admit_new_sft(tmp_path):
    a=SimpleNamespace(training_output=tmp_path)
    frozen=dict(training_receipt=dict(algorithm='oldRL',optimizer_updates=1))
    with pytest.raises(ValueError,match='SFT84'):module.training_linkage(a,frozen,{}, {})


def test_missing_tokenizer_file_cannot_pass(tmp_path):
    (tmp_path/'tokenizer.json').write_text('{}')
    expected=dict(tokenizer_json='unused')
    with pytest.raises(ValueError,match='tokenizer'):
        module.tokenizer_files(tmp_path,{'tokenizer.json':'0'*64,'config.json':'a'*64})


def test_actual_selected2_binding_uses_original_statements():
    source=inspect.getsource(module.prepare)
    assert 'checks.admit_controls' in source and 'old_repair.bind_tasks' in source
    assert 'paired.validate_inputs' in source


def test_identity_drift_during_prepare_blocks_all_checks(tmp_path,monkeypatch):
    a=SimpleNamespace(output=tmp_path/'output',prospective_sha256='a'*64,target_admission_sha256='b'*64)
    for name in module.LOCAL_PATHS:
        path=tmp_path/(name+'.json');path.write_text('{}');setattr(a,name,path)
    tasks=dict(greedy40=[{'id':'one'}],repair2=[{'id':'one'}])
    monkeypatch.setattr(module.checks,'admit_tasks',lambda value:tasks['greedy40'])
    monkeypatch.setattr(module.evaluation.repair,'packet',lambda path:{})
    monkeypatch.setattr(module.old_repair,'bind_tasks',lambda packet,original:tasks['repair2'])
    calls=[]
    identities=iter([{'before':True},{'changed':True}])
    monkeypatch.setattr(module,'identity',lambda *args:next(identities))
    def prepare(args):
        calls.append('prepare');return tasks,{}, {}, {}, {}
    monkeypatch.setattr(module,'prepare',prepare)
    monkeypatch.setattr(module.paired,'evaluate',lambda *args:pytest.fail('No checks after admission drift'))
    with pytest.raises(ValueError,match='during full local admission'):module.verify(a)
    assert calls==['prepare']
    assert module.load(a.output/'identity_before.json')=={'before':True}
    assert module.load(a.output/'summary.json')['complete'] is False
