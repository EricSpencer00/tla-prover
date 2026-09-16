import copy
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from tools import proof_sumsequence_repair_verify as v


@pytest.fixture
def tasks():
    return v.policy.broader.combined_tasks(v.policy.broader.load_manifests())+v.policy.extra.static_tasks()


def test_actual40_reference_extractor_controls(tasks):
    assert len(v.contexts(tasks))==40


def test_bad_reference_metadata_is_infrastructure(tasks):
    tasks[-1]['statement']='THEOREM Wrong == TRUE'
    with pytest.raises(ValueError,match='statement/prefix'):v.contexts(tasks)


def process(command,cwd):
    return dict(command=command,cwd=str(cwd),returncode=0,seconds=1,output='',timed_out=False,
        execution_complete=True,cleanup_complete=True,output_complete=True)


@pytest.mark.parametrize('mutation',['command','cwd','cleanup','seconds'])
def test_process_linkage_and_cleanup(mutation):
    p=process(['python','worker'],'/remote')
    if mutation=='command':p['command']=['other']
    elif mutation=='cwd':p['cwd']='/elsewhere'
    elif mutation=='cleanup':p['cleanup_complete']=False
    else:p['seconds']=1001
    with pytest.raises(ValueError):v.process_ok(p,['python','worker'],'/remote',1000)


@pytest.fixture
def arm(tmp_path,monkeypatch,tasks):
    from tools.proof_cuda_train import dump
    a=SimpleNamespace(generations=tmp_path/'cycle',prompts=tmp_path/'prompts.json',
        tokenizer_path=tmp_path/'tokenizer',remote_root='/remote',remote_model='/model',remote_parent='/parent')
    a.tokenizer_path.mkdir();a.prompts.write_bytes(b'{}');root=a.generations/'parent';root.mkdir(parents=True)
    inputs=[dict(id=t['id'],split=t['split'],prompt_sha256='prompt-hash',input_tokens=2,input_token_ids=[1,2],
        input_token_ids_sha256=v.digest([1,2]),rendered_prompt='prompt',rendered_prompt_sha256=v.sha(b'prompt'),status='ready') for t in tasks]
    mapped={r['id']:r for r in inputs}
    monkeypatch.setattr(v.policy.common,'encode_prompt',lambda tok,t:copy.deepcopy(mapped[t['id']]))
    monkeypatch.setattr(v.policy.common,'decode_reply',lambda *a:'')
    monkeypatch.setattr(v.policy.common,'MODEL_FILES_SHA',v.digest({}))
    admission=dict(role='parent',checkpoint_sha256=v.policy.PARENT_SHA,prompts_sha256=v.file_sha(a.prompts),
        budget=v.policy.BUDGET,implementation_sha256=v.policy.sources(),versions=v.policy.common.FIRST_VERSIONS,
        model_files={},model_files_sha256=v.digest({}),profile=v.policy.common.BUDGET['profile'],
        eos_token_ids=v.policy.common.EOS_IDS,optimizer_updates=0,cpu_environment=v.policy.CPU_ENV,input_evidence=inputs)
    rows=[dict(r,**v.policy.output_fields([128009],'')) for r in inputs]
    dump(root/'admission.json',admission);dump(root/'accounting.json',rows)
    (root/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    command=[v.PYTHON,'/remote/tools/proof_sumsequence_repair_eval.py','worker','--role','parent',
        '--expected-input-sha256',v.file_sha(a.prompts),'--expected-checkpoint-sha256',v.policy.PARENT_SHA,
        '--prompts','/remote/prompts.json','--model-path','/model','--checkpoint','/parent',
        '--admission','/remote/results/cycle/parent/admission.json','--output','/remote/results/cycle/parent']
    dump(root/'process.json',process(command,'/remote'))
    dump(root/'runtime.json',dict(allocated=1,reserved=2,optimizer_updates=0,restore_exact=True,weights_unchanged=True,cpu_threads=4))
    summary=dict(complete=True,role='parent',checkpoint_sha256=v.policy.PARENT_SHA,requested_tasks=40,
        accounted_tasks=40,generated_rows=40,unattempted_ids=[],optimizer_updates=0,full_admission_stable=True,
        memory_guard_passed=True,accounting_sha256=v.file_sha(root/'accounting.json'),process_sha256=v.file_sha(root/'process.json'),
        eos_complete=40,phase_seconds=10,returncode=0,timed_out=False,worker_timeout_seconds=970)
    dump(root/'summary.json',summary)
    return a,tasks,root


def test_exact_arm_raw_validation(arm):
    a,tasks,root=arm
    assert len(v.validate_arm(a,'parent',v.policy.PARENT_SHA,tasks,None)['rows'])==40


@pytest.mark.parametrize('mutation',['decode','truncated','order','checkpoint','optimizer','memory','source'])
def test_arm_invalid_evidence_rejected(arm,monkeypatch,mutation):
    a,tasks,root=arm
    if mutation=='decode':monkeypatch.setattr(v.policy.common,'decode_reply',lambda *a:'changed')
    elif mutation=='truncated':
        path=root/'generations.jsonl';path.write_bytes(path.read_bytes().rstrip(b'\n'))
    elif mutation=='order':
        path=root/'generations.jsonl';lines=path.read_text().splitlines();lines[0],lines[1]=lines[1],lines[0];path.write_text('\n'.join(lines)+'\n')
    elif mutation=='checkpoint':
        r=v.load(root/'summary.json');r['checkpoint_sha256']='a'*64;v.dump(root/'summary.json',r)
    elif mutation in ('optimizer','memory'):
        r=v.load(root/'runtime.json');r['optimizer_updates' if mutation=='optimizer' else 'reserved']=1 if mutation=='optimizer' else 40*1024**3
        v.dump(root/'runtime.json',r)
    else:
        r=v.load(root/'admission.json');r['implementation_sha256']={};v.dump(root/'admission.json',r)
    with pytest.raises(ValueError):v.validate_arm(a,'parent',v.policy.PARENT_SHA,tasks,None)


@pytest.fixture
def replay(tmp_path,tasks,monkeypatch):
    args=SimpleNamespace(output=tmp_path/'verify',controls=tmp_path/'controls')
    monkeypatch.setattr(v,'admit_integration_controls',lambda a:{})
    arms={role:dict(rows=[dict(finish_reason='eos',raw_reply='OBVIOUS',raw_reply_sha256=v.sha(b'OBVIOUS')) for t in tasks]) for role in ('parent','child')}
    context=v.contexts(tasks)
    monkeypatch.setattr(v,'prepare',lambda a:(tasks,context,arms))
    monkeypatch.setattr(v,'identity',lambda a,t:{'stable':True})
    calls=[]
    def check(task,fragment,work,*a):
        calls.append((task['split'],task['id']));return dict(certified=True,measured_model_outcome=True,classification='proof_success')
    monkeypatch.setattr(v,'check_original',check);monkeypatch.setattr(v.strict,'check',check)
    monkeypatch.setattr(v.seq,'audit_result',lambda *a:None)
    return args,tasks,arms,calls


def test_replay_separate_populations_and_eos_only(replay):
    a,tasks,arms,calls=replay
    arms['parent']['rows'][0]['finish_reason']='token_limit'
    arms['child']['rows'][36]['finish_reason']='time_limit'
    result=v.evaluate(a)
    assert len(calls)==78
    assert result['per_arm']['parent']['original_train']['certified']==31
    assert result['per_arm']['parent']['original_development']['certified']==4
    assert result['per_arm']['child']['new_train']['certified']==3
    assert not result['generalization_claim'] and not result['gate_claim']


def test_replay_identity_drift_never_claims_passes(replay,monkeypatch):
    a,tasks,arms,calls=replay;values=iter([{'v':1},{'v':2}])
    monkeypatch.setattr(v,'identity',lambda *a:next(values))
    with pytest.raises(ValueError,match='identity changed'):v.evaluate(a)
    summary=v.load(a.output/'summary.json')
    assert not summary['complete']
    assert all(p['certified']==0 for arm in summary['per_arm'].values() for p in arm.values())


def test_prepare_failure_all80_unknown(replay,monkeypatch):
    a,tasks,arms,calls=replay
    def fail(a):raise ValueError('training receipt invalid')
    monkeypatch.setattr(v,'prepare',fail)
    with pytest.raises(ValueError,match='training receipt'):v.evaluate(a)
    assert len(v.load(a.output/'rows.json'))==80 and not calls


def test_legacy_raw_audit_binds_process_and_target(tmp_path,monkeypatch):
    task=dict(split='development',prefix='---- MODULE Example ----\nTHEOREM Goal == TRUE\n',suffix='\n====',
        theorem_name='Goal',dependency_sha256={})
    def cmd(command,cwd,timeout):
        p=process(command,cwd);p['output']='All 1 obligations proved.\n';v.dump(Path(cwd)/'owned_process.json',p)
        return v.as_runner_tuple(p)
    monkeypatch.setattr(v.runner,'run_cmd',cmd)
    record=v.legacy.certify_fragment(task['prefix'],'OBVIOUS',task['suffix'],theorem_name='Goal',work_root=tmp_path,timeout=28.5)
    assert v.audit_original(task,'OBVIOUS',record)['classification']=='proof_success'
    with pytest.raises(ValueError):v.audit_original(dict(task,prefix=task['prefix'].replace('TRUE','FALSE')),'OBVIOUS',record)


def test_control_mutations_preserve_legacy_antecedent_and_top_theorem():
    pairs=v.control_tasks();good,bad=pairs[1]
    assert good['id']=='crdt-type-step'
    assert bad['prefix'].replace('=> FALSE',"=> TypeOK'")==good['prefix']
    assert bad['suffix']==good['suffix'] and bad['reference_fragment']==good['reference_fragment']
    assert bad['target_goal']==good['target_goal']


def test_controls_required_before_model_preparation(replay,monkeypatch):
    a,tasks,arms,calls=replay
    def fail(path):raise ValueError('controls not admitted')
    monkeypatch.setattr(v,'admit_integration_controls',fail)
    monkeypatch.setattr(v,'prepare',lambda *a:pytest.fail('prepared without controls'))
    with pytest.raises(ValueError,match='controls not admitted'):v.evaluate(a)
    assert not calls and len(v.load(a.output/'rows.json'))==80


def test_actual_legacy_false_diagnostic_requires_preserved_antecedent():
    path=v.ROOT/'results/runs/proof-sumsequence-repair-verifier-controls-20260906-v1/rows.json'
    row=v.load(path)[3];task=row['task'];record=row['result']['strict']
    assert v.negative_control_pass(task,record)
    for changed in (record['output'].replace('TypeOK /\\ [Next]_vars => FALSE','FALSE'),
                    record['output'].replace('1/6 obligations failed','2/6 obligations failed'),
                    record['output']+'\nUnknown operator: bad'):
        assert not v.negative_control_pass(task,dict(record,output=changed))
