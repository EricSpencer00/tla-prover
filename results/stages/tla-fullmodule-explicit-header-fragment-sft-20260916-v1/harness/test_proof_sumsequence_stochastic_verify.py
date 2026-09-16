import copy
import json
from pathlib import Path
from types import SimpleNamespace
import pytest
import torch
from tools import proof_sumsequence_stochastic_verify as v
from harness.test_proof_token_rl_packet import row as rollout


@pytest.fixture
def raw():return (v.ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json').read_bytes()


@pytest.fixture
def tasks():
    all_tasks=v.sampling.common.export_tasks.__globals__['combined_tasks'](v.sampling.common.export_tasks.__globals__['load_manifests']())
    return {t['id']:t for t in all_tasks if t['id'] in v.IDS}


def test_actual8_reference_extractor_contexts(tasks):
    assert list(tasks)==v.IDS
    for task in tasks.values():
        result=v.bridge.extract(task['reference_fragment'],task)
        assert result['fragment'].strip()==task['reference_fragment'].strip()


def initialized():
    return [dict(arm=arm,task_id=task,attempt=i,proof=1,sany=1,finish_reason='eos',raw_reply_sha256=str(i))
        for arm in ('parent','child') for task in v.IDS for i in range(4)]


def test_group_variance_requires_all4_actual_complete_measured():
    rows=initialized()
    rows[0]['proof']=0;rows[2]['proof']=0
    rows[4]['proof']=0;rows[5]['proof']=None
    rows[8]['proof']=0;rows[9]['finish_reason']='token_limit'
    result=v.summarize(rows,True)['parent']
    assert result['variance_eligible_groups']==1
    first=result['tasks'][v.IDS[0]]
    assert first['proof_variance']==.25 and first['pass_at4'] and not first['sample0_proved']
    assert first['distinct_outputs']==4
    assert not result['tasks'][v.IDS[1]]['complete_measured_group']
    assert not result['tasks'][v.IDS[2]]['complete_measured_group']
    assert result['requested_samples']==32 and result['requested_tasks']==8


def test_unfinished_replay_cannot_claim_proof_or_variance():
    result=v.summarize(initialized(),False)
    assert all(a['proof_passes']==a['pass_at4_tasks']==a['variance_eligible_groups']==0 for a in result.values())


@pytest.mark.parametrize('sany,proof',[(1,1),(1,0),(1,None),(0,0),(None,None)])
def test_pipeline_partial_unknown_and_strict_feedback(tmp_path,monkeypatch,sany,proof):
    task={'id':'example'};work=tmp_path/'check'
    sv=dict(reward=sany,status='pass' if sany==1 else 'model_sany_reject' if sany==0 else 'unmeasured_infrastructure')
    monkeypatch.setattr(v.bridge,'check',lambda *a,**kw:sv)
    monkeypatch.setattr(v.bridge,'audit_check',lambda *a:None)
    calls=[]
    def strict(*a):
        calls.append(1);return dict(certified=proof==1,measured_model_outcome=proof is not None,
            classification='proof_success' if proof==1 else 'unproved_obligation' if proof==0 else 'unmeasured_infrastructure')
    monkeypatch.setattr(v.strict,'check',strict);monkeypatch.setattr(v.repair.seq,'audit_result',lambda *a:None)
    result=v.check(task,'OBVIOUS',work,{'sany':{}})
    v.audit_check(task,'OBVIOUS',result,work,{'sany':{}})
    assert result['proof']==proof and result['sany']==sany and len(calls)==int(sany==1)
    with pytest.raises(ValueError):v.audit_check(dict(task,id='weakened'),'OBVIOUS',result,work,{'sany':{}})


@pytest.fixture
def arm(raw,tmp_path,monkeypatch):
    root=tmp_path/'cycle/parent';root.mkdir(parents=True)
    a=SimpleNamespace(generations=tmp_path/'cycle',broader_prompts=tmp_path/'prompts.json',
        parent_checkpoint=tmp_path/'parent.pt',tokenizer_path=tmp_path/'tokenizer',
        remote_root='/remote',remote_model='/model',remote_parent='/parent')
    a.broader_prompts.write_bytes(raw);a.tokenizer_path.mkdir();a.parent_checkpoint.write_bytes(b'fake')
    evaluation=v.sampling.derive_requests(raw,'parent')
    encodings=[dict(id=t['id'],split='train',prompt_sha256=t['prompt_sha256'],input_tokens=2,
        input_token_ids=[1,2],input_token_ids_sha256=v.digest([1,2]),rendered_prompt='prompt',
        rendered_prompt_sha256=v.sha(b'prompt'),status='ready') for t in evaluation['tasks']]
    mapped={r['id']:r for r in encodings}
    monkeypatch.setattr(v.sampling.common,'encode_prompt',lambda tok,t:copy.deepcopy(mapped[t['id']]))
    monkeypatch.setattr(v.sampling.common,'decode_reply',lambda *a:'')
    monkeypatch.setattr(v.sampling.common,'MODEL_FILES_SHA',v.digest({}))
    originalsha=v.file_sha
    monkeypatch.setattr(v,'file_sha',lambda p:v.sampling.POLICIES['parent'] if Path(p)==a.parent_checkpoint else originalsha(p))
    original_load=torch.load
    monkeypatch.setattr(torch,'load',lambda p,**kw:{} if Path(p)==a.parent_checkpoint else original_load(p,**kw))
    monkeypatch.setattr(v.sampling,'checkpoint_state',lambda *a:'checkpoint-config')
    admission=dict(evaluation=evaluation,checkpoint_sha256=v.sampling.POLICIES['parent'],
        checkpoint_config_sha256='checkpoint-config',model_files={},model_files_sha256=v.digest({}),
        versions=v.sampling.common.FIRST_VERSIONS,dtype_profile=v.sampling.train.PROFILE,
        eos_token_ids=v.sampling.EOS_IDS,encodings=encodings,implementation_sha256={n:originalsha(v.ROOT/n) for n in v.sampling.SOURCES})
    for p in (root/'admission.json',a.generations/'parent-admission.json'):v.dump(p,admission)
    rows=[rollout(request) for request in evaluation['requests']]
    for name in ('rollouts','events'):(root/(name+'.jsonl')).write_text(''.join(json.dumps(r)+'\n' for r in rows))
    rng={}
    for name in ('before','after'):
        p=root/('sampling_generator_'+name+'.pt');torch.save(torch.tensor([1,2],dtype=torch.uint8),p);rng[name]=originalsha(p)
    command=[v.repair.PYTHON,'/remote/tools/proof_sumsequence_stochastic_eval.py','worker',
        '--broader-prompts','/remote/prompts.json','--model-path','/model','--checkpoint','/parent',
        '--output','/remote/results/cycle/parent','--arm','parent','--admission','/remote/results/cycle/parent/admission.json','--worker-seconds','1490.0']
    process=dict(command=command,cwd='/remote',returncode=0,output='',seconds=100,timed_out=False,
        execution_complete=True,cleanup_complete=True,output_complete=True)
    v.dump(root/'process.json',process)
    worker=dict(phase_complete=True,identity_stable=True,failure=None,optimizer_updates=0,
        frozen_weights_verified=True,checkpoint_restored_exactly=True,checkpoint_sha256=v.sampling.POLICIES['parent'],
        verification_pending=True,generalization_claim=False,**v.sampling.accounting(rows),
        rollouts_sha256=originalsha(root/'rollouts.jsonl'),sampling_generator_sha256=rng,
        elapsed_seconds=99,memory=dict(allocated=1,reserved=2))
    v.dump(root/'worker_summary.json',worker)
    v.dump(root/'summary.json',dict(worker,total_arm_seconds=101,process_sha256=originalsha(root/'process.json')))
    return a,admission,root


def test_actual_full_raw_arm_validation(arm):
    a,admission,root=arm
    rows,state=v.validate_arm(a,'parent',admission,object())
    assert len(rows)==32 and state.dtype==torch.uint8


@pytest.mark.parametrize('mutation',['events','decode','rng','cleanup','logps','memory','checkpoint','budget'])
def test_arm_fail_closed_mutations(arm,monkeypatch,mutation):
    a,admission,root=arm
    if mutation=='events':(root/'events.jsonl').write_text('{}\n')
    elif mutation=='decode':monkeypatch.setattr(v.sampling.common,'decode_reply',lambda *a:'altered')
    elif mutation=='rng':(root/'sampling_generator_before.pt').write_bytes(b'wrong')
    elif mutation=='cleanup':
        p=v.load(root/'process.json');p['cleanup_complete']=False;v.dump(root/'process.json',p)
    elif mutation=='logps':
        rows=v.read_rows(root/'rollouts.jsonl');rows[0]['selected_token_logprobs']=[1.]
        (root/'rollouts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    elif mutation=='memory':
        for name in ('summary','worker_summary'):
            p=v.load(root/(name+'.json'));p['memory']['reserved']=40*1024**3;v.dump(root/(name+'.json'),p)
    elif mutation=='checkpoint':admission['checkpoint_config_sha256']='changed'
    else:admission['evaluation']['budget']=dict(v.sampling.BUDGET,seed=7)
    with pytest.raises(ValueError):v.validate_arm(a,'parent',admission,object())


@pytest.fixture
def replay(tasks,raw,tmp_path,monkeypatch):
    a=SimpleNamespace(output=tmp_path/'replay')
    arms={arm:[rollout(r) for r in v.sampling.derive_requests(raw,arm)['requests']] for arm in ('parent','child')}
    monkeypatch.setattr(v,'prepare',lambda a:(tasks,arms))
    monkeypatch.setattr(v,'identity',lambda *a:{'verifier':{'sany':{}},'stable':True})
    monkeypatch.setattr(v.bridge,'extract',lambda *a:{'fragment':'OBVIOUS'})
    calls=[]
    def check(task,fragment,work,current):calls.append(task['id']);return dict(proof=1,sany=1,status='proof_success')
    monkeypatch.setattr(v,'check',check);monkeypatch.setattr(v,'audit_check',lambda *a:None)
    return a,arms,calls


def test_replay_eos_only_and_complete64(replay):
    a,arms,calls=replay
    arms['parent'][0]['finish_reason']='token_limit';arms['child'][0]['finish_reason']='time_limit'
    summary=v.evaluate(a)
    assert len(calls)==62 and summary['requested_samples']==summary['accounted_samples']==64
    assert all(r['proof_passes']==31 and r['variance_eligible_groups']==0 for r in summary['per_arm'].values())


def test_admission_failure_initializes_all64(replay,monkeypatch):
    a,arms,calls=replay
    def fail(a):raise ValueError('missing actual controls')
    monkeypatch.setattr(v,'prepare',fail)
    with pytest.raises(ValueError):v.evaluate(a)
    assert len(v.load(a.output/'rows.json'))==64 and not calls


def test_source_drift_rejects_final_claims(replay,monkeypatch):
    a,arms,calls=replay;states=iter([{'verifier':{'sany':{}},'v':1},{'verifier':{'sany':{}},'v':2}])
    monkeypatch.setattr(v,'identity',lambda *a:next(states))
    with pytest.raises(ValueError,match='drift'):v.evaluate(a)
    assert all(r['proof_passes']==0 for r in v.load(a.output/'summary.json')['per_arm'].values())


def test_extraction_metadata_failure_is_not_model_negative(replay,monkeypatch):
    a,arms,calls=replay
    def missing_context(*args):raise KeyError('target_goal')
    monkeypatch.setattr(v.bridge,'extract',missing_context)
    with pytest.raises(KeyError):v.evaluate(a)
    rows=v.load(a.output/'rows.json')
    assert len(rows)==64 and all(r['proof'] is None for r in rows)
    assert not calls and not v.load(a.output/'summary.json')['complete']


def test_invalid_reference_context_blocks_task_packet(tasks,monkeypatch):
    monkeypatch.setattr(v.bridge,'prepare',lambda *a:({},tasks,object()))
    monkeypatch.setattr(v.bridge,'extract',lambda *a:{'fragment':None})
    with pytest.raises(ValueError,match='reference extractor'):v.task_packet()
