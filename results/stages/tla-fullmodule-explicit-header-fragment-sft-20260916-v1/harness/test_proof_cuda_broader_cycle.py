import copy
import json
import sys
import types
import pytest
from tools import proof_cuda_broader_cycle as b


def training_fixture(path):
    path.mkdir()
    ids=[str(i) for i in range(32)]
    frozen=dict(model_files={'model':'hash'},train_input_sha256='train-hash',train_ids=ids,
        train_evidence={'strict':True},implementation_sha256={n:'hash' for n in b.TRAIN_SOURCES},
        admissions={'base':{'torch_version':'pinned-torch','transformers_version':'pinned-transformers'}})
    config=dict(model_files=frozen['model_files'],input_sha256=frozen['train_input_sha256'],train_ids=ids,
        evidence=frozen['train_evidence'],dtype_profile=b.PROFILE,requested_updates=100,seconds=600,
        seed=b.SEED,lr=1e-5,max_tokens=8192,cuda_cache_policy=b.CACHE_POLICY,
        implementation_sha256=frozen['implementation_sha256'],**frozen['admissions']['base'])
    (path/'policy_optimizer.pt').write_bytes(b'fake checkpoint for unit test only')
    summary=dict(reload_tensors_exact=True,reload_logits_exact=True,evaluation_responses_forwarded=0,
        train_tasks=32,attempted_train_tasks=32,updates=100,requested_updates=100,parameter_delta_l2=1.,
        cuda_peak_allocated=24*1024**3,cuda_peak_reserved=30*1024**3,
        checkpoint_sha256=b.file_sha(path/'policy_optimizer.pt'))
    steps=[dict(step=i+1,task=ids[i%32],loss=.5,gradient_norm=.4) for i in range(100)]
    b.dump(path/'config.json',config);b.dump(path/'summary.json',summary)
    (path/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in steps))
    return frozen,config,summary,steps


def test_exact32_training_and_reload_admitted(tmp_path):
    path=tmp_path/'train';frozen,_,summary,_=training_fixture(path)
    assert b.check_training(path,frozen)==summary


@pytest.mark.parametrize('fault',['reserved','allocated','nan','coverage','steps','reload','eval_leak','cache','versions','source','checkpoint','gradient'])
def test_training_guard_failures(tmp_path,fault):
    path=tmp_path/'train';frozen,config,summary,steps=training_fixture(path)
    if fault=='reserved':summary['cuda_peak_reserved']=37*1024**3
    elif fault=='allocated':summary['cuda_peak_allocated']=37*1024**3
    elif fault=='nan':summary['parameter_delta_l2']=float('nan')
    elif fault=='coverage':summary['attempted_train_tasks']=31
    elif fault=='steps':steps.pop()
    elif fault=='reload':summary['reload_logits_exact']=False
    elif fault=='eval_leak':summary['evaluation_responses_forwarded']=1
    elif fault=='cache':config['cuda_cache_policy']='disabled'
    elif fault=='versions':config['torch_version']='different'
    elif fault=='source':config['implementation_sha256']={}
    elif fault=='checkpoint':summary['checkpoint_sha256']='different'
    elif fault=='gradient':steps[0]['gradient_norm']=float('inf')
    b.dump(path/'config.json',config);b.dump(path/'summary.json',summary)
    (path/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in steps))
    with pytest.raises(ValueError):b.check_training(path,frozen)


def test_full_generation_required_before_training(tmp_path,monkeypatch):
    tasks=[{'id':str(i)} for i in range(36)]
    fake=types.SimpleNamespace(IMPLEMENTATION=(),validate_run=lambda *a:tasks)
    monkeypatch.setitem(sys.modules,'tools.proof_cuda_broader_eval',fake)
    b.dump(tmp_path/'config.json',{})
    b.dump(tmp_path/'summary.json',{'returncode':0,'termination':'complete'})
    (tmp_path/'generations.jsonl').write_text(''.join(json.dumps({'status':'generated'})+'\n' for _ in range(35)))
    with pytest.raises(ValueError,match='All36'):
        b.check_probe(tmp_path,b'',{},None,None)


def test_time_limited_reply_never_advances(tmp_path,monkeypatch):
    tasks=[{'id':str(i)} for i in range(36)]
    monkeypatch.setitem(sys.modules,'tools.proof_cuda_broader_eval',types.SimpleNamespace(
        IMPLEMENTATION=(),validate_run=lambda *a:tasks))
    b.dump(tmp_path/'config.json',{});b.dump(tmp_path/'summary.json',{'returncode':0,'termination':'complete'})
    rows=[{'status':'generated'} for _ in range(36)];rows[0]['status']='generation_time_limit'
    (tmp_path/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    with pytest.raises(ValueError,match='All36'):
        b.check_probe(tmp_path,b'',{},None,None)


def test_check_encodings_requires_actual_same_prefix(monkeypatch):
    task={'id':'train'};encoded={'status':'ready','input_tokens':2,'input_token_ids':[1,2]}
    monkeypatch.setitem(sys.modules,'tools.proof_cuda_broader_eval',types.SimpleNamespace(encode_prompt=lambda *a:encoded))
    packet={'rows':[{'id':'train'}],'token_feasibility':{'rows':[{'id':'train','prompt_tokens':2,
        'input_token_ids_sha256':b.digest([1,2]),'response_tokens':1,'total_tokens':3}]}}
    monkeypatch.setattr(b,'encode_row',lambda *a:{'input_ids':[1,2,3],'prompt_tokens':2,'response_tokens':1})
    b.check_encodings(None,packet,[task])
    monkeypatch.setattr(b,'encode_row',lambda *a:{'input_ids':[1,1,3],'prompt_tokens':2,'response_tokens':1})
    with pytest.raises(ValueError,match='Training/inference'):
        b.check_encodings(None,packet,[task])


@pytest.mark.parametrize('fail_parents',[False,True])
def test_main_phase_order_and_no_advance_on_failure(tmp_path,monkeypatch,fail_parents):
    prompts=tmp_path/'prompts.json';prompts.write_text('{}')
    output=tmp_path/'output';calls=[]
    monkeypatch.setattr(sys,'argv',['cycle','--train-input',str(tmp_path/'train.json'),
        '--prompts',str(prompts),'--model-path',str(tmp_path/'model'),
        '--parent-checkpoint',str(tmp_path/'parent.pt'),'--output',str(output),
        '--train-input-sha256','trainhash','--prompts-sha256','prompthash'])
    monkeypatch.setattr(b,'freeze',lambda *a:{})
    monkeypatch.setitem(sys.modules,'transformers',types.SimpleNamespace(
        AutoTokenizer=types.SimpleNamespace(from_pretrained=lambda *a,**kw:object())))
    monkeypatch.setattr(b,'check_probe',lambda *a:{'complete':True})
    monkeypatch.setattr(b,'check_training',lambda *a:{'checkpoint_sha256':'newchild'})
    def run(commands,logs,seconds):
        calls.append((commands,seconds))
        if fail_parents:raise RuntimeError('parent probe incomplete')
    monkeypatch.setattr(b,'run_processes',run)
    if fail_parents:
        with pytest.raises(RuntimeError,match='parent probe'):b.main()
        assert len(calls)==1 and not (output/'summary.json').exists()
        assert json.loads((output/'failure.json').read_text())['completed_phases']==[]
    else:
        b.main()
        assert [len(commands) for commands,_ in calls]==[2,1,1]
        assert [seconds for _,seconds in calls]==[1220,620,1220]
        training=calls[1][0][0]
        assert training[1].endswith('proof_cuda_train.py') and training[2]=='train'
        assert training[training.index('--steps')+1]=='100'
        assert '--checkpoint' not in training
        assert calls[2][0][0][-1]==str(output/'training/policy_optimizer.pt')
        summary=json.loads((output/'summary.json').read_text())
        assert summary['verification_pending'] and summary['proof_success_claim'] is False
