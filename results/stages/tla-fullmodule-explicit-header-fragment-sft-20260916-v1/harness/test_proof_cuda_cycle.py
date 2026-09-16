import json
from pathlib import Path
import pytest
from tools import proof_cuda_cycle as cycle
from tools.proof_cuda_cycle import check_training
from tools.proof_cuda_train import file_sha


def result(tmp_path):
    checkpoint=tmp_path/'policy_optimizer.pt';checkpoint.write_bytes(b'controlled-test-checkpoint')
    data=dict(reload_tensors_exact=True,reload_logits_exact=True,parameter_delta_l2=1.,
        evaluation_responses_forwarded=0,cuda_peak_allocated=20*1024**3,
        updates=100,attempted_train_tasks=50,checkpoint_sha256=file_sha(checkpoint))
    return data


@pytest.mark.parametrize('field,value',[('updates',0),('attempted_train_tasks',49),
    ('parameter_delta_l2',0),('parameter_delta_l2',float('nan')),
    ('reload_logits_exact',False),('cuda_peak_allocated',37*1024**3)])
def test_incomplete_or_unhealthy_training_cannot_advance(tmp_path,field,value):
    data=result(tmp_path);data[field]=value
    (tmp_path/'summary.json').write_text(json.dumps(data))
    with pytest.raises(ValueError):check_training(tmp_path)


def resume_fixture(tmp_path,monkeypatch):
    source=tmp_path/'old';source.mkdir();preflight=source/'preflight';preflight.mkdir()
    data=result(preflight);data.update(updates=1,attempted_train_tasks=1)
    (preflight/'summary.json').write_text(json.dumps(data))
    config=dict(train_input_sha256='train',prompts_sha256='prompts',model_path='/base',
                seed=20260923,train_evidence={'controlled':True})
    (source/'config.json').write_text(json.dumps(config))
    pre=dict(input_sha256='train',model_path='/base',model_files={'weight':'hash'},
             dtype_profile=cycle.PROFILE,seed=20260923,lr=1e-5,requested_updates=1,
             seconds=180,max_tokens=8192,evidence=config['train_evidence'],
             implementation_sha256={'tools/proof_cuda_train.py':file_sha(cycle.ROOT/'tools/proof_cuda_train.py')},
             torch_version='controlled')
    (preflight/'config.json').write_text(json.dumps(pre))
    for i in range(4):
        shard=source/f'base-shard{i}';shard.mkdir()
        for name in ('config.json','generations.jsonl','summary.json'):
            (shard/name).write_text('{}')
    identity=dict(arm='base',checkpoint_sha256=None,model_files={'weight':'hash'})
    monkeypatch.setattr(cycle,'saved_arm',lambda *a:identity)
    args=(source,tmp_path/'new',config,b'prompts',{}, {'weight':'hash'},object(),{'torch_version':'controlled'})
    return args,pre,identity


def test_resume_binds_old_evidence_without_mutating_or_loading_preflight(tmp_path,monkeypatch):
    args,pre,identity=resume_fixture(tmp_path,monkeypatch)
    before={str(p):file_sha(p) for p in args[0].rglob('*') if p.is_file()}
    out=cycle.validate_resume(*args)
    assert out['generated']==119 and not out['optimizer_resume']
    assert not out['preflight_checkpoint_used_for_training']
    assert before=={str(p):file_sha(p) for p in args[0].rglob('*') if p.is_file()}


@pytest.mark.parametrize('fault',['checkpoint','input','runtime','trainer','model','trained','nested'])
def test_resume_rejects_changed_or_already_trained_parent(tmp_path,monkeypatch,fault):
    args,pre,identity=resume_fixture(tmp_path,monkeypatch);args=list(args)
    if fault=='checkpoint':(args[0]/'preflight/policy_optimizer.pt').write_bytes(b'changed')
    elif fault=='input':args[2]['train_input_sha256']='other'
    elif fault=='runtime':args[-1]['torch_version']='changed'
    elif fault=='trainer':
        pre['implementation_sha256']['tools/proof_cuda_train.py']='changed'
        (args[0]/'preflight/config.json').write_text(json.dumps(pre))
    elif fault=='model':identity['model_files']={'other':'weights'}
    elif fault=='trained':(args[0]/'training').mkdir()
    elif fault=='nested':args[1]=args[0]/'nested'
    with pytest.raises(ValueError):cycle.validate_resume(*args)


def test_saved_arm_reconstructs_every_token_before_training(tmp_path,monkeypatch):
    tasks=[{'id':str(i)} for i in range(119)]
    rows={t['id']:dict(status='generated') for t in tasks}
    for i in range(4):
        p=tmp_path/f'base-shard{i}';p.mkdir()
        for name in ('config.json','summary.json'):(p/name).write_text('{}')
        (p/'generations.jsonl').write_text('')
    monkeypatch.setattr(cycle,'merge_shards',lambda *a:(rows,{'arm':'base'}))
    monkeypatch.setattr(cycle,'validate_export',lambda data:tasks)
    seen=[]
    monkeypatch.setattr(cycle,'validate_tokenization',lambda tok,t,r:seen.append(t['id']))
    assert cycle.saved_arm(tmp_path,b'',{},object())=={'arm':'base'}
    assert seen==[t['id'] for t in tasks]
    rows.pop('0')
    with pytest.raises(ValueError,match='complete119'):cycle.saved_arm(tmp_path,b'',{},object())


def test_resume_cli_skips_baseline_and_preflight_but_trains_fresh(tmp_path,monkeypatch):
    import sys
    from types import SimpleNamespace
    train=tmp_path/'train.json';train.write_text('{"evidence":{}}')
    prompts=tmp_path/'prompts.json';prompts.write_text('{}')
    output=tmp_path/'new';source=tmp_path/'old';source.mkdir()
    monkeypatch.setattr(sys,'argv',['cycle','--train-input',str(train),'--prompts',str(prompts),
        '--model-path','/base','--output',str(output),'--resume-cycle',str(source)])
    monkeypatch.setattr(cycle,'validate_packet',lambda p:None)
    monkeypatch.setattr(cycle,'validate_export',lambda p:None)
    monkeypatch.setattr(cycle,'model_files',lambda p:{})
    monkeypatch.setitem(sys.modules,'torch',SimpleNamespace(__version__='test',
        cuda=SimpleNamespace(get_device_name=lambda i:'test')))
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(__version__='test',
        AutoTokenizer=SimpleNamespace(from_pretrained=lambda *a,**kw:object())))
    events=[]
    monkeypatch.setattr(cycle,'validate_resume',lambda *a:events.append('validate') or {})
    monkeypatch.setattr(cycle,'check_training',lambda *a,**kw:{'updates':100})
    monkeypatch.setattr(cycle,'merge_shards',lambda *a:({str(i):{'status':'generated'} for i in range(119)},{}))
    def run(commands,logs,seconds):
        events.append(commands)
        for command in commands:
            dest=Path(command[command.index('--output')+1]);dest.mkdir()
            for name in ('config.json','summary.json'):(dest/name).write_text('{}')
            (dest/'generations.jsonl').write_text('')
    monkeypatch.setattr(cycle,'run_processes',run)
    cycle.main()
    assert events[0]=='validate'
    training=events[1][0]
    assert training[2]=='train' and training[training.index('--steps')+1]=='100'
    assert '--checkpoint' not in training and '--resume' not in training
    assert len(events)==3 and len(events[2])==4
    assert all(c[c.index('--checkpoint')+1]==str(output/'training/policy_optimizer.pt') for c in events[2])
    assert not (output/'preflight').exists() and not (output/'base-shard0').exists()
    assert json.loads((output/'config.json').read_text())['budgets']['total_supervisor_seconds']==2100


def test_verified_preflight_and_full_population_gate(tmp_path):
    data=result(tmp_path);(tmp_path/'summary.json').write_text(json.dumps(data))
    assert check_training(tmp_path)['updates']==100
    data.update(updates=1,attempted_train_tasks=1)
    (tmp_path/'summary.json').write_text(json.dumps(data))
    assert check_training(tmp_path,preflight=True)['updates']==1
    with pytest.raises(ValueError):check_training(tmp_path)
