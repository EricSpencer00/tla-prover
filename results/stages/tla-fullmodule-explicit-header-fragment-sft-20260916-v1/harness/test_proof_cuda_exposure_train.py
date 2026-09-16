"""Isolated512-step profile: fake artifacts and tiny CPU optimizer, no GPU."""
from collections import Counter
import json
from types import SimpleNamespace

import pytest

from tools import proof_cuda_exposure_train as train
from tools.proof_cuda_train import schedule as original_schedule


def test_exact_sixteen_epochs_and_old_prefix():
    indices=train.schedule(32,512,train.SEED)
    assert indices[:100]==original_schedule(32,100,train.SEED)
    assert Counter(indices)=={i:16 for i in range(32)}
    assert all(set(indices[i:i+32])==set(range(32)) for i in range(0,512,32))
    with pytest.raises(ValueError):original_schedule(32,512,train.SEED)


@pytest.mark.parametrize('count,steps',[(31,512),(32,100),(6,512),(32,513)])
def test_schedule_rejects_other_profiles(count,steps):
    with pytest.raises(ValueError):train.schedule(count,steps,train.SEED)


@pytest.fixture
def args(tmp_path):
    return SimpleNamespace(steps=512,seed=train.SEED,seconds=600,max_tokens=8192,lr=1e-5,
        expected_input_sha256=train.INPUT_SHA,input=tmp_path/'input.json',model_path=tmp_path/'model',output=tmp_path/'run')


@pytest.mark.parametrize('changes',[dict(steps=100),dict(seed=1),dict(seconds=601),dict(max_tokens=4096),dict(lr=2e-5),
                                    dict(expected_input_sha256='a'*64)])
def test_only_exact_production_profile(args,changes):
    train.validate_args(args)
    for k,v in changes.items():setattr(args,k,v)
    with pytest.raises(ValueError):train.validate_args(args)


def test_output_isolation(args):
    args.output=args.model_path/'run'
    with pytest.raises(ValueError):train.validate_args(args)


@pytest.mark.parametrize('allocated,reserved',[(1,train.MEMORY_LIMIT+1),(train.MEMORY_LIMIT+1,1),(0,1),(float('nan'),1)])
def test_memory_is_not_waived(allocated,reserved):
    with pytest.raises(ValueError):train.memory_guard(allocated,reserved)


def test_memory_boundary():
    train.memory_guard(train.MEMORY_LIMIT,train.MEMORY_LIMIT)


@pytest.fixture
def artifacts(tmp_path,monkeypatch):
    model={'model.safetensors':'a'*64};monkeypatch.setattr(train,'MODEL_FILES_SHA',train.digest(model))
    frozen=dict(model_files=model,train_input_sha256=train.INPUT_SHA,train_ids=train.TRAIN_IDS[:],train_evidence={'frozen':True},
        implementation_sha256={n:'b'*64 for n in train.SOURCES},
        admissions={'base':{'torch_version':'torch-test','transformers_version':'transformers-test'}})
    names=['final.'+str(i) for i in range(9)]
    config=dict(model_files=model,input_sha256=train.INPUT_SHA,train_ids=train.TRAIN_IDS,evidence=frozen['train_evidence'],
        dtype_profile=train.PROFILE,algorithm=train.ALGORITHM,requested_updates=512,seconds=600,seed=train.SEED,lr=1e-5,
        max_tokens=8192,cuda_cache_policy=train.CACHE_POLICY,implementation_sha256=frozen['implementation_sha256'],
        training_epochs=16,initialization='fresh immutable base and fresh AdamW; no checkpoint resume',
        task_schedule=[train.TRAIN_IDS[i] for i in train.schedule(32,512,train.SEED)],
        torch_version='torch-test',transformers_version='transformers-test',trainable_parameters=218112000,
        trainable_names=names,trainable_dtypes={n:'torch.float32' for n in names},all_parameter_dtypes=['torch.bfloat16','torch.float32'])
    checkpoint=tmp_path/'policy_optimizer.pt';checkpoint.write_bytes(b'fake-checkpoint-only-validator-mechanics')
    summary=dict(reload_tensors_exact=True,reload_logits_exact=True,evaluation_responses_forwarded=0,
        train_tasks=32,attempted_train_tasks=32,updates=512,requested_updates=512,stop_reason='step_budget',
        task_update_counts={i:16 for i in train.TRAIN_IDS},algorithm=train.ALGORITHM,parameter_delta_l2=1.,
        cuda_peak_allocated=30*1024**3,cuda_peak_reserved=35*1024**3,checkpoint_sha256=train.file_sha(checkpoint))
    steps=[dict(step=i+1,task=t,loss=1.,gradient_norm=.1) for i,t in enumerate(config['task_schedule'])]
    def write():
        train.dump(tmp_path/'config.json',config);train.dump(tmp_path/'summary.json',summary)
        (tmp_path/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in steps))
    write()
    return tmp_path,frozen,config,summary,steps,write


def test_validate_complete_artifacts(artifacts):
    path,frozen,*_=artifacts
    assert train.validate_training(path,frozen)['updates']==512


@pytest.mark.parametrize('mutation',[
    lambda c,s,r:c.update(seed=123),lambda c,s,r:c.update(requested_updates=100),
    lambda c,s,r:c.update(torch_version='changed'),lambda c,s,r:c.update(trainable_parameters=1),
    lambda c,s,r:s.update(updates=511),lambda c,s,r:s.update(reload_logits_exact=False),
    lambda c,s,r:s.update(cuda_peak_reserved=37*1024**3),lambda c,s,r:s.update(parameter_delta_l2=0),
    lambda c,s,r:s['task_update_counts'].update({train.TRAIN_IDS[0]:15}),
    lambda c,s,r:r.pop(),lambda c,s,r:r[0].update(task=r[1]['task']),
    lambda c,s,r:r[0].update(loss=float('nan')),
])
def test_artifacts_reject_bad_completion(artifacts,mutation):
    path,frozen,config,summary,steps,write=artifacts
    mutation(config,summary,steps);write()
    with pytest.raises(ValueError):train.validate_training(path,frozen)


def test_checkpoint_bytes_bound(artifacts):
    path,frozen,*_=artifacts
    (path/'policy_optimizer.pt').write_bytes(b'changed')
    with pytest.raises(ValueError,match='Checkpoint'):train.validate_training(path,frozen)


def test_tiny_cpu_optimizer_really_updates_all512():
    import torch
    class Tiny(torch.nn.Module):
        def __init__(self):
            super().__init__();self.weight=torch.nn.Parameter(torch.tensor([.5],dtype=torch.float32))
        def forward(self,input_ids,labels,use_cache):
            return SimpleNamespace(loss=(self.weight-float(labels[0,-1])).square().sum())
    net=Tiny();initial=net.weight.detach().clone()
    rows=[{'id':i} for i in train.TRAIN_IDS]
    encoded=[dict(input_ids=[0,1],labels=[-100,1],response_tokens=1) for _ in rows]
    emitted=[]
    optimizer,metrics,indices=train.train_steps(net,{'weight':net.weight},encoded,rows,512,train.SEED,1e-5,20,'cpu',emitted.append,clear_cache=False)
    assert len(metrics)==len(emitted)==512
    assert Counter(r['task'] for r in metrics)=={i:16 for i in train.TRAIN_IDS}
    assert not torch.equal(initial,net.weight)
    assert int(optimizer.state[net.weight]['step'])==512


def test_first100_optimizer_losses_and_weights_match_original():
    import torch
    from tools import proof_cuda_train as original
    class Tiny(torch.nn.Module):
        def __init__(self):
            super().__init__();self.weight=torch.nn.Parameter(torch.tensor([.5],dtype=torch.float32))
        def forward(self,input_ids,labels,use_cache):
            return SimpleNamespace(loss=(self.weight-float(labels[0,-1])).square().sum())
    old,new=Tiny(),Tiny()
    rows=[{'id':i} for i in train.TRAIN_IDS]
    encoded=[dict(input_ids=[0,1],labels=[-100,i%3],response_tokens=1) for i in range(32)]
    _,old_metrics,_=original.train_steps(old,{'weight':old.weight},encoded,rows,100,train.SEED,1e-5,20,'cpu',lambda r:None)
    hundred=[]
    def capture(row):
        if row['step']==100:hundred.append(new.weight.detach().clone())
    _,new_metrics,_=train.train_steps(new,{'weight':new.weight},encoded,rows,512,train.SEED,1e-5,20,'cpu',capture,clear_cache=False)
    assert torch.equal(old.weight,hundred[0])
    assert [{k:r[k] for k in ('step','task','loss','gradient_norm','response_tokens')} for r in old_metrics]==[
        {k:r[k] for k in ('step','task','loss','gradient_norm','response_tokens')} for r in new_metrics[:100]]
