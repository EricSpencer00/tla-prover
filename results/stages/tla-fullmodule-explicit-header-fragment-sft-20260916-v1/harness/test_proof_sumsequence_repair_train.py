"""CPU mechanics/adversarial accounting tests, never evidence of 8B learning."""
from contextlib import nullcontext
from copy import deepcopy
import json
import random
from types import SimpleNamespace

import pytest
import torch

from tools import proof_sumsequence_repair_train as module

torch.set_num_threads(2)


class Tiny(torch.nn.Module):
    def __init__(self):
        super().__init__()
        for i in range(9):self.register_parameter('p'+str(i),torch.nn.Parameter(torch.randn(7)*.01))

    def forward(self,input_ids,labels=None,**kwargs):
        logits=sum(self.parameters())[None,None,:].expand(input_ids.shape[0],input_ids.shape[1],7)
        loss=None if labels is None else torch.nn.functional.cross_entropy(
            logits[:,:-1].reshape(-1,7),labels[:,1:].reshape(-1),ignore_index=-100)
        return SimpleNamespace(loss=loss,logits=logits)


@pytest.fixture
def tiny(monkeypatch):
    net=Tiny();selected=dict(net.named_parameters())
    monkeypatch.setattr(module,'EXPECTED_NAMES',tuple(selected))
    monkeypatch.setattr(module,'PARAMETERS',63)
    encoded=[dict(input_ids=[1,2,3]+([4] if i==7 else []),
        labels=[-100,2,3]+([4] if i==7 else []),response_tokens=3 if i==7 else 2) for i in range(40)]
    rows=[{'id':'train-'+str(i)} for i in range(40)]
    return net,selected,encoded,rows


def memory():return dict(allocated=100,reserved=120)


def test_schedule_exact_two_epochs():
    order=module.schedule()
    assert len(order)==80 and sorted(order[:40])==list(range(40)) and sorted(order[40:])==list(range(40))
    assert order==module.schedule()


@pytest.mark.parametrize('allocated,reserved',[(0,1),(2,1),(1,2**40),(True,3),(1,float('nan'))])
def test_memory_guard(allocated,reserved):
    with pytest.raises(ValueError):module.memory_guard(allocated,reserved)


def test_longest_backward_no_update(tiny):
    net,selected,encoded,_=tiny
    before={n:p.detach().clone() for n,p in selected.items()}
    result,logits=module.preflight(net,selected,encoded,device='cpu',context=nullcontext,measure=memory)
    assert result['index']==7 and result['optimizer_updates']==0 and result['parameters_unchanged']
    assert set(result['gradient_norms'])==set(selected) and torch.isfinite(logits).all()
    assert all(torch.equal(before[n],p) and p.grad is None for n,p in selected.items())


def test_missing_gradient_rejected(tiny):
    _,selected,_,_=tiny
    with pytest.raises(ValueError,match='finite gradient'):module.gradients(selected)


def run(tiny,**kwargs):
    net,selected,encoded,rows=tiny
    return module.train_steps(net,selected,encoded,rows,deadline=100,device='cpu',
        context=nullcontext,measure=memory,clock=lambda:0,release=lambda:None,emit=lambda r:None,**kwargs)


def test_actual80_fresh_adamw_updates(tiny):
    net,selected,encoded,rows=tiny
    before={n:p.detach().clone() for n,p in selected.items()}
    optimizer,metrics=run(tiny)
    config=dict(budget=module.BUDGET,schedule=module.schedule(),train_ids=[r['id'] for r in rows],encodings=encoded)
    module.validate_ledger(config,metrics)
    assert all(v['step'].item()==80 for v in optimizer.state.values())
    assert any(not torch.equal(before[n],p) for n,p in selected.items())


def test_deadline_never_silently_completes(tiny):
    net,selected,encoded,rows=tiny
    _,metrics=module.train_steps(net,selected,encoded,rows,deadline=0,device='cpu',
        context=nullcontext,measure=memory,clock=lambda:1,release=lambda:None,emit=lambda r:None)
    assert not metrics
    with pytest.raises(ValueError,match='Exactly80'):module.validate_ledger(
        dict(budget=module.BUDGET,schedule=module.schedule(),train_ids=[r['id'] for r in rows]),metrics)


@pytest.mark.parametrize('field,value',[('step',4),('index',99),('task','dev'),('loss',float('nan')),
    ('gradient_norms',{}),('input_ids_sha256','bad')])
def test_ledger_mutations_rejected(tiny,field,value):
    _,_,encoded,rows=tiny;_,metrics=run(tiny)
    metrics[0][field]=value
    with pytest.raises(ValueError):module.validate_ledger(
        dict(budget=module.BUDGET,schedule=module.schedule(),train_ids=[r['id'] for r in rows],encodings=encoded),metrics)


@pytest.fixture
def checkpoint(tiny,tmp_path,monkeypatch):
    net,selected,encoded,rows=tiny
    parent=tmp_path/'parent.pt';initial={n:p.detach().clone() for n,p in selected.items()}
    torch.save(dict(trainable_state=initial),parent)
    monkeypatch.setattr(module,'CHILD_SHA',module.helpers.file_sha(parent))
    output=tmp_path/'result';output.mkdir()
    (output/'train.json').write_bytes(b'fixture packet')
    monkeypatch.setattr(module,'packet_rows',lambda raw:rows)
    preflight,logits=module.preflight(net,selected,encoded,device='cpu',context=nullcontext,measure=memory)
    module.helpers.dump(output/'preflight.json',preflight);torch.save(logits,output/'preflight_logits.pt')
    optimizer,metrics=run(tiny)
    config=dict(budget=module.BUDGET,schedule=module.schedule(),train_ids=[r['id'] for r in rows],
        encodings=encoded,optimizer_parameter_names=list(selected),parent_restored_exactly=True,
        input_sha256=module.helpers.sha(b'fixture packet'))
    module.helpers.dump(output/'config.json',config)
    (output/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in metrics))
    rng=dict(torch_rng_state=torch.get_rng_state(),python_rng_state=random.getstate(),
        cuda_rng_state=[torch.tensor([1],dtype=torch.uint8)])
    state={n:p.detach().clone() for n,p in selected.items()}
    saved=dict(trainable_state=state,optimizer=optimizer.state_dict(),metrics=metrics,config=config,**rng)
    torch.save(saved,output/'policy_optimizer.pt')
    torch.save(dict(torch=rng['torch_rng_state'],python=rng['python_rng_state'],cuda=rng['cuda_rng_state']),output/'rng_before.pt')
    with torch.no_grad():value=net(torch.tensor([encoded[0]['input_ids']])).logits[:,-1].clone()
    torch.save(dict(input_ids=encoded[0]['input_ids'],before=value,after=value.clone()),output/'reload_logits.pt')
    delta=sum(float((state[n]-initial[n]).double().square().sum()) for n in state)**.5
    summary=dict(complete=True,identity_stable=True,actual_updates=80,parent_checkpoint_sha256=module.CHILD_SHA,
        requested_updates=80,coverage={r['id']:2 for r in rows},
        elapsed_seconds=2,fresh_optimizer=True,full_state_resume=False,memory=memory(),
        checkpoint_sha256=module.helpers.file_sha(output/'policy_optimizer.pt'),parameter_delta_l2=delta,
        reload_tensors_exact=True,reload_logits_exact=True,preflight_sha256=module.helpers.file_sha(output/'preflight.json'))
    for name in ('steps','reload_logits','preflight_logits','rng_before'):
        summary[name+'_sha256']=module.helpers.file_sha(output/(name+('.jsonl' if name=='steps' else '.pt')))
    module.helpers.dump(output/'summary.json',summary)
    return output,deepcopy(config),parent


def test_validate_actual_tensor_optimizer_delta(checkpoint):
    output,admission,parent=checkpoint
    assert module.validate_training(output,admission,parent)['complete']


@pytest.mark.parametrize('target',['optimizer_step','optimizer_shape','nan_weight','delta','preflight','rng','reload'])
def test_checkpoint_corruption_rejected(checkpoint,target):
    output,admission,parent=checkpoint
    summary=json.loads((output/'summary.json').read_text())
    if target in ('optimizer_step','optimizer_shape','nan_weight','rng'):
        path=output/'policy_optimizer.pt';saved=torch.load(path,weights_only=False)
        item=next(iter(saved['optimizer']['state'].values()))
        if target=='optimizer_step':item['step']=torch.tensor(79.)
        elif target=='optimizer_shape':item['exp_avg']=torch.zeros(2)
        elif target=='nan_weight':next(iter(saved['trainable_state'].values()))[0]=float('nan')
        else:saved['cuda_rng_state']=[]
        torch.save(saved,path);summary['checkpoint_sha256']=module.helpers.file_sha(path)
    elif target=='delta':summary['parameter_delta_l2']+=1
    elif target=='preflight':
        path=output/'preflight.json';value=json.loads(path.read_text());value['index']=0
        module.helpers.dump(path,value);summary['preflight_sha256']=module.helpers.file_sha(path)
    else:
        path=output/'reload_logits.pt';value=torch.load(path,weights_only=True);value['after']+=1
        torch.save(value,path);summary['reload_logits_sha256']=module.helpers.file_sha(path)
    module.helpers.dump(output/'summary.json',summary)
    with pytest.raises(ValueError):module.validate_training(output,admission,parent)


@pytest.mark.parametrize('failed',[False,True])
def test_supervisor_returns_only_validated_summary(tmp_path,monkeypatch,failed):
    a=SimpleNamespace(input=tmp_path/'input.json',checkpoint=tmp_path/'parent.pt',
        model_path=tmp_path/'model',admission=tmp_path/'admission.json',output=tmp_path/'run',
        expected_input_sha256='fixture')
    a.input.write_bytes(b'input');a.checkpoint.write_bytes(b'parent');a.model_path.mkdir()
    a.admission.write_text('{"frozen":true}')
    monkeypatch.setattr(module,'admit',lambda a:{'frozen':True})
    result={'complete':True,'checkpoint_sha256':'child'}
    def owned(command,cwd,seconds):
        assert seconds==900 and 'worker' in command
        module.helpers.dump(a.output/'summary.json',result)
        return dict(command=command,cwd=str(cwd),returncode=0,output='',seconds=1,
            execution_complete=not failed,cleanup_complete=not failed,output_complete=True,timed_out=False)
    monkeypatch.setattr(module,'run_owned',owned)
    monkeypatch.setattr(module,'validate_training',lambda *a:result)
    if failed:
        with pytest.raises(RuntimeError,match='incomplete'):module.supervise(a)
        assert not (a.output/'admitted.json').exists()
    else:
        assert module.supervise(a)==result
        assert json.loads((a.output/'admitted.json').read_text())['complete']
