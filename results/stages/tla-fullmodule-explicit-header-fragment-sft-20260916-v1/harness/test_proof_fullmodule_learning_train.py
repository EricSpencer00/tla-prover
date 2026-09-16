"""CPU mechanics/adversarial accounting tests, never evidence of 8B learning."""
from contextlib import nullcontext
from copy import deepcopy
import json
import random
from types import SimpleNamespace

import pytest
import torch

from tools import proof_fullmodule_learning_train as module

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
        labels=[-100,2,3]+([4] if i==7 else []),response_tokens=3 if i==7 else 2) for i in range(169)]
    rows=[{'id':'train-'+str(i)} for i in range(169)]
    return net,selected,encoded,rows


def memory(phase=None):return dict(allocated=100,reserved=120)


def test_schedule_exact_two_epochs():
    order=module.schedule()
    assert len(order)==338 and sorted(order[:169])==list(range(169)) and sorted(order[169:])==list(range(169))
    assert order==module.schedule()


@pytest.mark.parametrize('allocated,reserved',[(0,1),(2,1),(1,2**42),(True,3),(1,float('nan'))])
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


def test_preflight_gradient_metadata_persisted_before_guard(tiny):
    net,selected,encoded,_=tiny;records=[]
    def measure(phase):
        if phase=='preflight_backward':raise ValueError('memory limit fixture')
        return memory()
    with pytest.raises(ValueError,match='memory limit'):
        module.preflight(net,selected,encoded,device='cpu',context=nullcontext,measure=measure,persist=lambda r:records.append(dict(r)))
    assert records[0]['optimizer_updates']==0 and set(records[0]['gradient_norms'])==set(selected)
    assert records[0]['parameters_unchanged']


def test_raw_memory_saved_even_above_guard(tmp_path,monkeypatch):
    monkeypatch.setattr(torch.cuda,'max_memory_allocated',lambda:module.BUDGET['memory_limit'])
    monkeypatch.setattr(torch.cuda,'max_memory_reserved',lambda:module.BUDGET['memory_limit']+1)
    with pytest.raises(ValueError):module.gpu_memory(tmp_path,'actual_failure')
    row=json.loads((tmp_path/'memory.jsonl').read_text())
    assert row['phase']=='actual_failure' and row['reserved']==module.BUDGET['memory_limit']+1


def test_post_step_failure_records_actual_update(tiny):
    net,selected,encoded,rows=tiny;records=[]
    def measure(phase):
        if phase=='after_step_1':raise ValueError('memory limit fixture')
        return memory()
    with pytest.raises(RuntimeError,match='actual optimizer update 1'):
        module.train_steps(net,selected,encoded,rows,deadline=100,device='cpu',context=nullcontext,
            measure=measure,clock=lambda:0,release=lambda:None,emit=records.append)
    assert [r['phase'] for r in records]==['backward_complete','optimizer_step_started','optimizer_step_completed']
    assert records[-1]['step']==1 and records[-1]['optimizer_step_completed']


def test_worker_failure_retains_progress_and_partial_checkpoint(tmp_path,monkeypatch):
    module.helpers.dump(tmp_path/'progress.json',dict(actual_updates=7,optimizer_step_incomplete=True))
    def fail(a):raise ValueError('fixture failure')
    monkeypatch.setattr(module,'_worker',fail)
    with pytest.raises(ValueError):module.worker(SimpleNamespace(output=tmp_path))
    value=json.loads((tmp_path/'summary.json').read_text())
    assert not value['complete'] and value['actual_updates']==7 and value['optimizer_step_incomplete']
    assert not value['checkpoint_written']


def test_explicit_new_context_and_import_order():
    import inspect
    source=inspect.getsource(module)
    assert source.index("os.environ[_key]='4'")<source.index('from tools import proof_cuda_train')
    assert 'helpers.encode_row(' not in source and "row['response'],9216" in source
    assert module.BUDGET['max_tokens']==9216 and module.BUDGET['checkpoint_reserve']==180
    assert module.PATHS[:3]==('input','model_path','checkpoint') and len(module.PARENT_PATHS)==4


def test_isolated_actual_import_source_closure():
    import subprocess,sys
    code="""import sys
from pathlib import Path
from tools import proof_fullmodule_learning_train as m
used=set()
for obj in list(sys.modules.values()):
    path=getattr(obj,'__file__',None)
    if not path:continue
    try:name=Path(path).resolve().relative_to(m.ROOT).as_posix()
    except ValueError:continue
    if name.startswith(('tools/','harness/')) and '/.venv/' not in name and not name.endswith('__init__.py'):used.add(name)
assert used<=set(m.SOURCES), sorted(used-set(m.SOURCES))
"""
    subprocess.run([sys.executable,'-c',code],cwd=module.ROOT,check=True,timeout=30)


def test_actual169_trainonly_encodings_preserve42_and_masks():
    from transformers import AutoTokenizer
    p=module.packet
    rows,encoded,eligibility,eos=p.compose(p.OLD.read_text(),(p.AUDIT/'rows.json').read_text(),(p.CONTROLS/'rows.json').read_text())
    tokenizer=AutoTokenizer.from_pretrained(p.retained.repair.TOKENIZER,local_files_only=True)
    old=p.load(p.OLD)
    assert rows[:42]==old['rows'] and encoded[:42]==old['encodings']
    assert len(rows)==169 and len(eligibility)==128 and sum(r['included'] for r in eligibility)==127
    assert [r['id'] for r in eligibility if not r['included']]==[p.BLOCKED]
    for row,e in zip(rows,encoded):
        actual=module.helpers.encode_candidate(tokenizer,row['prompt'],row['response'],9216)
        assert e==dict(actual,id=row['id'],prompt_sha256=row['prompt_sha256'],response_sha256=row['response_sha256'])
        n=e['prompt_tokens'];assert e['labels']==[-100]*n+e['input_ids'][n:]
        assert e['input_ids'][-1]==eos and row['split']=='train'
        assert e['input_ids'][:n]==module.common.encode_prompt(tokenizer,row)['input_token_ids']
    assert max(len(e['input_ids']) for e in encoded)<=9216




def run(tiny,**kwargs):
    net,selected,encoded,rows=tiny
    return module.train_steps(net,selected,encoded,rows,deadline=100,device='cpu',
        context=nullcontext,measure=memory,clock=lambda:0,release=lambda:None,emit=lambda r:None,**kwargs)


def test_actual338_fresh_adamw_updates(tiny):
    net,selected,encoded,rows=tiny
    before={n:p.detach().clone() for n,p in selected.items()}
    optimizer,metrics=run(tiny)
    config=dict(budget=module.BUDGET,schedule=module.schedule(),train_ids=[r['id'] for r in rows],encodings=encoded)
    module.validate_ledger(config,metrics)
    assert all(v['step'].item()==338 for v in optimizer.state.values())
    assert any(not torch.equal(before[n],p) for n,p in selected.items())


def test_deadline_never_silently_completes(tiny):
    net,selected,encoded,rows=tiny
    _,metrics=module.train_steps(net,selected,encoded,rows,deadline=0,device='cpu',
        context=nullcontext,measure=memory,clock=lambda:1,release=lambda:None,emit=lambda r:None)
    assert not metrics
    with pytest.raises(ValueError,match='Exactly338'):module.validate_ledger(
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
    monkeypatch.setattr(module,'SOURCES',())
    (output/'train.json').write_bytes(b'fixture packet')
    monkeypatch.setattr(module,'packet_rows',lambda raw:rows)
    preflight,logits=module.preflight(net,selected,encoded,device='cpu',context=nullcontext,measure=memory)
    module.helpers.dump(output/'preflight.json',preflight);torch.save(torch.nn.functional.pad(logits,(0,128256-logits.numel())),output/'preflight_logits.pt')
    optimizer,metrics=run(tiny)
    config=dict(budget=module.BUDGET,schedule=module.schedule(),train_ids=[r['id'] for r in rows],
        encodings=encoded,optimizer_parameter_names=list(selected),parent_restored_exactly=True,
        input_sha256=module.helpers.sha(b'fixture packet'),seed=module.BUDGET['seed'],algorithm=module.ALGORITHM,implementation_sha256={})
    module.helpers.dump(output/'config.json',config)
    (output/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in metrics))
    rng=dict(torch_rng_state=torch.get_rng_state(),python_rng_state=random.getstate(),
        cuda_rng_state=[torch.tensor([1],dtype=torch.uint8)])
    state={n:p.detach().clone() for n,p in selected.items()}
    saved=dict(trainable_state=state,optimizer=optimizer.state_dict(),metrics=metrics,config=config,**rng)
    torch.save(saved,output/'policy_optimizer.pt')
    torch.save(dict(torch=rng['torch_rng_state'],python=rng['python_rng_state'],cuda=rng['cuda_rng_state']),output/'rng_before.pt')
    with torch.no_grad():value=net(torch.tensor([encoded[0]['input_ids']])).logits[:,-1].clone()
    value=torch.nn.functional.pad(value,(0,128256-value.shape[-1]))
    torch.save(dict(input_ids=encoded[0]['input_ids'],before=value,after=value.clone()),output/'reload_logits.pt')
    phases=['after_model_load','after_parent_restore','preflight_forward','preflight_backward']
    phases += [prefix+str(i) for i in range(1,339) for prefix in ('before_step_','after_step_')]
    phases += ['before_checkpoint_save','after_checkpoint_reload','after_final_admission']
    (output/'memory.jsonl').write_text(''.join(json.dumps(dict(phase=p,**memory()))+'\n' for p in phases))
    delta=sum(float((state[n]-initial[n]).double().square().sum()) for n in state)**.5
    summary=dict(complete=True,identity_stable=True,actual_updates=338,parent_checkpoint_sha256=module.CHILD_SHA,
        requested_updates=338,coverage={r['id']:2 for r in rows},
        elapsed_seconds=2,fresh_optimizer=True,full_state_resume=False,memory=memory(),
        proof_success_claim=False,learning_improvement_claim=False,optimizer_reload_exact=True,
        checkpoint_sha256=module.helpers.file_sha(output/'policy_optimizer.pt'),parameter_delta_l2=delta,
        reload_tensors_exact=True,reload_logits_exact=True,preflight_sha256=module.helpers.file_sha(output/'preflight.json'))
    for name in ('steps','reload_logits','preflight_logits','rng_before','memory'):
        summary[name+'_sha256']=module.helpers.file_sha(output/(name+('.jsonl' if name in ('steps','memory') else '.pt')))
    module.helpers.dump(output/'summary.json',summary)
    return output,deepcopy(config),parent


def test_validate_actual_tensor_optimizer_delta(checkpoint):
    output,admission,parent=checkpoint
    assert module.validate_training(output,admission,parent)['complete']


def test_actual_optimizer_serialization_all_values(tiny,tmp_path):
    optimizer,_=run(tiny);path=tmp_path/'checkpoint.pt'
    torch.save(dict(optimizer=optimizer.state_dict()),path)
    assert module.optimizer_reload_exact(optimizer,path)
    raw=torch.load(path,weights_only=False)
    next(iter(raw['optimizer']['state'].values()))['exp_avg'][0]+=1
    torch.save(raw,path)
    with pytest.raises(ValueError,match='serialization tensor'):module.optimizer_reload_exact(optimizer,path)


@pytest.mark.parametrize('target',['optimizer_step','optimizer_shape','optimizer_mapping','optimizer_flags',
    'nan_weight','delta','preflight','rng','reload','memory','claim','coverage'])
def test_checkpoint_corruption_rejected(checkpoint,target):
    output,admission,parent=checkpoint
    summary=json.loads((output/'summary.json').read_text())
    if target in ('optimizer_step','optimizer_shape','optimizer_mapping','optimizer_flags','nan_weight','rng'):
        path=output/'policy_optimizer.pt';saved=torch.load(path,weights_only=False)
        item=next(iter(saved['optimizer']['state'].values()))
        if target=='optimizer_step':item['step']=torch.tensor(79.)
        elif target=='optimizer_shape':item['exp_avg']=torch.zeros(2)
        elif target=='optimizer_mapping':saved['optimizer']['param_groups'][0]['params'][1]=saved['optimizer']['param_groups'][0]['params'][0]
        elif target=='optimizer_flags':saved['optimizer']['param_groups'][0]['maximize']=True
        elif target=='nan_weight':next(iter(saved['trainable_state'].values()))[0]=float('nan')
        else:saved['cuda_rng_state']=[]
        torch.save(saved,path);summary['checkpoint_sha256']=module.helpers.file_sha(path)
    elif target=='delta':summary['parameter_delta_l2']+=1
    elif target=='preflight':
        path=output/'preflight.json';value=json.loads(path.read_text());value['index']=0
        module.helpers.dump(path,value);summary['preflight_sha256']=module.helpers.file_sha(path)
    elif target=='memory':
        path=output/'memory.jsonl';path.write_text('');summary['memory_sha256']=module.helpers.file_sha(path)
    elif target=='claim':summary['proof_success_claim']=True
    elif target=='coverage':summary['coverage'].pop(next(iter(summary['coverage'])))
    else:
        path=output/'reload_logits.pt';value=torch.load(path,weights_only=True);value['after']+=1
        torch.save(value,path);summary['reload_logits_sha256']=module.helpers.file_sha(path)
    module.helpers.dump(output/'summary.json',summary)
    with pytest.raises(ValueError):module.validate_training(output,admission,parent)


def test_exact_parent84_provenance_paths(tmp_path,monkeypatch):
    a=SimpleNamespace(model_path=tmp_path/'model',checkpoint=tmp_path/'8866',
        parent_training_input=tmp_path/'original42.json',parent_training_output=tmp_path/'old84',
        parent_training_admission=tmp_path/'admission.json',parent_parent_checkpoint=tmp_path/'1bb6')
    a.parent_training_admission.write_text('{}')
    calls=[]
    def receipt(args,prospective):
        calls.append((args,prospective));return dict(optimizer_updates=84,child_sha256=module.CHILD_SHA,parent_sha256=module.ancestry.PARENT_SHA)
    monkeypatch.setattr(module.ancestry,'training_receipt',receipt)
    assert module.parent_receipt(a)['optimizer_updates']==84
    args,_=calls[0]
    assert args.training_input==a.parent_training_input and args.training_output==a.parent_training_output
    assert args.parent_checkpoint==a.parent_parent_checkpoint and args.checkpoint==a.checkpoint
    assert args.expected_input_sha256=='d370761500e0f828f536d74fffd7d9785df34215ffa61c09490bccbcfe6544d7'
    monkeypatch.setattr(module.ancestry,'training_receipt',lambda *args:dict(optimizer_updates=1,child_sha256=module.CHILD_SHA,parent_sha256=module.ancestry.PARENT_SHA))
    with pytest.raises(ValueError,match='actual84'):module.parent_receipt(a)


@pytest.mark.parametrize('failed',[False,True])
def test_supervisor_returns_only_validated_summary(tmp_path,monkeypatch,failed):
    a=SimpleNamespace(input=tmp_path/'input.json',checkpoint=tmp_path/'parent.pt',
        model_path=tmp_path/'model',admission=tmp_path/'admission.json',output=tmp_path/'run',
        expected_input_sha256='fixture')
    a.input.write_bytes(b'input');a.checkpoint.write_bytes(b'parent');a.model_path.mkdir()
    for name in module.PARENT_PATHS:
        path=tmp_path/name;path.write_bytes(b'ancestry fixture');setattr(a,name,path)
    a.admission.write_text('{"frozen":true}')
    monkeypatch.setattr(module,'admit',lambda a:{'frozen':True})
    result={'complete':True,'checkpoint_sha256':'child'}
    def owned(command,cwd,seconds):
        assert seconds==1800 and 'worker' in command
        module.helpers.dump(a.output/'summary.json',result)
        return dict(command=command,cwd=str(cwd),returncode=0,output='',seconds=1,
            execution_complete=not failed,cleanup_complete=not failed,output_complete=True,timed_out=False,
            output_limit=False,root_reaped=True,errors=[],surviving_owned_processes=[])
    monkeypatch.setattr(module,'run_owned',owned)
    monkeypatch.setattr(module,'validate_training',lambda *a:result)
    if failed:
        with pytest.raises(RuntimeError,match='incomplete'):module.supervise(a)
        assert not (a.output/'admitted.json').exists()
    else:
        assert module.supervise(a)==result
        assert json.loads((a.output/'admitted.json').read_text())['complete']


@pytest.mark.parametrize('key,value',[('command',['wrong']),('cwd','/wrong'),('execution_complete',False),
    ('cleanup_complete',False),('output_complete',False),('root_reaped',False),('timed_out',True),
    ('output_limit',True),('surviving_owned_processes',[{'pid':1}]),('errors',['lost ancestry']),
    ('returncode',True),('seconds',float('nan')),('seconds',1801)])
def test_exact_owned_process_failclosed(key,value):
    command=['python','worker'];process=dict(command=command,cwd=str(module.ROOT),returncode=0,output='',seconds=1,
        execution_complete=True,cleanup_complete=True,output_complete=True,root_reaped=True,
        timed_out=False,output_limit=False,surviving_owned_processes=[],errors=[])
    module.process_ok(process,command)
    process[key]=value
    with pytest.raises(RuntimeError):module.process_ok(process,command)
