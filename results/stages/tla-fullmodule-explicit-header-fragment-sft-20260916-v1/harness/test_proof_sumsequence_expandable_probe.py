"""Tiny CPU numerical/causal-gradient tests, not actual8B feasibility evidence."""
from contextlib import nullcontext
from copy import deepcopy
import json
import os
import subprocess
import sys
from types import SimpleNamespace

import pytest
import torch

from tools import proof_sumsequence_expandable_probe as module


@pytest.fixture
def original():
    path=module.ROOT/'results/runs/proof-sumsequence-stochastic-cycle-20260906-v1/child/rollouts.jsonl'
    raw=path.read_bytes()
    assert module.sha(raw)==module.PINS['rollouts']
    return [json.loads(s) for s in raw.splitlines()]


def test_exact_full32_longest_in_group(original):
    rows=module.select_rows(original)
    assert [len(r['token_ids']) for r in rows]==[777,712,268,319]
    assert rows==original[4:8]


@pytest.mark.parametrize('mutation',['drop','reorder','length','finish','longest'])
def test_selection_cannot_shorten_or_drop(original,mutation):
    rows=deepcopy(original)
    if mutation=='drop':rows.pop()
    elif mutation=='reorder':rows[4],rows[5]=rows[5],rows[4]
    elif mutation=='length':rows[4]['token_ids'].pop()
    elif mutation=='finish':rows[4]['finish_reason']='time_limit'
    else:
        row=next(r for r in rows if r['task_id']!=module.TASK and r.get('finish_reason')=='eos')
        row['input_token_ids']=[1]*8192
    with pytest.raises(ValueError):module.select_rows(rows)


class Tiny(torch.nn.Module):
    def __init__(self):
        super().__init__();self.weight=torch.nn.Parameter(torch.tensor([.1,.2,.3]))
    def forward(self,input_ids,past_key_values=None,**kwargs):
        prior=0 if past_key_values is None else past_key_values
        hidden=input_ids.float().unsqueeze(-1)*self.weight+prior
        return SimpleNamespace(logits=hidden,past_key_values=hidden[:,-1:,:]*.2)


@pytest.fixture
def tiny(monkeypatch):
    monkeypatch.setattr(module,'EOS_IDS',[2])
    net=Tiny();row=dict(sample_id='tiny',input_token_ids=[1,1],token_ids=[1,1,2])
    with torch.no_grad():
        actual=module.cached_token_logps(net,torch.tensor(row['input_token_ids']),torch.tensor(row['token_ids']),
            eos_token_ids=[2],seconds=2)
    row['selected_token_logprobs']=actual.tolist()
    return net,row


def allocator():
    return dict(memory=dict(allocated=100,reserved=120),backend='native',
        settings=dict(expandable_segments=True,PYTORCH_CUDA_ALLOC_CONF=module.ALLOCATOR_CONF),
        segments=[dict(is_expandable=True,total_size=120)],memory_stats={})


def test_cached_grad_exact_logps_and_no_update(tiny):
    net,row=tiny;before=net.weight.detach().clone();events=[]
    result=module.probe_one(net,dict(net.named_parameters()),row,seconds=2,device='cpu',
        context=nullcontext,capture=allocator,emit=lambda r:events.append(deepcopy(r)))
    assert result['status']=='complete' and result['parity']['max_abs']==0
    assert result['gradients']['weight']['norm']>0 and net.weight.grad is None
    assert torch.equal(before,net.weight) and result['actual_token_logprobs']==row['selected_token_logprobs']
    assert events[0]['status']=='scoring' and events[-1]['status']=='complete'


def test_discrepancy_preserved_before_abort(tiny):
    net,row=tiny;row['selected_token_logprobs'][0]-=.1;events=[]
    with pytest.raises(module.scoring.LogprobDiscrepancyError):
        module.probe_one(net,dict(net.named_parameters()),row,seconds=2,device='cpu',capture=allocator,
            emit=lambda r:events.append(deepcopy(r)))
    last=events[-1]
    assert last['status']=='failed' and last['actual_token_logprobs']
    assert last['failure']['logprob_discrepancy']['max_abs']>.03
    assert net.weight.grad is None


def test_missing_gradient_refused(tiny):
    net,row=tiny;extra=torch.nn.Parameter(torch.ones(2))
    with pytest.raises(ValueError,match='finite gradient'):
        module.probe_one(net,dict(weight=net.weight,unused=extra),row,seconds=2,device='cpu',capture=allocator)


def test_no_synthetic_eos_or_shortening(tiny):
    net,row=tiny;row['token_ids']=row['token_ids'][:-1]
    with pytest.raises(ValueError,match='terminal EOS'):
        module.probe_one(net,dict(net.named_parameters()),row,seconds=2,device='cpu',capture=allocator)


def test_memory_failure_preserves_failed_row(tiny):
    net,row=tiny;events=[]
    def fail():
        value=allocator();value['memory']['reserved']=2**40
        return value
    with pytest.raises(ValueError,match='36GiB'):
        module.probe_one(net,dict(net.named_parameters()),row,seconds=2,device='cpu',capture=fail,
            emit=lambda r:events.append(deepcopy(r)))
    assert events[-1]['status']=='failed' and '36GiB' in events[-1]['failure']['reason']


def test_run_preserves_four_keys_on_admission_failure(tmp_path,monkeypatch):
    values={name:tmp_path/name for name in module.PATHS}
    for path in values.values():path.write_bytes(b'fixture')
    args=SimpleNamespace(**values,output=tmp_path/'output',admission=tmp_path/'admission.json')
    args.admission.write_text('{}')
    def fail(a):raise ValueError('bad original admission')
    monkeypatch.setattr(module,'admit',fail)
    with pytest.raises(ValueError,match='original admission'):module.run(args)
    summary=json.loads((args.output/'summary.json').read_bytes())
    assert summary['accounted_samples']==4 and summary['completed_samples']==0 and not summary['complete']
    assert summary['checkpoint_writes']==0 and summary['optimizer_updates']==0


@pytest.fixture
def completed(tiny,monkeypatch):
    net,row=tiny
    result=module.probe_one(net,dict(net.named_parameters()),row,seconds=2,device='cpu',capture=allocator)
    monkeypatch.setattr(module,'GRADIENT_ELEMENTS',{'weight':3})
    originals=[];results=[]
    for i in range(4):
        r=deepcopy(row);r['sample_id']='sample'+str(i);originals.append(r)
        value=deepcopy(result);value['sample_id']=r['sample_id'];results.append(value)
    return originals,results


def test_raw_result_reaudit(completed):
    module.validate_results(*completed)


@pytest.mark.parametrize('mutation',['parity','logps','dtype','elements','norm','update','memory'])
def test_raw_result_reaudit_rejects_mutations(completed,mutation):
    original,results=completed;r=results[0]
    if mutation=='parity':r['parity']['max_abs']=.001
    elif mutation=='logps':r['actual_token_logprobs'][0]-=.2
    elif mutation=='dtype':r['gradients']['weight']['dtype']='torch.bfloat16'
    elif mutation=='elements':r['gradients']['weight']['elements']=2
    elif mutation=='norm':r['gradients']['weight']['norm']=float('nan')
    elif mutation=='update':r['optimizer_updates']=1
    else:r['memory_after_backward']['reserved']=2**40
    with pytest.raises(ValueError):module.validate_results(original,results)


def test_corrupt_partial_ledger_does_not_mask_original_error(tmp_path,monkeypatch):
    values={name:tmp_path/name for name in module.PATHS}
    for path in values.values():path.write_bytes(b'fixture')
    a=SimpleNamespace(**values,output=tmp_path/'output',admission=tmp_path/'admission.json')
    a.admission.write_text('{}')
    def fail(a):
        (a.output/'rows.json').write_text('{broken')
        raise ValueError('original cause')
    monkeypatch.setattr(module,'admit',fail)
    with pytest.raises(ValueError,match='original cause'):module.run(a)
    failure=json.loads((a.output/'failure.json').read_text())
    assert failure['reason']=='original cause' and 'ledger_error' in failure
    summary=json.loads((a.output/'summary.json').read_text())
    assert summary['accounted_samples']==0 and summary['requested_samples']==4


def test_atomic_snapshot(tmp_path):
    module.snapshot_rows(tmp_path,[{'id':1}])
    assert json.loads((tmp_path/'rows.json').read_text())==[{'id':1}]
    assert not (tmp_path/'rows.pending').exists()


def test_cross_device_mean_tolerance_does_not_weaken_threshold(completed):
    original,results=completed
    # Tiny reduction-order discrepancy only; both means remain under .003.
    results[0]['parity_gpu']['mean_abs']=1e-9
    module.validate_results(original,results)
    results[0]['parity_gpu']['mean_abs']=.003000001
    with pytest.raises(ValueError,match='GPU parity'):module.validate_results(original,results)


@pytest.mark.parametrize('field',['max_limit','tokens','worst_token_index','sampled_at_worst'])
def test_gpu_parity_metadata_cannot_drift(completed,field):
    original,results=completed;results[0]['parity_gpu'][field]+=1
    with pytest.raises(ValueError,match='GPU parity'):module.validate_results(original,results)


def test_configuration_precedes_torch_import_in_fresh_process():
    result=subprocess.run([sys.executable,'-c',
        'import tools.proof_sumsequence_expandable_probe as p; import os; print(p.TORCH_PREIMPORTED); print(os.environ["PYTORCH_ALLOC_CONF"])'],
        cwd=module.ROOT,capture_output=True,text=True,check=True)
    assert result.stdout.splitlines()==['False',module.ALLOCATOR_CONF]


@pytest.mark.parametrize('name,value',[
    ('PYTORCH_ALLOC_CONF','backend:cudaMallocAsync'),
    ('PYTORCH_ALLOC_CONF','backend:native,expandable_segments:False'),
    ('PYTORCH_CUDA_ALLOC_CONF','expandable_segments:True'),
    ('PYTORCH_NO_CUDA_MEMORY_CACHING','1')])
def test_conflicting_allocator_configuration_rejected(monkeypatch,name,value):
    monkeypatch.setenv(name,value)
    with pytest.raises(ValueError):module.configure_allocator()


@pytest.mark.parametrize('mutation',['backend','settings','segment','missing','over_limit'])
def test_actual_allocator_not_environment_only(mutation):
    value=allocator()
    if mutation=='backend':value['backend']='cudaMallocAsync'
    elif mutation=='settings':value['settings']['expandable_segments']=False
    elif mutation=='segment':value['segments'][0]['is_expandable']=False
    elif mutation=='missing':value['settings']=None
    else:value['memory']['reserved']=36*1024**3+1
    with pytest.raises(ValueError):module.guard_allocator(value)


def test_backward_guard_preserves_gradients_and_runtime_snapshot(tiny):
    net,row=tiny;events=[];calls=[0]
    def capture():
        calls[0]+=1;value=allocator()
        if calls[0]>=2:value['memory']['reserved']=38795214848
        value['memory_stats']={'reserved_bytes.all.peak':value['memory']['reserved']}
        return value
    with pytest.raises(ValueError,match='36GiB'):
        module.probe_one(net,dict(net.named_parameters()),row,seconds=2,device='cpu',capture=capture,
            emit=lambda r:events.append(deepcopy(r)))
    last=events[-1]
    assert last['gradients']['weight']['norm']>0
    assert last['allocator_after_backward']['memory']['reserved']==38795214848
    assert last['allocator_at_failure']['memory_stats']['reserved_bytes.all.peak']==38795214848
    assert last['status']=='failed' and net.weight.grad is None


def test_runtime_capture_is_compact_and_pre_guard():
    snapshot=dict(allocator_settings=dict(expandable_segments=True,PYTORCH_CUDA_ALLOC_CONF=module.ALLOCATOR_CONF),
        segments=[dict(is_expandable=True,total_size=120,blocks=[{'huge':'omitted'}],frames=['omitted'])])
    cuda=SimpleNamespace(max_memory_allocated=lambda:100,max_memory_reserved=lambda:120,
        memory=SimpleNamespace(get_allocator_backend=lambda:'native',_snapshot=lambda:snapshot),
        memory_stats=lambda:{'reserved_bytes.all.peak':120,'unrelated':99})
    value=module.allocator_evidence(SimpleNamespace(cuda=cuda))
    assert value['segments']==[dict(total_size=120,is_expandable=True)]
    assert value['memory_stats']=={'reserved_bytes.all.peak':120}
    assert module.guard_allocator(value)==dict(allocated=100,reserved=120)
