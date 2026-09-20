"""CPU integration only; production requires real CUDA transfer evidence."""
from copy import deepcopy
from types import SimpleNamespace

import pytest
import torch

from tools import proof_sumsequence_logprob_offload_probe as probe
from tools.proof_logprob_offload import LogprobOffload


class Tiny(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.weight=torch.nn.Parameter(torch.tensor([.1,.2,.3]))

    def forward(self,input_ids,past_key_values=None,**kwargs):
        prior=0 if past_key_values is None else past_key_values
        hidden=input_ids.float().unsqueeze(-1)*self.weight+prior
        return SimpleNamespace(logits=hidden,past_key_values=hidden[:,-1:,:]*.2)


def allocator():
    return dict(memory=dict(allocated=100,reserved=120),backend='native',
        settings=dict(expandable_segments=True,PYTORCH_CUDA_ALLOC_CONF=probe.ALLOCATOR_CONF),
        segments=[dict(is_expandable=True,total_size=120)],memory_stats={})


def cpu_factory(vocab_size,response_tokens):
    return LogprobOffload(vocab_size,response_tokens,allow_cpu=True)


@pytest.fixture
def case(monkeypatch):
    monkeypatch.setattr(probe,'VOCAB_SIZE',3)
    monkeypatch.setattr(probe,'EOS_IDS',[2])
    model=Tiny()
    row=dict(sample_id='tiny',input_token_ids=[1,1],token_ids=[1,1,2])
    values=probe.cached_token_logps(model,torch.tensor(row['input_token_ids']),
        torch.tensor(row['token_ids']),eos_token_ids=[2],seconds=2)
    row['selected_token_logprobs']=values.detach().tolist()
    expected=torch.autograd.grad(values.sum(),model.weight)[0].norm().item()
    return model,row,expected


def test_offload_probe_preserves_score_gradient_and_weights(case):
    model,row,expected=case
    before=model.weight.detach().clone()
    result=probe.probe_one(model,dict(model.named_parameters()),row,seconds=2,
        device='cpu',capture=allocator,offload_factory=cpu_factory)
    assert result['status']=='complete'
    assert result['parity']['max_abs']==result['parity']['mean_abs']==0
    assert result['gradients']['weight']['norm']==expected
    assert 'offload_after_forward' in result and 'offload_after_backward' in result
    assert torch.equal(before,model.weight) and model.weight.grad is None


def test_guard_failure_keeps_offload_and_gradient_evidence(case):
    model,row,_=case
    events=[];calls=[0]
    def capture():
        calls[0]+=1
        value=allocator()
        if calls[0]>=2:value['memory']['reserved']=36*1024**3+1
        return value
    with pytest.raises(ValueError,match='36GiB'):
        probe.probe_one(model,dict(model.named_parameters()),row,seconds=2,
            device='cpu',capture=capture,offload_factory=cpu_factory,
            emit=lambda r:events.append(deepcopy(r)))
    failure=events[-1]
    assert failure['status']=='failed'
    assert failure['gradients']['weight']['norm']>0
    assert 'offload_after_backward' in failure and 'offload_at_failure' in failure


def test_default_production_context_rejects_cpu(case):
    model,row,_=case
    with pytest.raises(ValueError):
        probe.probe_one(model,dict(model.named_parameters()),row,seconds=2,
            device='cpu',capture=allocator)


def test_frozen_budget_does_not_relax_original_probe():
    assert probe.BUDGET['memory_limit']==36*1024**3
    assert probe.BUDGET['seconds']==900
    assert probe.BUDGET['max_logprob_error']==.03
    assert probe.BUDGET['mean_logprob_error']==.003
    assert probe.BUDGET['optimizer_updates']==probe.BUDGET['checkpoint_writes']==0
    assert probe.BUDGET['saved_logprob_offload']['host_limit_bytes']==1024**3
    assert 'tools/proof_logprob_offload.py' in probe.SOURCES
