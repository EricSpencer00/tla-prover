from types import SimpleNamespace

import pytest
import torch

from tools.proof_token_rl_sampling import sample_tokens,same_rng_device
from tools.proof_token_rl_objective import sequence_logprob


class Causal(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.table=torch.nn.Parameter(torch.tensor([[0.,1.,2.,.5],[2.,-.5,1.,.5],[.5,1.,0.,2.],[0.,0.,0.,0.]]))
        self.child=torch.nn.Dropout(.5)
        self.calls=[]

    def forward(self,input_ids,attention_mask,past_key_values=None,use_cache=True):
        old=0 if past_key_values is None else past_key_values
        assert attention_mask.shape==(1,old+input_ids.shape[1])
        assert bool((attention_mask==1).all())
        self.calls.append(dict(length=input_ids.shape[1],cache=old,mask=attention_mask.shape[1],
                               grad=torch.is_grad_enabled(),training=self.training))
        return SimpleNamespace(logits=self.table[input_ids],past_key_values=old+input_ids.shape[1])


def sample(model,seed=123,**kwargs):
    args=dict(generator=torch.Generator().manual_seed(seed),eos_token_ids=[3],max_new_tokens=20,seconds=10)
    args.update(kwargs)
    return sample_tokens(model,torch.tensor([0,1]),**args)


def test_selected_logps_match_teacher_forced_actual_tokens():
    model=Causal();result=sample(model)
    assert result['finish_reason']=='eos'
    ids=torch.tensor([0,1]+result['token_ids'])
    logits=model.table[ids]
    teacher=sequence_logprob(logits,ids,result['token_ids'],prompt_length=2,eos_token_ids=[3])
    assert teacher.item()==pytest.approx(result['sequence_logprob'],abs=2e-6)
    assert len(result['selected_token_logprobs'])==len(result['token_ids'])
    assert model.calls[0]['length']==2
    assert all(c['length']==1 for c in model.calls[1:])
    assert all(not c['grad'] and not c['training'] for c in model.calls)


def test_exact_seed_replication_and_mode_weight_preservation():
    model=Causal();model.train();model.child.eval();original=model.table.detach().clone()
    one=sample(model);two=sample(model)
    for key in ('token_ids','selected_token_logprobs','sequence_logprob','finish_reason'):
        assert one[key]==two[key]
    assert model.training and not model.child.training
    assert torch.equal(model.table,original) and model.table.grad is None


def test_eos_only_never_appended():
    model=Causal()
    with torch.no_grad():model.table[:]=torch.tensor([-100.,-100.,-100.,100.])
    result=sample(model)
    assert result['token_ids']==[3] and result['finish_reason']=='eos' and result['forward_calls']==1


def test_token_limit_does_not_force_eos():
    model=Causal()
    with torch.no_grad():model.table[:]=torch.tensor([100.,-100.,-100.,-100.])
    result=sample(model,max_new_tokens=3)
    assert result['token_ids']==[0,0,0] and result['finish_reason']=='token_limit'
    assert not result['eos_reached']


@pytest.mark.parametrize('ticks,expected_calls', [([0,2,2],0),([0,0,2,2],1)])
def test_deadline_before_and_after_forward(ticks,expected_calls):
    clock=iter(ticks);model=Causal()
    result=sample(model,seconds=1,clock=lambda:next(clock))
    assert result['token_ids']==[] and result['finish_reason']=='time_limit'
    assert result['forward_calls']==expected_calls


def test_full_vocabulary_normalization_matches_multinomial_without_filtering():
    model=Causal();seed=81
    expected=torch.multinomial(model.table[1].detach().float().log_softmax(-1).exp(),1,
                               replacement=True,generator=torch.Generator().manual_seed(seed)).item()
    result=sample(model,seed,max_new_tokens=1)
    assert result['token_ids']==[expected]
    assert result['selected_token_logprobs'][0]==model.table[1].detach().log_softmax(-1)[expected].item()
    probability=model.table[1].detach().softmax(-1)
    assert result['token_entropies'][0]==pytest.approx(-(probability*probability.log()).sum().item())


@pytest.mark.parametrize('kwargs',[{'max_context':2},{'max_new_tokens':3073},{'max_new_tokens':0},
    {'seconds':0},{'seconds':float('nan')},{'eos_token_ids':[]},{'eos_token_ids':[3,3]}])
def test_invalid_budget_or_eos(kwargs):
    with pytest.raises(ValueError):sample(Causal(),**kwargs)


def test_no_cache_fails_and_restores_mode():
    class NoCache(Causal):
        def forward(self,**kwargs):
            answer=super().forward(**kwargs);answer.past_key_values=None;return answer
    model=NoCache();model.train()
    with torch.no_grad():model.table[:]=torch.tensor([100.,-100.,-100.,-100.])
    with pytest.raises(ValueError,match='cache'):sample(model)
    assert model.training


def test_context_factory_invoked_every_forward():
    from contextlib import contextmanager
    calls=[]
    @contextmanager
    def context():
        calls.append('enter');yield;calls.append('exit')
    result=sample(Causal(),context_factory=context)
    assert calls==['enter','exit']*result['forward_calls']


def test_nonmaximal_vocabulary_tokens_remain_sampleable():
    model=Causal()
    seen={sample(model,seed,max_new_tokens=1)['token_ids'][0] for seed in range(128)}
    assert seen=={0,1,2,3}


def test_nonfinite_logits_fail_closed_and_restore_mode():
    model=Causal();model.train()
    with torch.no_grad():model.table[1,0]=float('nan')
    with pytest.raises(ValueError,match='Finite'):sample(model)
    assert model.training


def test_deadline_after_sample_preserves_eos_but_not_completion():
    model=Causal()
    with torch.no_grad():model.table[:]=torch.tensor([-100.,-100.,-100.,100.])
    ticks=iter([0,0,.5,2,2])
    result=sample(model,seconds=1,clock=lambda:next(ticks))
    assert result['token_ids']==[3] and len(result['selected_token_logprobs'])==1
    assert result['eos_reached'] is True
    assert result['finish_reason']=='time_limit' and result['deadline_exceeded'] is True


def test_deadline_after_final_sample_overrides_token_limit():
    model=Causal()
    with torch.no_grad():model.table[:]=torch.tensor([100.,-100.,-100.,-100.])
    ticks=iter([0,0,.5,2,2])
    result=sample(model,max_new_tokens=1,seconds=1,clock=lambda:next(ticks))
    assert result['token_ids']==[0] and result['hit_token_limit'] is True
    assert result['finish_reason']=='time_limit' and result['deadline_exceeded'] is True


@pytest.mark.parametrize('left,right,current,expected',[
    ('cuda','cuda:0',0,True),('cuda:0','cuda',0,True),
    ('cuda','cuda:1',1,True),('cuda:1','cuda',1,True),
    ('cuda','cuda:0',1,False),('cuda:0','cuda',1,False),
    ('cuda:0','cuda:1',0,False),('cuda:1','cuda:0',1,False),
    ('cuda:1','cuda:1',0,True),('cuda','cuda',1,True),
    ('cpu','cuda:0',0,False),('cuda','cpu',0,False),('cpu','cpu',1,True),
])
def test_cuda_rng_device_alias_resolution_without_hardware(left,right,current,expected):
    assert same_rng_device(torch.device(left),torch.device(right),current_cuda_index=current) is expected


def test_current_cuda_device_is_read_only_when_ordinal_implicit(monkeypatch):
    calls=[]
    def current():calls.append(True);return 1
    monkeypatch.setattr(torch.cuda,'current_device',current)
    assert same_rng_device(torch.device('cuda'),torch.device('cuda:1'))
    assert calls==[True]
    calls.clear()
    assert not same_rng_device(torch.device('cuda:0'),torch.device('cuda:1'))
    assert not same_rng_device(torch.device('cpu'),torch.device('cuda'))
    assert calls==[]
def test_actual_tiny_llama_cache_and_teacher_forced_gradient_agree():
    import torch
    from transformers import LlamaConfig,LlamaForCausalLM
    from tools.proof_token_rl_sampling import sample_tokens
    from tools.proof_token_rl_objective import sequence_logprob
    torch.manual_seed(7)
    model=LlamaForCausalLM(LlamaConfig(vocab_size=8,hidden_size=16,intermediate_size=32,
        num_hidden_layers=2,num_attention_heads=2,num_key_value_heads=2,max_position_embeddings=128))
    model.eval();prompt=torch.tensor([1,2,3])
    result=sample_tokens(model,prompt,generator=torch.Generator().manual_seed(91),
        eos_token_ids=[7],max_new_tokens=64,seconds=20,max_context=128)
    assert result['finish_reason']=='eos' and result['forward_calls']>1
    ids=torch.tensor([prompt.tolist()+result['token_ids']])
    logits=model(input_ids=ids,use_cache=False).logits[0]
    lp=sequence_logprob(logits,ids[0],result['token_ids'],prompt_length=3,eos_token_ids=[7])
    assert abs(float(lp.detach())-result['sequence_logprob'])<1e-5
    (-lp).backward()
    assert any(p.grad is not None and p.grad.abs().sum()>0 for p in model.parameters())
