import math

import pytest
import torch

from tools.proof_token_rl_objective import sequence_logprob,group_advantages,centered_reinforce_loss,sample_reinforce_loss


def samples(rewards=(1,0,0,0)):
    return [dict(task_id='train-proof',split='train',prompt_sha256='a'*64,policy_sha256='b'*64,
                 finish_reason='eos',measured_model_outcome=True,reward_eligible=True,reward=r) for r in rewards]


def score(logits,ids=(0,1,2,3),response=(2,3),**kwargs):
    return sequence_logprob(logits,list(ids),list(response),prompt_length=2,eos_token_ids=[3],**kwargs)


def test_exact_hand_calculated_shift_sum_and_eos():
    probs=torch.tensor([[.25,.25,.25,.25],[.1,.2,.3,.4],[.2,.2,.1,.5],[.7,.1,.1,.1]],dtype=torch.float64)
    logits=probs.log().requires_grad_()
    result=score(logits)
    assert result.item()==pytest.approx(math.log(.3)+math.log(.5),abs=1e-12)
    result.backward()
    assert torch.equal(logits.grad[0],torch.zeros(4,dtype=torch.float64))
    assert torch.equal(logits.grad[3],torch.zeros(4,dtype=torch.float64))
    assert torch.allclose(logits.grad[1],torch.tensor([-.1,-.2,.7,-.4],dtype=torch.float64))
    assert torch.allclose(logits.grad[2],torch.tensor([-.2,-.2,-.1,.5],dtype=torch.float64))


def test_padding_both_edges_is_not_scored():
    logits=torch.zeros((7,4),dtype=torch.float64,requires_grad=True)
    result=sequence_logprob(logits,[3,0,1,2,3,3,3],[2,3],prompt_length=2,eos_token_ids=[3],attention_mask=[0,1,1,1,1,0,0])
    assert result.item()==pytest.approx(2*math.log(.25))
    result.backward()
    assert torch.equal(logits.grad[[0,1,4,5,6]],torch.zeros((5,4),dtype=torch.float64))
    assert logits.grad[2,2]>0 and logits.grad[3,3]>0


def test_length_is_sum_not_mean():
    short=score(torch.zeros((4,4)))
    long=sequence_logprob(torch.zeros((5,4)),[0,1,2,2,3],[2,2,3],prompt_length=2,eos_token_ids=[3])
    assert long.item()==pytest.approx(short.item()*1.5)


@pytest.mark.parametrize('temperature',[0,.5,2,float('nan'),float('inf'),True])
def test_frozen_temperature(temperature):
    with pytest.raises(ValueError):score(torch.zeros((4,4)),temperature=temperature)


@pytest.mark.parametrize('ids,response',[
    ([0,1,2,3],[1,3]),([0,1,2,3],[2]),([0,1,2,2],[2,2]),
    ([0,1,3,2,3],[3,2,3]),([0,1],[]),([0,1,2,4],[2,4]),
])
def test_exact_sampled_ids_and_eos_required(ids,response):
    with pytest.raises(ValueError):score(torch.zeros((len(ids),4)),ids,response)


def test_internal_padding_rejected():
    with pytest.raises(ValueError):score(torch.zeros((4,4)),attention_mask=[1,0,1,1])


def test_nonfinite_scored_logits_rejected():
    logits=torch.zeros((4,4));logits[1,0]=float('nan')
    with pytest.raises(ValueError):score(logits)


def test_group_centering_and_exact_gradient():
    admission=group_advantages(samples())
    assert admission['advantages']==[.75,-.25,-.25,-.25]
    assert admission['reward_variance']==.1875
    logps=torch.tensor([-2.,-3.,-4.,-5.],requires_grad=True)
    loss=centered_reinforce_loss(logps,admission,eligible_groups=2)
    assert loss.item()==pytest.approx(-(.75*-2-.25*-3-.25*-4-.25*-5)/8)
    loss.backward()
    assert torch.equal(logps.grad,torch.tensor([-.75,.25,.25,.25])/8)


def test_real_token_gradients_raise_success_relative_probability():
    # Separate prefix states ensure normalizers cannot be canceled across samples.
    logits=[torch.zeros((4,4),dtype=torch.float64,requires_grad=True) for _ in range(4)]
    loss=centered_reinforce_loss([score(x) for x in logits],group_advantages(samples()))
    loss.backward()
    assert logits[0].grad[1,2]<0 and logits[0].grad[1,0]>0
    assert logits[1].grad[1,2]>0 and logits[1].grad[1,0]<0
    assert logits[0].grad[2,3]<0  # EOS itself participates.


@pytest.mark.parametrize('rewards',[(0,0,0,0),(1,1,1,1)])
def test_zero_variance_has_no_loss_or_update(rewards):
    admission=group_advantages(samples(rewards))
    assert admission['exclusion']=='zero_variance'
    assert centered_reinforce_loss(None,admission) is None


@pytest.mark.parametrize('field,value,reason',[
    ('reward',None,'unmeasured_reward'),('reward',float('nan'),'unmeasured_reward'),
    ('reward',True,'unmeasured_reward'),('measured_model_outcome',False,'unmeasured_reward'),
    ('reward_eligible',False,'unmeasured_reward'),('finish_reason','time_limit','incomplete_generation'),
    ('finish_reason','token_limit','incomplete_generation'),
])
def test_any_unknown_excludes_full_group(field,value,reason):
    rows=samples();rows[2][field]=value
    admission=group_advantages(rows)
    assert admission['exclusion']==reason and admission['advantages'] is None
    assert centered_reinforce_loss(None,admission) is None


@pytest.mark.parametrize('field,value',[('split','development'),('split','fresh_evaluation'),
    ('task_id','other'),('prompt_sha256','c'*64),('policy_sha256','c'*64)])
def test_no_cross_task_policy_or_eval_group(field,value):
    rows=samples();rows[2][field]=value
    with pytest.raises(ValueError):group_advantages(rows)


def test_partial_group_not_filtered():
    with pytest.raises(ValueError):group_advantages(samples()[:3])


def test_no_detached_logprob_update_claim():
    with pytest.raises(ValueError):centered_reinforce_loss(torch.zeros(4),group_advantages(samples()))


def test_forged_advantages_rejected():
    admission=group_advantages(samples());admission['advantages']=[1.,0.,0.,0.]
    with pytest.raises(ValueError):centered_reinforce_loss(torch.zeros(4,requires_grad=True),admission)


def test_sequential_graph_accumulation_equals_full_group():
    weights=torch.randn((4,4),dtype=torch.float64,requires_grad=True)
    admission=group_advantages(samples((1,0,1,0)))
    full=centered_reinforce_loss([score(weights) for _ in range(4)],admission)
    full.backward();expected=weights.grad.clone();weights.grad=None
    for i in range(4):sample_reinforce_loss(score(weights),admission,i).backward()
    assert torch.allclose(weights.grad,expected,atol=1e-12)
    # Independently parameterized responses also match, not just shared zeros.
    values=torch.tensor([-2.,-3.,-4.,-5.],requires_grad=True)
    full=centered_reinforce_loss(values,admission);full.backward();expected=values.grad.clone();values.grad=None
    for i in range(4):sample_reinforce_loss(values[i],admission,i).backward()
    assert torch.equal(values.grad,expected)


def test_tensor_input_ids_and_float32_gradient():
    logits=torch.zeros((4,4),dtype=torch.float32,requires_grad=True)
    value=sequence_logprob(logits,torch.tensor([0,1,2,3]),torch.tensor([2,3]),prompt_length=2,
                          eos_token_ids=[3],attention_mask=torch.tensor([1,1,1,1]))
    value.backward()
    assert value.dtype==torch.float32 and torch.isfinite(logits.grad).all()


def test_eos_only_is_a_real_sample_with_causal_probability_and_gradient():
    probs=torch.tensor([[.25,.25,.25,.25],[.1,.2,.3,.4],[.7,.1,.1,.1]],dtype=torch.float64)
    logits=probs.log().requires_grad_()
    value=score(logits,ids=[0,1,3],response=[3])
    assert value.item()==pytest.approx(math.log(.4),abs=1e-12)
    value.backward()
    assert torch.allclose(logits.grad[1],torch.tensor([-.1,-.2,-.3,.6],dtype=torch.float64))
    assert torch.equal(logits.grad[[0,2]],torch.zeros((2,4),dtype=torch.float64))
    # A bound contract rejection for empty decoded text remains a valid negative.
    admission=group_advantages(samples((0,1,1,1)))
    assert admission['eligible'] and admission['advantages'][0]==-.75
