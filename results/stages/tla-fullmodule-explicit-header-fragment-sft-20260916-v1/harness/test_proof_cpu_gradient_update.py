import io
import pytest
import torch
from tools.proof_cpu_gradient_update import CPUGradientUpdate,validate_prepared
from tools.proof_saved_tensor_census import tiny_model
from tools.proof_token_rl_cached_score_compact import cached_token_logps


def rewards():
    return [dict(sample_id=f's{i}',task_id=f't{i//4}',prompt_sha256='a'*64,policy_sha256='b'*64,
                 split='train',finish_reason='eos',measured_model_outcome=True,reward_eligible=True,
                 reward=int(i==1)) for i in range(32)]


def parameters():return {f'p{i}':torch.nn.Parameter(torch.ones(i+1)) for i in range(9)}


def fill(update):
    for i,request in enumerate(update.requests):
        for p in update.selected.values():p.grad=torch.full_like(p,float(i+1))
        update.accumulate(request['sample_id'])


def test_prepare_commit_reload_and_exact_parent_immutability():
    selected=parameters();update=CPUGradientUpdate(selected,rewards());fill(update)
    assert all(p.grad is None for p in selected.values())
    result=update.prepare()
    assert all(torch.equal(p,update.initial[n]) for n,p in selected.items())
    assert result['summary']['actual_updates']==1 and result['summary']['parameter_delta_l2']>0
    buffer=io.BytesIO();torch.save(result,buffer);buffer.seek(0)
    restored=torch.load(buffer,weights_only=False);validate_prepared(restored,update.initial)
    assert all(torch.equal(restored['trainable_state'][n],p) for n,p in result['trainable_state'].items())
    update.commit()
    assert all(torch.equal(p,result['trainable_state'][n]) for n,p in selected.items())
    with pytest.raises(ValueError):update.commit()


@pytest.mark.parametrize('kind',['unknown','zero','missing'])
def test_no_optimizer_for_ineligible_or_missing(monkeypatch,kind):
    rows=rewards()
    if kind=='unknown':rows[1]['reward_eligible']=False
    if kind=='zero':rows[1]['reward']=0
    update=CPUGradientUpdate(parameters(),rows)
    def forbidden(*a,**k):raise AssertionError('Optimizer must not be constructed')
    monkeypatch.setattr(torch.optim,'AdamW',forbidden)
    if kind=='missing':
        with pytest.raises(ValueError,match='Missing'):update.prepare()
    else:
        result=update.prepare();assert result['summary']['actual_updates']==0
        assert result['optimizer_state'] is None


def test_invalid_gradient_order_and_parent_drift_fail_closed():
    update=CPUGradientUpdate(parameters(),rewards())
    for p in update.selected.values():p.grad=torch.ones_like(p)
    with pytest.raises(ValueError,match='order'):update.accumulate('s1')
    assert all(p.grad is None for p in update.selected.values())
    with pytest.raises(ValueError):update.prepare()
    update=CPUGradientUpdate(parameters(),rewards())
    for p in update.selected.values():p.grad=torch.ones_like(p)
    next(iter(update.selected.values())).grad.fill_(float('nan'))
    with pytest.raises(ValueError):update.accumulate('s0')
    assert all(p.grad is None for p in update.selected.values())
    update=CPUGradientUpdate(parameters(),rewards())
    with torch.no_grad():next(iter(update.selected.values())).add_(1)
    with pytest.raises(ValueError,match='parent'):update.prepare()


def test_zero_aggregate_never_constructs_optimizer(monkeypatch):
    update=CPUGradientUpdate(parameters(),rewards())
    for request in update.requests:
        for p in update.selected.values():p.grad=torch.ones_like(p)
        update.accumulate(request['sample_id'])
    def forbidden(*a,**k):raise AssertionError('Zero gradient must not construct optimizer')
    monkeypatch.setattr(torch.optim,'AdamW',forbidden)
    with pytest.raises(ValueError,match='Nonzero'):update.prepare()


@pytest.mark.parametrize('mutation',['shape','nonfinite','optimizer','duplicate_ids','maximize','groups','coefficient','step_shape','step_dtype'])
def test_commit_validates_everything_before_any_device_copy(mutation):
    update=CPUGradientUpdate(parameters(),rewards());fill(update);result=update.prepare()
    last=list(result['trainable_state'])[-1]
    if mutation=='shape':result['trainable_state'][last]=torch.zeros(1)
    if mutation=='nonfinite':result['trainable_state'][last].fill_(float('nan'))
    if mutation=='optimizer':result['optimizer_state']['state'][8]['step'].fill_(2)
    if mutation=='duplicate_ids':result['optimizer_state']['param_groups'][0]['params'][-1]=0
    if mutation=='maximize':result['optimizer_state']['param_groups'][0]['maximize']=True
    if mutation=='groups':result['summary']['groups'][0]['task_id']='tampered'
    if mutation=='coefficient':result['summary']['ledger'][0]['coefficient']*=-1
    if mutation=='step_shape':result['optimizer_state']['state'][8]['step']=torch.tensor([1.])
    if mutation=='step_dtype':result['optimizer_state']['state'][8]['step']=torch.tensor(1.,dtype=torch.float64)
    with pytest.raises(ValueError):update.commit()
    assert all(torch.equal(p,update.initial[n]) for n,p in update.selected.items())


def test_cpu_estimator_matches_explicit_weighted_causal_llama_loss():
    # Isolate estimator algebra in FP32. Weighting before versus after BF16
    # backward changes rounding and is explicitly not a bitwise identity claim.
    model=tiny_model().float();selected={n:p for n,p in model.named_parameters() if p.requires_grad}
    update=CPUGradientUpdate(selected,rewards());prompt=torch.arange(24)%126+1
    responses=[torch.tensor([2+i,4+i,6+i,127]) for i in range(4)]
    def sum_logps(response):
        return cached_token_logps(model,prompt,response,eos_token_ids=[127],seconds=20,max_context=512).sum()
    for request,response in zip(update.requests,responses):
        sum_logps(response).backward();update.accumulate(request['sample_id'])
    expected=sum(request['coefficient']*sum_logps(response)
                 for request,response in zip(update.requests,responses))
    expected.backward()
    for n,p in selected.items():
        torch.testing.assert_close(update.accumulated[n],p.grad,rtol=1e-5,atol=1e-6)
    for p in selected.values():p.grad=None
    result=update.prepare();assert result['summary']['actual_updates']==1
    assert all(torch.equal(p,update.initial[n]) for n,p in selected.items())
