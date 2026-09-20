import copy
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
import torch

from tools import proof_token_rl_worker as w
from tools.proof_token_rl_packet import load_requests,digest,sha,EOS_IDS

ROOT=Path(__file__).resolve().parents[1]


@pytest.fixture(autouse=True)
def synthetic_worker_eos(monkeypatch):
    # Only the worker's synthetic four-token scorer uses EOS3; packet/mailbox
    # fixtures remain bound to their independently imported production EOS IDs.
    monkeypatch.setattr(w,'EOS_IDS',[3])


@pytest.fixture
def mailbox():
    raw=(ROOT/'results/runs/proof-token-rl-requests-20260906-v1/requests.json').read_bytes()
    packet=load_requests(raw,w.REQUESTS_SHA);rows=[];rewardrows=[]
    for request in packet['requests']:
        r=dict(**request,request_sha256=digest(request),status='generated',
            input_token_ids=[1,2],input_token_ids_sha256=digest([1,2]),input_tokens=2,
            rendered_prompt='x',rendered_prompt_sha256=sha(b'x'),token_ids=[EOS_IDS[-1]],
            token_ids_sha256=digest([EOS_IDS[-1]]),output_tokens=1,raw_reply='',raw_reply_sha256=sha(b''),
            selected_token_logprobs=[-.5],sequence_logprob=-.5,token_entropies=[1.],finish_reason='eos',
            eos_reached=True,hit_token_limit=False,deadline_exceeded=False,temperature=1.,
            distribution='full_vocabulary_categorical',elapsed_seconds=1.)
        rows.append(r)
        rewardrows.append(dict(**{k:request[k] for k in ('sample_id','task_id','prompt_sha256','policy_sha256','split','reward_stage')},
            finish_reason='eos',measured_model_outcome=True,reward_eligible=True,reward=request['attempt']%2,
            status='pass' if request['attempt']%2 else 'model_sany_reject',evidence={'bound':True}))
    rewards=dict(schema=1,requests_sha256=w.REQUESTS_SHA,rollouts_sha256='c'*64,policy_sha256=w.POLICY_SHA,
        reward_stage='sany_partial',complete=True,rows=rewardrows,verifier_identity={'runtime':'bound'})
    return packet,rows,rewards


def receipt(raw):
    return dict(schema=1,rewards_sha256=sha(raw),requests_sha256=w.REQUESTS_SHA,rollouts_sha256='c'*64,
                bridge_source_sha256='d'*64,provenance_verified=True)


def validate(mailbox):
    packet,rows,rewards=mailbox;raw=json.dumps(rewards).encode()
    return w.validate_rewards(packet,rows,raw,receipt(raw),rollouts_sha256='c'*64,bridge_source_sha256='d'*64)


def test_full_bound_mailbox(mailbox):assert len(validate(mailbox)['rows'])==32


@pytest.mark.parametrize('field,value',[
    ('sample_id','other'),('policy_sha256','e'*64),('reward_stage','strict_tlaps'),
    ('split','development'),('finish_reason','time_limit'),('reward',True),
    ('measured_model_outcome',False),('reward_eligible',False)])
def test_reward_binding_mutations_rejected(mailbox,field,value):
    mailbox[2]['rows'][0][field]=value
    with pytest.raises(ValueError):validate(mailbox)


def test_unknown_requires_null_and_both_false(mailbox):
    mailbox[2]['rows'][0].update(reward=None,measured_model_outcome=False,reward_eligible=False,status='unmeasured_unknown')
    assert validate(mailbox)['rows'][0]['reward'] is None


def test_receipt_hash_failure(mailbox):
    packet,rows,rewards=mailbox;raw=json.dumps(rewards).encode();proof=receipt(raw);proof['rewards_sha256']='f'*64
    with pytest.raises(ValueError):w.validate_rewards(packet,rows,raw,proof,rollouts_sha256='c'*64,bridge_source_sha256='d'*64)


def test_reordered_reward_samples_rejected(mailbox):
    rows=mailbox[2]['rows'];rows[0],rows[1]=rows[1],rows[0]
    with pytest.raises(ValueError):validate(mailbox)


class Tiny(torch.nn.Module):
    def __init__(self):
        super().__init__();self.weight=torch.nn.Parameter(torch.zeros((4,4)))
    def forward(self,input_ids,attention_mask,use_cache,past_key_values=None):
        old=0 if past_key_values is None else past_key_values
        assert attention_mask.shape==(1,old+input_ids.shape[1])
        return SimpleNamespace(logits=self.weight[input_ids],past_key_values=old+input_ids.shape[1])


def cpu_batch(net):
    rows=[];rewards=[]
    for i in range(32):
        row=dict(sample_id=str(i),input_token_ids=[0,1],token_ids=[2 if i%2 else 1,3],finish_reason='eos')
        with torch.no_grad():row['selected_token_logprobs']=w.teacher_logps(net,row,'cpu').tolist()
        rows.append(row)
        rewards.append(dict(task_id=str(i//4),prompt_sha256='a'*64,policy_sha256='b'*64,split='train',
            measured_model_outcome=True,reward_eligible=True,reward=i%2,finish_reason='eos'))
    return rows,rewards


def test_real_cpu_one_update_and_fresh_optimizer():
    net=Tiny();rows,rewards=cpu_batch(net);before=net.weight.detach().clone();guards=[]
    result,opt=w.one_update(net,{'weight':net.weight},rows,rewards,device='cpu',guard=lambda:guards.append(True))
    assert result['actual_updates']==1 and result['eligible_groups']==8
    assert result['gradient_norm']>0 and len(result['teacher_logprob_checks'])==32
    assert not torch.equal(net.weight,before)
    assert int(next(iter(opt.state.values()))['step'])==1
    assert len(guards)==34


def test_zero_variance_no_optimizer_or_parameter_change():
    net=Tiny();rows,rewards=cpu_batch(net);before=net.weight.detach().clone()
    for r in rewards:r['reward']=1
    result,opt=w.one_update(net,{'weight':net.weight},rows,rewards,device='cpu')
    assert result['actual_updates']==0 and opt is None and torch.equal(net.weight,before)


def test_logprob_mismatch_fails_before_update():
    net=Tiny();rows,rewards=cpu_batch(net);before=net.weight.detach().clone()
    rows[0]['selected_token_logprobs'][0]+=1
    with pytest.raises(w.LogprobDiscrepancyError,match='discrepancy') as error:
        w.one_update(net,{'weight':net.weight},rows,rewards,device='cpu')
    assert torch.equal(net.weight,before)
    persisted=json.loads(json.dumps(w.failure_record(error.value)))
    report=persisted['logprob_discrepancy']
    assert report['max_abs']==pytest.approx(1.) and report['mean_abs']==pytest.approx(.5)
    assert report['sample_id']=='0' and report['phase']=='longest_sequence_preflight'
    assert report['worst_token_index']==0 and report['max_limit']==.03 and report['mean_limit']==.003


def test_memory_preflight_failure_has_no_optimizer_step():
    net=Tiny();rows,rewards=cpu_batch(net);before=net.weight.detach().clone()
    def fail():w.memory_guard(37*1024**3,37*1024**3)
    with pytest.raises(ValueError,match='36GiB'):w.one_update(net,{'weight':net.weight},rows,rewards,device='cpu',guard=fail)
    assert torch.equal(net.weight,before)


@pytest.mark.parametrize('delta',[.031,.004])
def test_frozen_token_and_mean_logprob_limits(delta):
    with pytest.raises(ValueError):w.check_logps(torch.tensor([delta]),[0.])


def test_update_budget_reserve_before_backward():
    net=Tiny();rows,rewards=cpu_batch(net);ticks=iter([0,121])
    with pytest.raises(TimeoutError):w.one_update(net,{'weight':net.weight},rows,rewards,device='cpu',clock=lambda:next(ticks))
    assert net.weight.grad is None


@pytest.mark.parametrize('status,reward', [('pass',0),('model_sany_reject',1),
    ('model_contract',1),('model_extraction',1),('unmeasured_unknown',0),('unmeasured_infrastructure',1)])
def test_status_cannot_be_relabelled_as_arbitrary_reward(mailbox,status,reward):
    mailbox[2]['rows'][0].update(status=status,reward=reward)
    with pytest.raises(ValueError):validate(mailbox)


def test_exact_parent_snapshot_detects_sampling_mutation():
    net=Tiny();selected={'weight':net.weight};initial={'weight':net.weight.detach().clone()}
    w.assert_parent_unchanged(selected,initial)
    with torch.no_grad():net.weight[0,0]+=1
    with pytest.raises(ValueError,match='parent weights changed'):w.assert_parent_unchanged(selected,initial)


def test_sampling_generator_state_roundtrip(tmp_path):
    generator=torch.Generator().manual_seed(w.SEED)
    path=tmp_path/'rng.pt';digest=w.persist_generator_state(generator,path)
    assert digest==w.file_sha(path)
    expected=torch.multinomial(torch.ones(4),4,replacement=True,generator=generator)
    restored=torch.Generator();restored.set_state(torch.load(path,weights_only=True))
    assert torch.equal(expected,torch.multinomial(torch.ones(4),4,replacement=True,generator=restored))


def test_real_llama_cached_one_update(monkeypatch):
    from harness.test_proof_token_rl_cached_score import tiny_llama
    from tools.proof_token_rl_sampling import sample_tokens
    monkeypatch.setattr(w,'EOS_IDS',[7])
    net=tiny_llama();selected={n:p for n,p in net.named_parameters() if p.requires_grad}
    before={n:p.detach().clone() for n,p in selected.items()}
    rows=[];rewards=[];prompt=torch.tensor([1,2,3])
    for index in range(4):
        result=sample_tokens(net,prompt,generator=torch.Generator().manual_seed(91+index),
            eos_token_ids=[7],max_new_tokens=64,max_context=128,seconds=20)
        assert result['finish_reason']=='eos'
        rows.append(dict(sample_id=str(index),input_token_ids=prompt.tolist(),**result))
    rows=[dict(rows[i%4],sample_id=str(i)) for i in range(32)]
    for index in range(32):
        rewards.append(dict(task_id=str(index//4),prompt_sha256='a'*64,policy_sha256='b'*64,
            split='train',measured_model_outcome=True,reward_eligible=True,
            reward=index%2 if index<4 else 1,finish_reason='eos'))
    def forbidden_teacher(*args,**kwargs):raise AssertionError('Full teacher must not train')
    monkeypatch.setattr(w,'teacher_logps',forbidden_teacher)
    result,optimizer=w.one_update(net,selected,rows,rewards,device='cpu')
    assert result['actual_updates']==1 and result['eligible_groups']==1
    assert result['scoring']==w.SCORING and result['longest_sequence_preflight']['max_abs']<1e-6
    assert len(result['teacher_logprob_checks'])==4
    assert all(int(entry['step'])==1 for entry in optimizer.state.values())
    for suffix in ('k_proj.weight','v_proj.weight'):
        parameters=[(n,p) for n,p in selected.items() if n.endswith(suffix)]
        assert len(parameters)==1
        name,parameter=parameters[0]
        assert parameter.grad.abs().sum()>0 and not torch.equal(before[name],parameter)


def test_remaining_budget_passed_to_cached_scorer(monkeypatch):
    net=Tiny();rows,rewards=cpu_batch(net);seen=[]
    def fake_score(*args,**kwargs):
        seen.append(kwargs['seconds']);raise TimeoutError('synthetic scoring timeout')
    monkeypatch.setattr(w,'cached_logps',fake_score)
    ticks=iter([0,10,20])
    with pytest.raises(TimeoutError):
        w.one_update(net,{'weight':net.weight},rows,rewards,device='cpu',clock=lambda:next(ticks))
    assert seen==[100] and net.weight.grad is None


def test_preflight_backward_exhaustion_stops_before_optimizer(monkeypatch):
    net=Tiny();rows,rewards=cpu_batch(net);now=[0.]
    def elapsed(gradient):now[0]=121.;return gradient
    handle=net.weight.register_hook(elapsed)
    def forbidden_optimizer(*args,**kwargs):raise AssertionError('Optimizer created after deadline')
    monkeypatch.setattr(torch.optim,'AdamW',forbidden_optimizer)
    try:
        with pytest.raises(TimeoutError,match='checkpoint reserve'):
            w.one_update(net,{'weight':net.weight},rows,rewards,device='cpu',clock=lambda:now[0])
    finally:handle.remove()
    assert torch.equal(net.weight,torch.zeros_like(net.weight))


def test_main_persists_discrepancy_before_reraising(monkeypatch,tmp_path):
    report=dict(max_abs=.15,mean_abs=.02,tokens=5,worst_token_index=2)
    def failed_run(args):raise w.LogprobDiscrepancyError(report)
    monkeypatch.setattr(w,'run',failed_run)
    monkeypatch.setattr(w.sys,'argv',['worker','--requests','r','--broader-prompts','b',
        '--model-path','m','--checkpoint','c','--output',str(tmp_path)])
    with pytest.raises(w.LogprobDiscrepancyError):w.main()
    assert json.loads((tmp_path/'failure.json').read_text())['logprob_discrepancy']==report
