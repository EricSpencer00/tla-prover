"""Pure exact-token grouped REINFORCE helpers; no sampling or optimizer steps.

Frozen contract: temperature1, untruncated categorical policy, G=4 same-prompt
TRAIN samples, sequence-SUM log probability including sampled terminal EOS.
Caller must attest on-policy sampling and exact verifier/rollout provenance.
Centered rewards include each sample itself (the usual G=4 group-mean baseline);
this is not leave-one-out REINFORCE, PPO, GRPO or a finite-candidate objective.
"""
import math
import re

GROUP_SIZE=4
TEMPERATURE=1.0


def _ids(values,name):
    import torch
    if isinstance(values,torch.Tensor):
        if values.ndim!=1 or values.dtype not in (torch.int32,torch.int64):
            raise ValueError(name+' must be one-dimensional integer IDs')
        values=values.detach().cpu().tolist()
    if not isinstance(values,(list,tuple)) or any(type(i) is not int or i<0 for i in values):
        raise ValueError(name+' must contain nonnegative integer IDs')
    return list(values)


def sequence_logprob(logits,input_token_ids,response_token_ids,*,prompt_length,
                     eos_token_ids,attention_mask=None,temperature=TEMPERATURE):
    """Score exact generated IDs, never retokenized text or synthetic appended EOS.

    logits[t] predicts input_token_ids[t+1]. prompt_length counts non-padding
    prompt tokens. Padding may occur on either edge, not inside the sequence.
    Every active token after the prompt must be one of the supplied sampled
    response IDs. The first EOS must be the last sampled response token.
    """
    import torch
    if type(temperature) not in (int,float) or not math.isfinite(temperature) or temperature!=1.0:
        raise ValueError('Frozen temperature1 required in sampling and scoring')
    if not isinstance(logits,torch.Tensor) or logits.ndim!=2 or not logits.is_floating_point():
        raise ValueError('Floating [sequence,vocabulary] logits required')
    ids=_ids(input_token_ids,'input');response=_ids(response_token_ids,'response');eos=_ids(eos_token_ids,'EOS')
    if (len(ids)!=logits.shape[0] or logits.shape[1]<2 or not eos or len(set(eos))!=len(eos)
            or any(i>=logits.shape[1] for i in [*ids,*eos]) or
            type(prompt_length) is not int or prompt_length<1):
        raise ValueError('Invalid sequence/vocabulary/prompt/EOS contract')
    if not response or response[-1] not in eos or any(i in eos for i in response[:-1]):
        raise ValueError('Nonempty sampled response with terminal EOS required')
    if attention_mask is None:
        mask=[1]*len(ids)
    else:
        mask=_ids(attention_mask,'attention mask')
        if len(mask)!=len(ids) or any(i not in (0,1) for i in mask):
            raise ValueError('Binary attention mask matching input required')
    active=[i for i,v in enumerate(mask) if v]
    if not active or active!=list(range(active[0],active[-1]+1)):
        raise ValueError('Only contiguous active input with edge padding supported')
    if len(active)!=prompt_length+len(response) or [ids[i] for i in active[prompt_length:]]!=response:
        raise ValueError('Exact prompt boundary and sampled response IDs required')
    start=active[0]+prompt_length
    positions=torch.arange(start-1,start+len(response)-1,device=logits.device)
    selected=logits.index_select(0,positions)
    if not bool(torch.isfinite(selected).all()):
        raise ValueError('Nonfinite response-predicting logits')
    # Float32 for low precision CUDA logits; preserve float64 CPU verification.
    selected=selected if selected.dtype==torch.float64 else selected.float()
    labels=torch.tensor(response,dtype=torch.long,device=logits.device)
    return selected.log_softmax(-1).gather(1,labels[:,None]).sum()


def group_advantages(samples):
    """Return explicit exclusion instead of silently filtering any of G=4 rows."""
    if not isinstance(samples,(list,tuple)) or len(samples)!=GROUP_SIZE:
        raise ValueError('Exactly four sampled outcomes required')
    if any(not isinstance(s,dict) for s in samples):raise ValueError('Outcome records required')
    for key in ('task_id','prompt_sha256','policy_sha256'):
        values=[s.get(key) for s in samples]
        if not all(isinstance(v,str) and v for v in values) or len(set(values))!=1:
            raise ValueError('Same task, prompt and frozen policy required')
        if key.endswith('sha256') and not re.fullmatch('[0-9a-f]{64}',values[0]):
            raise ValueError('Explicit prompt/policy hashes required')
    if any(s.get('split')!='train' for s in samples):raise ValueError('TRAIN-only objective')
    result=dict(task_id=samples[0]['task_id'],prompt_sha256=samples[0]['prompt_sha256'],
        policy_sha256=samples[0]['policy_sha256'],group_size=4,temperature=1.0,
        eligible=False,advantages=None,reward_variance=None)
    if any(s.get('finish_reason')!='eos' for s in samples):
        return dict(result,exclusion='incomplete_generation')
    if any(s.get('measured_model_outcome') is not True or s.get('reward_eligible') is not True or
           type(s.get('reward')) not in (int,float) or s['reward'] not in (0,1) for s in samples):
        return dict(result,exclusion='unmeasured_reward')
    rewards=[float(s['reward']) for s in samples];mean=sum(rewards)/4
    advantages=[r-mean for r in rewards];variance=sum(a*a for a in advantages)/4
    if variance==0:return dict(result,exclusion='zero_variance',reward_variance=0.0)
    return dict(result,eligible=True,exclusion=None,advantages=advantages,rewards=rewards,reward_variance=variance)


def centered_reinforce_loss(sequence_logps,admission,*,eligible_groups=1):
    """One group contribution; sum contributions then take ONE optimizer step.

    eligible_groups must be frozen after all groups have been audited. Sequence
    lengths are never used as divisors. Excluded groups return None, not a
    misleading zero-gradient optimizer update. Advantages are detached data.
    A list may include constant scalar zero placeholders, as used by the
    sequential helper. Callers scoring all four actual samples must provide
    their differentiable logprobs; aggregate requires_grad cannot attest that.
    """
    import torch
    if type(eligible_groups) is not int or eligible_groups<1:
        raise ValueError('Positive eligible-group denominator required')
    if not isinstance(admission,dict) or admission.get('group_size')!=4 or admission.get('temperature')!=1.0:
        raise ValueError('Frozen group admission required')
    if admission.get('eligible') is False:return None
    if admission.get('eligible') is not True:raise ValueError('Explicit group eligibility required')
    rewards=admission.get('rewards');advantages=admission.get('advantages')
    if (not isinstance(rewards,list) or len(rewards)!=4 or any(type(r) not in (int,float) or r not in (0,1) for r in rewards)
            or advantages!=[r-sum(rewards)/4 for r in rewards] or not any(advantages)):
        raise ValueError('Exact nonzero within-group centered rewards required')
    if isinstance(sequence_logps,(list,tuple)):
        if len(sequence_logps)!=4 or any(not isinstance(x,torch.Tensor) or x.ndim!=0 for x in sequence_logps):
            raise ValueError('Four scalar differentiable sequence logprobs required')
        sequence_logps=torch.stack(list(sequence_logps))
    if (not isinstance(sequence_logps,torch.Tensor) or sequence_logps.shape!=(4,) or
            not sequence_logps.is_floating_point() or not sequence_logps.requires_grad or
            not bool(torch.isfinite(sequence_logps).all())):
        raise ValueError('Finite differentiable four-vector required')
    weights=torch.tensor(advantages,dtype=sequence_logps.dtype,device=sequence_logps.device)
    return -(weights*sequence_logps).sum()/(4*eligible_groups)


def sample_reinforce_loss(sequence_logp,admission,sample_index,*,eligible_groups=1):
    """Memory-bounded equivalent: backward once per sample, step once in total.

    Zero the optimizer before the complete batch, not between these sample
    contributions. This helper needs only one causal-forward graph at a time.
    """
    import torch
    if type(sample_index) is not int or not 0<=sample_index<4:
        raise ValueError('Sample index must identify one of the four outcomes')
    if not isinstance(sequence_logp,torch.Tensor) or sequence_logp.ndim!=0:
        raise ValueError('One scalar sequence logprob required')
    values=[sequence_logp if i==sample_index else torch.zeros_like(sequence_logp) for i in range(4)]
    return centered_reinforce_loss(values,admission,eligible_groups=eligible_groups)
