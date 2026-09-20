"""Bounded frozen-policy TRAIN8 sampling, authenticated-mailbox reward, one update.

Only the external controller sends reward evidence. No checker/network calls.
One fresh AdamW1e-6 update at most; partial SANY reward is not proof success.
"""
import argparse
from contextlib import nullcontext
import json
import math
import os
from pathlib import Path
import random
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_token_rl_packet import (load_requests,validate_rollouts,validate_rollout,digest,sha,
                                        POLICY_SHA,EOS_IDS,BROADER_SHA)
from tools.proof_token_rl_objective import group_advantages,sample_reinforce_loss
from tools.proof_token_rl_sampling import sample_tokens
from tools.proof_token_rl_cached_score import cached_token_logps
from tools.proof_cuda_train import file_sha,dump

REQUESTS_SHA='fa56d5234e710ec646ab4ba2fc3e5771dc699780ea4f05a4da3763fdafb7ebf5'
MODEL_SHA='be21cca8df80e80b27b11aa238d8d77192e3c0e47a096224d1292559190a4cf9'
VERSIONS={'torch_version':'2.11.0+cu128','transformers_version':'5.6.2'}
SEED=20260929
SOURCES=('tools/proof_token_rl_worker.py','tools/proof_token_rl_packet.py','tools/proof_token_rl_sampling.py',
    'tools/proof_token_rl_cached_score.py',
    'tools/proof_token_rl_objective.py','tools/proof_token_rl_rewards.py','tools/proof_cuda_train.py',
    'tools/proof_cuda_eval.py','tools/proof_broader_packet.py','tools/proof_whole_packet.py',
    'tools/proof_candidate_rank.py','tools/proof_sequence_train.py','tools/proof_repair_pilot.py')
MEMORY_LIMIT=36*1024**3
SCORING=dict(method='forced-token incremental differentiable KV-cache replay',
    precision_context='one fresh outer autocast per response; nested matching forward contexts',
    temperature=1.,sequence_reduction='sum including actual sampled EOS',
    max_token_logprob_discrepancy=.03,mean_token_logprob_discrepancy=.003,
    checkpoint_reserve_seconds=60)


def source_hashes():return {n:file_sha(ROOT/n) for n in SOURCES}


def memory_guard(allocated,reserved):
    if any(type(v) not in (int,float) or not math.isfinite(v) or v<0 or v>MEMORY_LIMIT for v in (allocated,reserved)):
        raise ValueError('36GiB allocated/reserved memory ceiling exceeded')


def admit(a):
    import torch,transformers
    from tools.proof_cuda_train import model_files,PROFILE
    from tools.proof_cuda_eval import encode_prompt
    output=a.output.resolve()
    for value in (a.requests,a.broader_prompts,a.model_path,a.checkpoint):
        source=value.resolve()
        if output==source or output in source.parents or source in output.parents:
            raise ValueError('Output must be isolated from immutable inputs')
    packet=load_requests(a.requests.read_bytes(),REQUESTS_SHA,broader_raw=a.broader_prompts.read_bytes())
    if packet['reward_stage']!='sany_partial' or file_sha(a.checkpoint)!=POLICY_SHA:
        raise ValueError('Exact partial-SANY experiment/parent required')
    versions=dict(torch_version=torch.__version__,transformers_version=transformers.__version__)
    files=model_files(a.model_path)
    if (versions!=VERSIONS or digest(files)!=MODEL_SHA or
        PROFILE!='frozen bf16 base with float32 final transformer layer; bf16 autocast'):
        raise ValueError('Pinned model, libraries and dtype profile required')
    if json.loads((a.model_path/'generation_config.json').read_text())['eos_token_id']!=EOS_IDS:
        raise ValueError('Pinned model EOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encodings=[encode_prompt(tokenizer,t) for t in packet['tasks']]
    if any(e['input_tokens']+3072>8192 for e in encodings):raise ValueError('Full sampled context budget required')
    return dict(requests_sha256=REQUESTS_SHA,broader_prompts_sha256=BROADER_SHA,policy_sha256=POLICY_SHA,
        reward_stage='sany_partial',model_files=files,dtype_profile=PROFILE,seed=SEED,
        implementation_sha256=source_hashes(),**versions,encodings=encodings,
        sampling_reward_seconds=1500,update_checkpoint_seconds=180,learning_rate=1e-6,
        sampling_seconds=1200,reward_exchange_reserve_seconds=300,
        scoring=dict(SCORING),
        requested_optimizer_updates=1,trainable_parameters=218112000,
        algorithm='one-batch centered same-prompt token-sequence-SUM REINFORCE, no PPO or finite-candidate policy')


def validate_rewards(packet,rollouts,raw,receipt,*,rollouts_sha256,bridge_source_sha256):
    validate_rollouts(packet,rollouts)
    receipt_fields={'schema','rewards_sha256','requests_sha256','rollouts_sha256','bridge_source_sha256','provenance_verified'}
    if (not isinstance(receipt,dict) or set(receipt)!=receipt_fields or receipt['schema']!=1 or
        receipt['provenance_verified'] is not True or receipt['rewards_sha256']!=sha(raw) or
        receipt['requests_sha256']!=REQUESTS_SHA or receipt['rollouts_sha256']!=rollouts_sha256 or
        receipt['bridge_source_sha256']!=bridge_source_sha256):raise ValueError('Bound controller reward receipt required')
    reward=json.loads(raw)
    fields={'schema','requests_sha256','rollouts_sha256','policy_sha256','reward_stage','complete','rows','verifier_identity'}
    if (set(reward)!=fields or reward['schema']!=1 or reward['requests_sha256']!=REQUESTS_SHA or
        reward['rollouts_sha256']!=rollouts_sha256 or reward['policy_sha256']!=POLICY_SHA or
        reward['reward_stage']!='sany_partial' or reward['complete'] is not True or
        not isinstance(reward['verifier_identity'],dict) or not reward['verifier_identity'] or len(reward['rows'])!=32):
        raise ValueError('Full immutable32 SANY reward bindings required')
    row_fields={'sample_id','task_id','prompt_sha256','policy_sha256','split','reward_stage','finish_reason',
                'measured_model_outcome','reward_eligible','reward','status','evidence'}
    for request,rollout,r in zip(packet['requests'],rollouts,reward['rows']):
        if (set(r)!=row_fields or any(r[k]!=request[k] for k in
            ('sample_id','task_id','prompt_sha256','policy_sha256','split','reward_stage')) or
            r['finish_reason']!=rollout.get('finish_reason',rollout['status']) or
            type(r['measured_model_outcome']) is not bool or type(r['reward_eligible']) is not bool or
            not isinstance(r['status'],str) or not isinstance(r['evidence'],dict)):
            raise ValueError('Ordered exact sample reward evidence required')
        measured=r['measured_model_outcome'] and r['reward_eligible']
        expected_reward={'pass':1,'model_sany_reject':0,'model_contract':0,'model_extraction':0}.get(r['status'])
        if expected_reward is not None and not measured:
            raise ValueError('Measured outcome status requires matching measured reward flags')
        if measured:
            if (expected_reward is None or r['finish_reason']!='eos' or type(r['reward']) not in (int,float)
                    or r['reward']!=expected_reward):
                raise ValueError('Only complete measured EOS samples can receive binary reward')
        elif r['reward'] is not None or r['measured_model_outcome'] or r['reward_eligible']:
            raise ValueError('Unknown/incomplete reward must remain null and ineligible')
    return reward


def teacher_logps(net,row,device,context_factory=nullcontext):
    """Full-sequence teacher-forcing control; production updates use cached_logps."""
    import torch
    ids=torch.tensor([row['input_token_ids']+row['token_ids']],dtype=torch.long,device=device)
    with context_factory():logits=net(input_ids=ids,attention_mask=torch.ones_like(ids),use_cache=False).logits
    start=len(row['input_token_ids'])-1
    scores=logits[0,start:start+len(row['token_ids'])].float()
    labels=torch.tensor(row['token_ids'],dtype=torch.long,device=device)
    return scores.log_softmax(-1).gather(1,labels[:,None]).reshape(-1)


def cached_logps(net,row,device,*,seconds,context_factory=nullcontext,clock=time.monotonic):
    """Replay exact sampler shapes with one per-response autocast cache scope."""
    import torch
    return cached_token_logps(net,torch.tensor(row['input_token_ids'],dtype=torch.long,device=device),
        torch.tensor(row['token_ids'],dtype=torch.long,device=device),eos_token_ids=EOS_IDS,
        seconds=seconds,context_factory=context_factory,clock=clock)


class LogprobDiscrepancyError(ValueError):
    def __init__(self,report):
        super().__init__('Sampled/replayed logprob discrepancy exceeds frozen .03/.003 limits')
        self.report=report


def failure_record(exc):
    record=dict(error=type(exc).__name__,reason=str(exc))
    if isinstance(exc,LogprobDiscrepancyError):record['logprob_discrepancy']=exc.report
    return record


def check_logps(actual,expected):
    import torch
    if actual.ndim!=1 or len(actual)!=len(expected) or not expected or not bool(torch.isfinite(actual).all()):
        raise ValueError('Finite matching sampled/teacher token logprobs required')
    old=torch.tensor(expected,dtype=actual.dtype,device=actual.device)
    if not bool(torch.isfinite(old).all()):raise ValueError('Nonfinite sampled logprob')
    differences=(actual.detach()-old).abs()
    worst=int(differences.argmax())
    report=dict(max_abs=float(differences.max()),mean_abs=float(differences.mean()),tokens=len(expected),
        worst_token_index=worst,sampled_at_worst=float(old[worst]),replayed_at_worst=float(actual.detach()[worst]),
        max_limit=.03,mean_limit=.003)
    if report['max_abs']>.03 or report['mean_abs']>.003:
        raise LogprobDiscrepancyError(report)
    return report


def assert_parent_unchanged(selected,initial):
    import torch
    if set(selected)!=set(initial) or any(not torch.equal(p.detach().cpu(),initial[n]) for n,p in selected.items()):
        raise ValueError('Frozen parent weights changed during sampling/reward phase')


def persist_generator_state(generator,path):
    import torch
    state=generator.get_state().cpu()
    if state.dtype!=torch.uint8 or state.ndim!=1:raise ValueError('Explicit byte-vector sampling RNG state required')
    torch.save(state,path)
    return file_sha(path)


def one_update(net,selected,rollouts,rewards,*,device,seconds=180,context_factory=nullcontext,
               guard=lambda:None,clock=time.monotonic):
    """Pure model/torch integration; caller saves checkpoint inside remaining180s."""
    import torch
    if len(rollouts)!=32 or len(rewards)!=32:raise ValueError('Exactly32 rollouts/rewards required')
    if not 60<seconds<=180:raise ValueError('Bounded update budget with60s checkpoint reserve required')
    started=clock();groups=[group_advantages(rewards[i:i+4]) for i in range(0,32,4)]
    eligible=[i for i,g in enumerate(groups) if g['eligible']]
    if not eligible:return dict(actual_updates=0,eligible_groups=0,groups=groups),None
    if not selected or any(p.dtype!=torch.float32 or not p.requires_grad for p in selected.values()):
        raise ValueError('Enabled float32 final-layer parameters required')
    def deadline():
        remaining=seconds-60-(clock()-started)
        if remaining<=0:raise TimeoutError('Update budget exhausted before checkpoint reserve')
        return remaining
    def score(row,phase):
        values=cached_logps(net,row,device,seconds=deadline(),context_factory=context_factory,clock=clock)
        try:report=check_logps(values,row['selected_token_logprobs'])
        except LogprobDiscrepancyError as exc:
            exc.report.update(sample_id=row['sample_id'],phase=phase,scoring=SCORING['method'])
            raise
        return values,report
    eos=[r for r in rollouts if r.get('finish_reason')=='eos']
    longest=max(eos,key=lambda r:len(r['input_token_ids'])+len(r['token_ids']))
    deadline()
    # Real longest EOS graph/backward before any optimizer is constructed.
    logits,preflight=score(longest,'longest_sequence_preflight')
    logits.sum().backward();guard();deadline()
    if any(p.grad is not None and not bool(torch.isfinite(p.grad).all()) for p in selected.values()):
        raise ValueError('Nonfinite preflight gradients')
    for p in selected.values():p.grad=None
    del logits
    optimizer=torch.optim.AdamW(selected.values(),lr=1e-6,weight_decay=0,foreach=False)
    optimizer.zero_grad(set_to_none=True);reports=[]
    for index in eligible:
        for sample in range(4):
            deadline();row=rollouts[4*index+sample]
            values,report=score(row,'eligible_group_update')
            reports.append(dict(sample_id=row['sample_id'],**report))
            loss=sample_reinforce_loss(values.sum(),groups[index],sample,eligible_groups=len(eligible))
            loss.backward();guard();deadline();del loss,values
    deadline()
    norm=torch.nn.utils.clip_grad_norm_(selected.values(),1.,error_if_nonfinite=True)
    if float(norm)<=0:raise ValueError('No nonzero aggregate policy gradient; no update')
    deadline()
    optimizer.step();guard()
    if any(not bool(torch.isfinite(p).all()) for p in selected.values()):raise ValueError('Nonfinite updated parameter')
    return dict(actual_updates=1,eligible_groups=len(eligible),groups=groups,gradient_norm=float(norm),
                scoring=dict(SCORING),longest_sequence_preflight=preflight,
                teacher_logprob_checks=reports,elapsed_seconds=clock()-started),optimizer


def run(a):
    import torch,transformers
    from tools.proof_cuda_train import load_policy,restore_policy,select_final_layer,autocast,save_reload
    from tools.proof_cuda_eval import encode_prompt,decode_reply
    started=time.monotonic();config=admit(a)
    a.output.mkdir(parents=True,exist_ok=False);dump(a.output/'config.json',config)
    (a.output/'requests.json').write_bytes(a.requests.read_bytes())
    packet=load_requests(a.requests.read_bytes(),REQUESTS_SHA,broader_raw=a.broader_prompts.read_bytes())
    os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
    random.seed(SEED);torch.set_num_threads(4);torch.manual_seed(SEED);torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats();net=load_policy(a.model_path)
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    if file_sha(a.checkpoint)!=POLICY_SHA:raise ValueError('Parent checkpoint changed during load')
    selected=restore_policy(net,saved,config['model_files'])
    if not all(torch.equal(p.detach().cpu(),saved['trainable_state'][n]) for n,p in selected.items()):
        raise ValueError('Exact immutable parent restore required')
    del saved
    initial={n:p.detach().cpu().clone() for n,p in selected.items()}
    if net.generation_config.eos_token_id!=EOS_IDS:raise ValueError('Actual model EOS changed')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    generator=torch.Generator(device='cuda').manual_seed(SEED);rollouts=[]
    config['sampling_generator_before_sha256']=persist_generator_state(generator,a.output/'sampling_generator_before.pt')
    dump(a.output/'config.json',config)
    def guard():
        memory_guard(torch.cuda.max_memory_allocated(),torch.cuda.max_memory_reserved())
        if source_hashes()!=config['implementation_sha256']:raise ValueError('Frozen runtime sources changed')
        if file_sha(a.requests)!=REQUESTS_SHA or file_sha(a.broader_prompts)!=BROADER_SHA:
            raise ValueError('Frozen request/input bytes changed')
    with (a.output/'rollouts.jsonl').open('x') as stream:
        for request in packet['requests']:
            remaining=1200-(time.monotonic()-started)
            row=dict(**request,request_sha256=digest(request))
            if remaining<=0:row.update(status='unattempted',reason='sampling_deadline_reserved_reward_exchange')
            else:
                task=next(t for t in packet['tasks'] if t['id']==request['task_id'])
                encoded=encode_prompt(tokenizer,task)
                if encoded!=config['encodings'][packet['tasks'].index(task)]:raise ValueError('Actual prompt encoding changed')
                answer=sample_tokens(net,torch.tensor(encoded['input_token_ids'],device='cuda'),generator=generator,
                    eos_token_ids=EOS_IDS,max_new_tokens=3072,seconds=remaining,context_factory=lambda:autocast('cuda'))
                row.update({k:encoded[k] for k in ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256')})
                row.update({k:v for k,v in answer.items() if k not in ('forward_calls','do_sample')})
                reply=decode_reply(tokenizer,row['token_ids'])
                row.update(token_ids_sha256=digest(row['token_ids']),raw_reply=reply,raw_reply_sha256=sha(reply.encode()),
                    status='generation_time_limit' if row['finish_reason']=='time_limit' else 'generated')
                guard()
            validate_rollout(request,row);rollouts.append(row);stream.write(json.dumps(row)+'\n');stream.flush()
    assert_parent_unchanged(selected,initial)
    config['sampling_generator_after_sha256']=persist_generator_state(generator,a.output/'sampling_generator_after.pt')
    dump(a.output/'config.json',config)
    validate_rollouts(packet,rollouts);rollouts_sha=file_sha(a.output/'rollouts.jsonl')
    dump(a.output/'rollouts_ready.json',dict(requests_sha256=REQUESTS_SHA,rollouts_sha256=rollouts_sha,rows=32,policy_sha256=POLICY_SHA))
    receipt_path=a.output/'rewards.receipt.json'
    while not receipt_path.exists():
        if time.monotonic()-started>=1500:
            dump(a.output/'summary.json',dict(actual_updates=0,reason='reward_mailbox_deadline',checkpoint_sha256=None,
                sampling_generator_before_sha256=config['sampling_generator_before_sha256'],
                sampling_generator_after_sha256=config['sampling_generator_after_sha256']));return
        time.sleep(.25)
    reward_raw=(a.output/'rewards.json').read_bytes();receipt=json.loads(receipt_path.read_bytes())
    rewards=validate_rewards(packet,rollouts,reward_raw,receipt,rollouts_sha256=rollouts_sha,
        bridge_source_sha256=config['implementation_sha256']['tools/proof_token_rl_rewards.py'])
    if time.monotonic()-started>=1500:raise TimeoutError('Reward receipt arrived outside sampling/reward budget')
    guard();assert_parent_unchanged(selected,initial)
    update_started=time.monotonic();selected=select_final_layer(net,train=True)
    if sum(p.numel() for p in selected.values())!=218112000:raise ValueError('Exact final-layer size required')
    result,optimizer=one_update(net,selected,rollouts,rewards['rows'],device='cuda',
        seconds=180-(time.monotonic()-update_started),context_factory=lambda:autocast('cuda'),guard=guard)
    if result['actual_updates']:
        config.update(reward_sha256=sha(reward_raw),rollouts_sha256=rollouts_sha,trainable_names=list(selected))
        dump(a.output/'config.json',config)
        probe=next(r for r in rollouts if r.get('finish_reason')=='eos')['input_token_ids']
        result.update(save_reload(net,selected,optimizer,initial,config,[result],probe,a.output/'policy_optimizer.pt','cuda'))
        guard()
        if result['parameter_delta_l2']<=0:raise ValueError('No actual parameter change')
        if time.monotonic()-update_started>180:raise TimeoutError('Update/checkpoint180s budget exceeded')
    else:result['checkpoint_sha256']=None
    result.update(requests_sha256=REQUESTS_SHA,rollouts_sha256=rollouts_sha,rewards_sha256=sha(reward_raw),
        sampling_generator_before_sha256=config['sampling_generator_before_sha256'],
        sampling_generator_after_sha256=config['sampling_generator_after_sha256'],
        reward_stage='sany_partial',cuda_peak_allocated=torch.cuda.max_memory_allocated(),cuda_peak_reserved=torch.cuda.max_memory_reserved())
    dump(a.output/'summary.json',result)


def validate_training(path,admission):
    """Read-only post-worker artifact audit for outer cycle; no model inference."""
    import torch
    path=Path(path)
    if (path/'failure.json').exists():raise ValueError('Worker failure is not a trained child')
    summary=json.loads((path/'summary.json').read_bytes());config=json.loads((path/'config.json').read_bytes())
    if any(config.get(k)!=v for k,v in admission.items()):raise ValueError('Worker admission changed')
    if summary.get('actual_updates') not in (0,1):raise ValueError('Only zero or one update allowed')
    memory_guard(summary.get('cuda_peak_allocated'),summary.get('cuda_peak_reserved'))
    for label in ('before','after'):
        name='sampling_generator_'+label
        if file_sha(path/(name+'.pt'))!=config.get(name+'_sha256') or summary.get(name+'_sha256')!=config.get(name+'_sha256'):
            raise ValueError('Sampling generator state artifact hash mismatch')
        state=torch.load(path/(name+'.pt'),map_location='cpu',weights_only=True)
        if not isinstance(state,torch.Tensor) or state.dtype!=torch.uint8 or state.ndim!=1 or not state.numel():
            raise ValueError('Sampling RNG byte-state required')
    if summary.get('requests_sha256')!=REQUESTS_SHA or file_sha(path/'rollouts.jsonl')!=summary.get('rollouts_sha256'):
        raise ValueError('Rollout byte identity changed')
    if file_sha(path/'rewards.json')!=summary.get('rewards_sha256'):raise ValueError('Reward bytes changed')
    receipt=json.loads((path/'rewards.receipt.json').read_text())
    packet=load_requests((path/'requests.json').read_bytes(),REQUESTS_SHA)
    rollouts=[json.loads(line) for line in (path/'rollouts.jsonl').read_text().splitlines()]
    rewards=validate_rewards(packet,rollouts,(path/'rewards.json').read_bytes(),receipt,
        rollouts_sha256=summary['rollouts_sha256'],bridge_source_sha256=admission['implementation_sha256']['tools/proof_token_rl_rewards.py'])
    groups=[group_advantages(rewards['rows'][i:i+4]) for i in range(0,32,4)]
    if summary.get('groups')!=groups or summary.get('eligible_groups')!=sum(g['eligible'] for g in groups):
        raise ValueError('Recorded objective group admissions changed')
    if (receipt.get('rewards_sha256')!=summary['rewards_sha256'] or receipt.get('rollouts_sha256')!=summary['rollouts_sha256'] or
        receipt.get('requests_sha256')!=REQUESTS_SHA or receipt.get('provenance_verified') is not True or
        receipt.get('bridge_source_sha256')!=admission['implementation_sha256']['tools/proof_token_rl_rewards.py']):
        raise ValueError('Receipt binding changed')
    if summary['actual_updates']==0:
        if summary.get('eligible_groups')!=0 or summary.get('checkpoint_sha256') is not None or (path/'policy_optimizer.pt').exists():
            raise ValueError('Zero eligible groups must not produce a child checkpoint')
    else:
        if (summary.get('eligible_groups',0)<1 or summary.get('reload_tensors_exact') is not True or
            summary.get('reload_logits_exact') is not True or summary.get('parameter_delta_l2',0)<=0 or
            file_sha(path/'policy_optimizer.pt')!=summary.get('checkpoint_sha256')):
            raise ValueError('Verified changed/reloaded one-update checkpoint required')
        saved=torch.load(path/'policy_optimizer.pt',map_location='cpu',weights_only=False)
        state=saved['trainable_state']
        if (set(state)!=set(config['trainable_names']) or len(state)!=9 or
            sum(v.numel() for v in state.values())!=218112000 or
            any(v.dtype!=torch.float32 or not bool(torch.isfinite(v).all()) for v in state.values()) or
            saved['config']!=config or not saved.get('optimizer',{}).get('state')):
            raise ValueError('Exact final-layer checkpoint state/optimizer required')
        for entry in saved['optimizer']['state'].values():
            if int(entry.get('step',0))!=1 or any(isinstance(v,torch.Tensor) and not bool(torch.isfinite(v).all()) for v in entry.values()):
                raise ValueError('Finite one-step optimizer state required')
    return summary


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('requests','broader-prompts','model-path','checkpoint','output'):parser.add_argument('--'+name,type=Path,required=True)
    a=parser.parse_args()
    try:run(a)
    except Exception as exc:
        if a.output.exists():dump(a.output/'failure.json',failure_record(exc))
        raise


if __name__=='__main__':main()
