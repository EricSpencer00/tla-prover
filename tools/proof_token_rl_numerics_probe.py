"""No-update CUDA diagnosis of the frozen v2 sampled/teacher scoring mismatch.

Replays recorded TRAIN tokens, never resamples or delivers new rewards. Existing
logprob tolerances and 36GiB guard remain unchanged. This is not training.
"""
import argparse
from contextlib import nullcontext
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_token_rl_cycle as cycle
from tools import proof_token_rl_worker as worker
from tools.proof_token_rl_packet import load_requests,validate_rollouts
from tools.proof_cuda_train import dump,file_sha

ROLLOUT_SHA='d072cf0b56c86675e5e84017f3767599e31563923b0ccb6401f3842b0335625a'
REWARD_SHA='4e25747c62bbdabb47c4a90e996a84263324c4c73627e0e6ae1124e1b0923dec'
EXTRA_SOURCES=('tools/proof_token_rl_numerics_probe.py','tools/proof_token_rl_cached_score.py',
               'tools/proof_token_rl_numerics_probe.pbs')


def select_rows(rows,rewards):
    """Frozen selection: longest complete sequence, then every eligible sample."""
    if len(rows)!=32 or len(rewards)!=32:raise ValueError('Full32 accounting required')
    eos=[r for r in rows if r.get('finish_reason')=='eos']
    if not eos:raise ValueError('A complete sampled response is required')
    selected=[max(eos,key=lambda r:len(r['input_token_ids'])+len(r['token_ids']))]
    groups=[worker.group_advantages(rewards[i:i+4]) for i in range(0,32,4)]
    for i,g in enumerate(groups):
        if g['eligible']:
            selected.extend(r for r in rows[i*4:i*4+4] if r['sample_id'] not in {s['sample_id'] for s in selected})
    return selected


def compare(actual,expected):
    import torch
    if actual.ndim!=1 or len(actual)!=len(expected) or not expected or not bool(torch.isfinite(actual).all()):
        raise ValueError('Finite matching token logprobs required')
    reference=torch.tensor(expected,device=actual.device,dtype=actual.dtype)
    if not bool(torch.isfinite(reference).all()):raise ValueError('Finite sampled logprobs required')
    delta=(actual.detach()-reference).abs()
    result=dict(tokens=len(expected),max_abs=float(delta.max()),mean_abs=float(delta.mean()),
        worst_token_index=int(delta.argmax()),bitwise_equal=torch.equal(actual.detach(),reference))
    result['within_frozen_tolerance']=result['max_abs']<=.03 and result['mean_abs']<=.003
    return result


def admit(a):
    frozen=cycle.freeze(a.requests,a.broader_prompts,a.model_path,a.checkpoint,a.output)
    for p in (a.rollouts,a.reward_file,a.receipt):
        p=p.resolve(strict=True);out=a.output.resolve()
        if p==out or p in out.parents or out in p.parents:raise ValueError('Isolated diagnostic output required')
    if file_sha(a.rollouts)!=ROLLOUT_SHA or file_sha(a.reward_file)!=REWARD_SHA:
        raise ValueError('Exact v2 rollout and reward bytes required')
    rows=[json.loads(l) for l in a.rollouts.read_bytes().splitlines()]
    packet=load_requests(a.requests.read_bytes(),worker.REQUESTS_SHA,broader_raw=a.broader_prompts.read_bytes())
    validate_rollouts(packet,rows)
    reward=worker.validate_rewards(packet,rows,a.reward_file.read_bytes(),json.loads(a.receipt.read_bytes()),
        rollouts_sha256=ROLLOUT_SHA,bridge_source_sha256=frozen['implementation_sha256']['tools/proof_token_rl_rewards.py'])
    selected=select_rows(rows,reward['rows'])
    return dict(frozen=frozen,rollouts_sha256=ROLLOUT_SHA,rewards_sha256=REWARD_SHA,
        receipt_sha256=file_sha(a.receipt),selected_sample_ids=[r['sample_id'] for r in selected],
        extra_sources={n:file_sha(ROOT/n) for n in EXTRA_SOURCES},
        hypothesis='Incremental cached gradient replay matches the sampled distribution where full-sequence BF16 scoring differs',
        seconds=900,optimizer_steps=0,checkpoint_writes=0,memory_limit=worker.MEMORY_LIMIT),selected


def run(a,frozen,rows):
    import torch
    from tools.proof_cuda_train import load_policy,restore_policy,select_final_layer,autocast
    from tools.proof_token_rl_cached_score import cached_token_logps
    a.output.mkdir(parents=True,exist_ok=False);dump(a.output/'config.json',frozen)
    started=time.monotonic();results=[]
    torch.set_num_threads(4);torch.manual_seed(worker.SEED);torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats()
    def guard():
        if time.monotonic()-started>=900:raise TimeoutError('Diagnostic900s budget exhausted')
        worker.memory_guard(torch.cuda.max_memory_allocated(),torch.cuda.max_memory_reserved())
    try:
        net=load_policy(a.model_path)
        saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
        selected=restore_policy(net,saved,frozen['frozen']['worker_admission']['model_files'])
        initial={n:v.detach().cpu().clone() for n,v in selected.items()};del saved
        selected=select_final_layer(net,train=True)
        for row in rows:
            guard();report=dict(sample_id=row['sample_id'],input_tokens=len(row['input_token_ids']),
                output_tokens=len(row['token_ids']),paths={})
            results.append(report)
            for mode in ('full_no_grad','cached_no_grad','cached_grad'):
                guard();t0=time.monotonic()
                for parameter in selected.values():parameter.grad=None
                with torch.no_grad() if mode!='cached_grad' else nullcontext():
                    if mode=='full_no_grad':values=worker.teacher_logps(net,row,'cuda',lambda:autocast('cuda'))
                    else:
                        values=cached_token_logps(net,torch.tensor(row['input_token_ids'],device='cuda'),
                            torch.tensor(row['token_ids'],device='cuda'),eos_token_ids=worker.EOS_IDS,
                            seconds=900-(time.monotonic()-started),context_factory=lambda:autocast('cuda'))
                detail=compare(values,row['selected_token_logprobs']);report['paths'][mode]=detail
                dump(a.output/'rows.json',results)
                if mode=='cached_grad':
                    values.sum().backward()
                    detail['gradient_norms']={n:float(p.grad.norm()) if p.grad is not None else None for n,p in selected.items()}
                    if any(p.grad is None or not bool(torch.isfinite(p.grad).all()) for p in selected.values()):
                        raise ValueError('Missing or nonfinite cached-score gradient')
                del values
                for parameter in selected.values():parameter.grad=None
                detail.update(seconds=time.monotonic()-t0,peak_allocated=torch.cuda.max_memory_allocated(),
                    peak_reserved=torch.cuda.max_memory_reserved())
                guard();dump(a.output/'rows.json',results)
        worker.assert_parent_unchanged(selected,initial)
        if admit(a)[0]!=frozen:raise ValueError('Frozen diagnostic identity changed')
        guard()
        dump(a.output/'summary.json',dict(complete=True,rows=len(results),optimizer_steps=0,
            parent_unchanged=True,elapsed_seconds=time.monotonic()-started,
            cached_grad_all_within_tolerance=all(r['paths']['cached_grad']['within_frozen_tolerance'] for r in results),
            proof_success_claim=False,learning_improvement_claim=False))
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__,reason=str(exc),optimizer_steps=0));raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('requests','broader-prompts','model-path','checkpoint','rollouts','reward-file','receipt','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--admit-only',action='store_true');a=parser.parse_args()
    frozen,rows=admit(a)
    if a.admit_only:print(json.dumps(frozen));return
    run(a,frozen,rows)


if __name__=='__main__':main()
