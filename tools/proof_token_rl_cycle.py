#!/usr/bin/env python3
"""One bounded token-policy update plus complete broader retention accounting.

CPU admission is exactly the pre-submission --admit-only path. This driver does
not assign rewards, run proof checkers, or infer proof/learning success.
"""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_cuda_broader_eval as probe
from tools.proof_token_rl_packet import load_requests,validate_rollouts,POLICY_SHA,BROADER_SHA
from tools.proof_cuda_train import file_sha
from tools.proof_cuda_cycle import run_processes,dump

REQUESTS_SHA='fa56d5234e710ec646ab4ba2fc3e5771dc699780ea4f05a4da3763fdafb7ebf5'
MODEL=Path('/grand/EVITA/eric-spencer/hf-cache/hub/models--meta-llama--Llama-3.1-8B-Instruct/snapshots/0e9e39f249a16976918f6564b8830bc894c89659')
WORKER_SECONDS=1700
RETENTION_SECONDS=1220
TOTAL_SECONDS=3300
SOURCES=('tools/proof_token_rl_cycle.py','tools/proof_token_rl_cycle.pbs','tools/proof_cuda_cycle.py',
         'tools/proof_token_rl_packet.py','tools/proof_token_rl_sampling.py','tools/proof_token_rl_objective.py')


def worker_module():
    from tools import proof_token_rl_worker
    return proof_token_rl_worker


def freeze(requests,broader_prompts,model_path,checkpoint,output):
    """Read-only production admission; no CUDA model construction or output writes."""
    requests=Path(requests);broader_prompts=Path(broader_prompts);model_path=Path(model_path);checkpoint=Path(checkpoint)
    if model_path.resolve(strict=True)!=MODEL.resolve(strict=True):raise ValueError('Pinned model snapshot path required')
    if file_sha(checkpoint)!=POLICY_SHA:raise ValueError('Immutable exposure512 parent checkpoint required')
    broader_raw=broader_prompts.read_bytes()
    packet=load_requests(requests.read_bytes(),REQUESTS_SHA,broader_raw=broader_raw)
    admission=probe.admit(broader_prompts,BROADER_SHA,model_path,checkpoint)
    if admission['checkpoint_sha256']!=POLICY_SHA or len(admission['requested_task_ids'])!=36:
        raise ValueError('Exact36 retention admission and parent required')
    worker=worker_module()
    worker_admission=worker.admit(SimpleNamespace(requests=requests,broader_prompts=broader_prompts,
        model_path=model_path,checkpoint=checkpoint,output=Path(output)/'training'))
    sources=sorted(set(SOURCES)|set(probe.IMPLEMENTATION)|set(worker.SOURCES))
    return dict(requests_sha256=REQUESTS_SHA,broader_prompts_sha256=BROADER_SHA,parent_checkpoint_sha256=POLICY_SHA,
        retention_admission=admission,worker_admission=worker_admission,requested_rollouts=32,
        requested_retention_tasks=36,request_keys=packet['requests'],
        implementation_sha256={name:file_sha(ROOT/name) for name in sources})


def check_training(path,frozen,requests):
    """Worker-owned policy/reward/checkpoint validation plus independent accounting."""
    from tools.proof_cuda_eval import read_rows
    worker=worker_module()
    summary=worker.validate_training(path,frozen['worker_admission'])
    rows=read_rows(path/'rollouts.jsonl')
    accounting=validate_rollouts(requests,rows,complete_accounting=True)
    if accounting['accounted_samples']!=32:raise ValueError('All32 sampled or explicitly unmeasured outcomes required')
    updates=summary.get('actual_updates')
    if type(updates) is not int or updates not in (0,1):raise ValueError('At most one actual optimizer update allowed')
    if updates==0:
        if summary.get('eligible_groups')!=0 or summary.get('checkpoint_sha256') is not None:
            raise ValueError('Zero-update completion requires explicit zero eligibility and no child')
    elif file_sha(path/'policy_optimizer.pt')!=summary.get('checkpoint_sha256'):
        raise ValueError('Child checkpoint bytes differ from validated worker result')
    return dict(summary=summary,rollout_accounting=accounting)


def check_retention(path,prompts,frozen,checkpoint):
    from transformers import AutoTokenizer
    from tools.proof_cuda_eval import read_rows,validate_tokenization,decode_reply
    raw=Path(prompts).read_bytes();config=json.loads((path/'config.json').read_bytes())
    rows=read_rows(path/'generations.jsonl');summary=json.loads((path/'summary.json').read_bytes())
    expected=probe.admit(prompts,BROADER_SHA,MODEL,checkpoint)
    if any(config.get(k)!=v for k,v in expected.items() if k!='restore_exact'):
        raise ValueError('Retention differs from exact admitted checkpoint/model/input/runtime')
    if {k:expected[k] for k in ('model_files','input_evidence','requested_task_ids')}!={
            k:frozen['retention_admission'][k] for k in ('model_files','input_evidence','requested_task_ids')}:
        raise ValueError('Retention input/model changed from parent admission')
    tasks=probe.validate_run(raw,config,rows,summary)
    if summary.get('returncode')!=0 or summary.get('termination')!='complete' or len(rows)!=36:
        raise ValueError('Full32 TRAIN plus four DEV retention accounting required')
    tokenizer=AutoTokenizer.from_pretrained(MODEL,local_files_only=True)
    for task,row in zip(tasks,rows):
        validate_tokenization(tokenizer,task,row)
        if decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:raise ValueError('Exact raw retention output reconstruction required')
    return dict(requested_tasks=36,accounted_tasks=36,train_tasks=32,development_tasks=4,
        generated_tasks=sum(r['status']=='generated' for r in rows),
        unmeasured_time_limits=sum(r['status']=='generation_time_limit' for r in rows),
        checkpoint_sha256=expected['checkpoint_sha256'],verification_pending=True,
        files_sha256={name:file_sha(path/name) for name in ('config.json','generations.jsonl','summary.json')})


def execute(output,requests,broader_prompts,model_path,checkpoint,frozen,*,clock=time.monotonic):
    output=Path(output);started=clock();training=output/'training';retention=output/'retention'
    def guard():
        if freeze(requests,broader_prompts,model_path,checkpoint,output)!=frozen:
            raise ValueError('Frozen code/model/input/parent changed')
    def remaining(limit):
        left=TOTAL_SECONDS-(clock()-started)
        if left<=0:raise TimeoutError('Overall3300-second cycle deadline exhausted')
        return min(limit,left)
    worker_command=[sys.executable,str(ROOT/'tools/proof_token_rl_worker.py'),
        '--requests',str(requests),'--broader-prompts',str(broader_prompts),'--model-path',str(model_path),
        '--checkpoint',str(checkpoint),'--output',str(training)]
    failure=None;trained=None;selected=checkpoint
    try:
        run_processes([worker_command],[output/'training.log'],remaining(WORKER_SECONDS))
        guard()
        packet=load_requests(Path(requests).read_bytes(),REQUESTS_SHA,broader_raw=Path(broader_prompts).read_bytes())
        trained=check_training(training,frozen,packet)
        if trained['summary']['actual_updates']==1:selected=training/'policy_optimizer.pt'
    except Exception as exc:
        failure=repr(exc)
        dump(output/'training_failure.json',dict(error=failure,retention_policy='immutable parent diagnostic',
             learning_success_claim=False,zero_eligibility_claim=False))
    # A failed worker does not become a zero-update success. The parent probe is
    # still useful and is explicitly labelled diagnostic; no failed child loads.
    guard()
    selected_sha=trained['summary']['checkpoint_sha256'] if trained and trained['summary']['actual_updates']==1 else POLICY_SHA
    if file_sha(Path(selected))!=selected_sha:raise ValueError('Selected retention checkpoint changed after training audit')
    command=[sys.executable,str(ROOT/'tools/proof_cuda_broader_eval.py'),'generate',
        '--prompts',str(broader_prompts),'--expected-input-sha256',BROADER_SHA,
        '--model-path',str(model_path),'--checkpoint',str(selected),'--output',str(retention)]
    run_processes([command],[output/'retention.log'],remaining(RETENTION_SECONDS))
    guard();measured=check_retention(retention,broader_prompts,frozen,selected)
    if file_sha(Path(selected))!=selected_sha:raise ValueError('Selected retention checkpoint changed during retention')
    remaining(0)  # Never accept a complete result after the outer deadline.
    result=dict(status='worker_failed_parent_retention_complete' if failure else 'token_rl_and_retention_accounted',
        training=trained,training_failure=failure,retention=measured,elapsed_seconds=clock()-started,
        reward_stage='sany_partial',proof_success_claim=False,learning_improvement_claim=False,
        strict_proof_verification_pending=True)
    dump(output/'summary.json',result)
    if failure:raise RuntimeError('Worker failed; parent retention preserved: '+failure)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('requests','broader-prompts','model-path','checkpoint','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--admit-only',action='store_true');args=parser.parse_args()
    args.output=args.output.resolve()
    for value in (args.requests,args.broader_prompts,args.model_path,args.checkpoint):
        path=value.resolve(strict=True)
        if path==args.output or path in args.output.parents or args.output in path.parents:
            raise ValueError('Output must be isolated from immutable inputs')
    frozen=freeze(args.requests,args.broader_prompts,args.model_path,args.checkpoint,args.output)
    if args.admit_only:
        print(json.dumps(frozen));return
    args.output.mkdir(parents=True,exist_ok=False)
    dump(args.output/'config.json',dict(frozen=frozen,
        hypothesis='One on-policy token REINFORCE update with independently verified SANY partial rewards changes retention',
        budget=dict(worker_seconds=1700,retention_seconds=1200,total_seconds=3300),
        requests=32,max_optimizer_updates=1,retention_tasks=36,
        rewards_path=str(args.output/'training'/'rewards.json'),
        checkpoint_policy='Verified one-update child, else immutable parent; no warm optimizer resume',
        semantic_scope='SANY partial reward is not proof success; no benchmark/fresh evaluation answers in training'))
    try:execute(args.output,args.requests,args.broader_prompts,args.model_path,args.checkpoint,frozen)
    except BaseException as exc:
        dump(args.output/'failure.json',dict(error=repr(exc),proof_success_claim=False,learning_improvement_claim=False));raise


if __name__=='__main__':main()
