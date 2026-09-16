"""Fixed CHILD TRAIN8/G4 stochastic diagnosis; no training or proof-success claim.

The parent request file stays immutable. Child requests are a distinct evaluation
contract, never passed off as admitted parent training requests. Parent comparison
requires a separate audit of the original baseline and is not performed here.
"""
import argparse
import copy
import json
import os
from pathlib import Path
import random
import sys
import time

CPU_ENV = {name: '4' for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS',
                                'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS')}
CPU_PROFILE = dict(environment=CPU_ENV, torch_num_threads=4)


def bound_cpu_environment():
    """Override inherited BLAS defaults before importing numerical libraries."""
    os.environ.update(CPU_ENV)


def cpu_runtime():
    bound_cpu_environment()
    import torch
    torch.set_num_threads(4)
    return check_cpu_runtime(torch)


def check_cpu_runtime(torch):
    actual = dict(environment={name: os.environ.get(name) for name in CPU_ENV},
                  torch_num_threads=torch.get_num_threads())
    if actual != CPU_PROFILE:
        raise ValueError('Frozen four-thread CPU runtime changed')
    return actual


# Also precede imports through the worker's transitive dependency graph.
bound_cpu_environment()
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_token_rl_worker as worker
from tools.proof_token_rl_packet import (load_requests, validate_requests,
    validate_rollout, digest, sha, canonical_bytes, POLICY_SHA, EOS_IDS, BROADER_SHA)
from tools.proof_cuda_train import file_sha, dump

CHILD_SHA = 'f41f4a147b0fbc4cbd62ba87403d76516b4cd9da96fcc577979b033fa96b1a91'
SOURCES = tuple(dict.fromkeys(('tools/proof_token_rl_policy_eval.py',) + worker.SOURCES))
SCOPE = 'Reused TRAIN8, same training seed; in-sample partial-SANY diagnosis, not unseen generalization'


def source_hashes():
    return {name: file_sha(ROOT/name) for name in SOURCES}


def derive_requests(parent):
    validate_requests(parent)
    if parent['reward_stage'] != 'sany_partial':
        raise ValueError('Partial SANY parent experiment required')
    return dict(schema=1, kind='frozen_child_policy_evaluation',
        parent_requests_sha256=worker.REQUESTS_SHA, parent_policy_sha256=POLICY_SHA,
        policy_sha256=CHILD_SHA, seed=worker.SEED, sampling_seconds=1200,
        max_optimizer_updates=0, scope=SCOPE, tasks=copy.deepcopy(parent['tasks']),
        requests=[dict(r, policy_sha256=CHILD_SHA) for r in parent['requests']])


def validate_rows(evaluation, rows):
    if not isinstance(rows, list) or len(rows) != 32:
        raise ValueError('Full32 ordered evaluation accounting required')
    return [validate_rollout(request, row)
            for request, row in zip(evaluation['requests'], rows)]


def check_checkpoint(saved, files):
    import torch
    from tools.proof_cuda_train import PROFILE
    config = saved['config']; state = saved['trainable_state']
    if (config.get('model_files') != files or config.get('dtype_profile') != PROFILE or
            config.get('policy_sha256') != POLICY_SHA or
            config.get('requests_sha256') != worker.REQUESTS_SHA or
            config.get('reward_stage') != 'sany_partial' or
            set(state) != set(config.get('trainable_names', [])) or len(state) != 9 or
            sum(v.numel() for v in state.values()) != 218112000 or
            any(v.dtype != torch.float32 or not bool(torch.isfinite(v).all()) for v in state.values())):
        raise ValueError('Exact finite one-update child configuration/state required')
    optimizer = saved.get('optimizer', {}).get('state', {})
    if len(optimizer) != 9 or any(int(v.get('step', 0)) != 1 for v in optimizer.values()):
        raise ValueError('Child must originate from exactly one recorded update')
    return digest(config)


def admit(a):
    """Full production CPU admission; no CUDA model load or output writes."""
    cpu_profile = cpu_runtime()
    import torch
    import transformers
    from tools.proof_cuda_train import model_files, PROFILE
    from tools.proof_cuda_eval import encode_prompt
    for value in (a.requests, a.broader_prompts, a.model_path, a.checkpoint):
        output, source = a.output.resolve(), value.resolve()
        if output == source or output in source.parents or source in output.parents:
            raise ValueError('Output must be isolated from immutable inputs')
    parent = load_requests(a.requests.read_bytes(), worker.REQUESTS_SHA,
                           broader_raw=a.broader_prompts.read_bytes())
    evaluation = derive_requests(parent)
    if file_sha(a.checkpoint) != CHILD_SHA:
        raise ValueError('Exact frozen child checkpoint required')
    versions = dict(torch_version=torch.__version__, transformers_version=transformers.__version__)
    files = model_files(a.model_path)
    if versions != worker.VERSIONS or digest(files) != worker.MODEL_SHA:
        raise ValueError('Pinned model and runtime required')
    if json.loads((a.model_path/'generation_config.json').read_text())['eos_token_id'] != EOS_IDS:
        raise ValueError('Pinned EOS configuration required')
    saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    checkpoint_config_sha = check_checkpoint(saved, files)
    if file_sha(a.checkpoint) != CHILD_SHA:
        raise ValueError('Checkpoint changed during admission')
    del saved
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    encodings = [encode_prompt(tokenizer, t) for t in evaluation['tasks']]
    if any(e['input_tokens'] + 3072 > 8192 for e in encodings):
        raise ValueError('Full untruncated context required')
    return dict(schema=1, evaluation=evaluation, evaluation_sha256=digest(evaluation),
        checkpoint_sha256=CHILD_SHA, checkpoint_config_sha256=checkpoint_config_sha,
        broader_prompts_sha256=BROADER_SHA, model_files=files, dtype_profile=PROFILE,
        implementation_sha256=source_hashes(), encodings=encodings, **versions,
        requested_samples=32, temperature=1., max_new_tokens=3072, max_context=8192,
        sampling_seconds=1200, seed=worker.SEED, optimizer_updates=0, scope=SCOPE,
        cuda_memory_limit_bytes=worker.MEMORY_LIMIT,
        cpu_thread_profile=cpu_profile,
        proof_success_claim=False, generalization_claim=False)


def generate(a):
    cpu_runtime()
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, restore_policy, autocast
    from tools.proof_cuda_eval import encode_prompt, decode_reply
    from tools.proof_token_rl_sampling import sample_tokens
    started = time.monotonic()  # Parent worker includes admission and loading.
    config = admit(a)
    if getattr(a,'admission',None) is None:
        raise ValueError('Previously frozen full CPU admission file required')
    admission_raw = a.admission.read_bytes()
    admission_sha = sha(admission_raw)
    if json.loads(admission_raw) != config:
        raise ValueError('Production admission differs from frozen full CPU admission')
    output, admission_path = a.output.resolve(), a.admission.resolve()
    if output == admission_path or output in admission_path.parents or admission_path in output.parents:
        raise ValueError('Output must be isolated from frozen admission')
    config['admission_sha256'] = admission_sha
    a.output.mkdir(parents=True, exist_ok=False)
    (a.output/'admission.json').write_bytes(admission_raw)
    dump(a.output/'config.json', config)
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    random.seed(worker.SEED); torch.set_num_threads(4); torch.manual_seed(worker.SEED)
    torch.backends.cuda.matmul.allow_tf32 = False
    torch.cuda.reset_peak_memory_stats()
    net = load_policy(a.model_path)
    config['hardware'] = dict(device=torch.cuda.get_device_name(),
        capability=list(torch.cuda.get_device_capability()),
        total_memory=torch.cuda.get_device_properties(torch.cuda.current_device()).total_memory)
    dump(a.output/'config.json', config)
    saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    check_checkpoint(saved, config['model_files'])
    selected = restore_policy(net, saved, config['model_files'])
    if any(not torch.equal(p.detach().cpu(), saved['trainable_state'][n]) for n,p in selected.items()):
        raise ValueError('Exact child restore required')
    del saved
    if any(p.requires_grad for p in net.parameters()) or net.generation_config.eos_token_id != EOS_IDS:
        raise ValueError('Frozen inference model and EOS required')
    initial = {n:p.detach().cpu().clone() for n,p in selected.items()}
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    generator = torch.Generator(device='cuda').manual_seed(worker.SEED)
    rng = dict(before=worker.persist_generator_state(generator, a.output/'sampling_generator_before.pt'))
    rows = []; failure = None
    with (a.output/'rollouts.jsonl').open('x') as stream:
        for request in config['evaluation']['requests']:
            remaining = 1200 - (time.monotonic()-started)
            row = dict(request, request_sha256=digest(request))
            if failure or remaining <= 0:
                row.update(status='unattempted', reason=failure or 'fixed_sampling_deadline')
            else:
                try:
                    index = next(i for i,t in enumerate(config['evaluation']['tasks']) if t['id']==request['task_id'])
                    encoded = encode_prompt(tokenizer, config['evaluation']['tasks'][index])
                    if encoded != config['encodings'][index]:
                        raise ValueError('Frozen prompt encoding changed')
                    answer = sample_tokens(net, torch.tensor(encoded['input_token_ids'], device='cuda'),
                        generator=generator, eos_token_ids=EOS_IDS, max_new_tokens=3072,
                        seconds=remaining, context_factory=lambda:autocast('cuda'))
                    row.update({k:encoded[k] for k in ('input_token_ids','input_token_ids_sha256',
                        'input_tokens','rendered_prompt','rendered_prompt_sha256')})
                    row.update({k:v for k,v in answer.items() if k not in ('forward_calls','do_sample')})
                    reply = decode_reply(tokenizer, row['token_ids'])
                    row.update(token_ids_sha256=digest(row['token_ids']), raw_reply=reply,
                        raw_reply_sha256=sha(reply.encode()), status='generation_time_limit'
                        if row['finish_reason']=='time_limit' else 'generated')
                    worker.memory_guard(torch.cuda.max_memory_allocated(), torch.cuda.max_memory_reserved())
                except Exception as exc:
                    failure = type(exc).__name__+': '+str(exc)
                    if row.get('status') not in ('generated','generation_time_limit'):
                        row = dict(request, request_sha256=digest(request), status='worker_error', reason=failure)
            validate_rollout(request, row); rows.append(row)
            stream.write(json.dumps(row)+'\n'); stream.flush()
    worker.assert_parent_unchanged(selected, initial)
    rng['after'] = worker.persist_generator_state(generator, a.output/'sampling_generator_after.pt')
    validate_rows(config['evaluation'], rows)
    check_cpu_runtime(torch)
    if (source_hashes()!=config['implementation_sha256'] or file_sha(a.checkpoint)!=CHILD_SHA or
            file_sha(a.requests)!=worker.REQUESTS_SHA or file_sha(a.broader_prompts)!=BROADER_SHA or
            sha(a.admission.read_bytes())!=admission_sha or
            sha((a.output/'admission.json').read_bytes())!=admission_sha):
        raise ValueError('Frozen inputs/source changed during generation')
    summary = dict(complete=failure is None, failure=failure, requested_samples=32, accounted_samples=32,
        rollouts_sha256=file_sha(a.output/'rollouts.jsonl'), config_sha256=file_sha(a.output/'config.json'),
        sampling_generator_sha256=rng, checkpoint_sha256=CHILD_SHA, optimizer_updates=0,
        frozen_weights_verified=True, scope=SCOPE, verification_pending=True,
        cuda_peak_allocated=torch.cuda.max_memory_allocated(), cuda_peak_reserved=torch.cuda.max_memory_reserved())
    dump(a.output/'summary.json', summary)
    if failure: raise RuntimeError(failure)
    return summary


def verify(a):
    """Independently reconstruct local tokenizer and run/audit current SANY."""
    cpu_profile = cpu_runtime()
    import torch
    from tools import proof_token_rl_rewards as bridge
    from tools.proof_cuda_eval import encode_prompt, decode_reply
    from tools.proof_cuda_train import PROFILE
    parent, tasks, tokenizer = bridge.prepare(a.requests)
    evaluation = derive_requests(parent)
    config = json.loads((a.generation/'config.json').read_bytes())
    admission_raw = (a.generation/'admission.json').read_bytes()
    admission = json.loads(admission_raw)
    if (config.get('admission_sha256') != sha(admission_raw) or
            {k:v for k,v in config.items() if k not in ('admission_sha256','hardware')} != admission):
        raise ValueError('Exact frozen CPU admission artifact required')
    summary = json.loads((a.generation/'summary.json').read_bytes())
    raw = (a.generation/'rollouts.jsonl').read_bytes()
    if file_sha(a.checkpoint) != CHILD_SHA:
        raise ValueError('Collected exact child checkpoint required for local verification')
    saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    checkpoint_config_sha = check_checkpoint(saved, config['model_files'])
    del saved
    if (config.get('evaluation') != evaluation or config.get('evaluation_sha256') != digest(evaluation) or
            config.get('implementation_sha256') != source_hashes() or
            config.get('checkpoint_sha256') != CHILD_SHA or config.get('optimizer_updates') != 0 or
            config.get('checkpoint_config_sha256') != checkpoint_config_sha or
            digest(config.get('model_files')) != worker.MODEL_SHA or
            any(config.get(k) != v for k,v in worker.VERSIONS.items()) or
            config.get('temperature') != 1. or config.get('max_new_tokens') != 3072 or
            config.get('max_context') != 8192 or
            config.get('requested_samples') != 32 or config.get('broader_prompts_sha256') != BROADER_SHA or
            config.get('dtype_profile') != PROFILE or config.get('scope') != SCOPE or
            config.get('proof_success_claim') is not False or config.get('generalization_claim') is not False or
            config.get('cuda_memory_limit_bytes') != worker.MEMORY_LIMIT or
            config.get('cpu_thread_profile') != cpu_profile or
            summary.get('checkpoint_sha256') != CHILD_SHA or
            summary.get('requested_samples') != 32 or summary.get('accounted_samples') != 32 or
            type(summary.get('complete')) is not bool or
            (summary.get('complete') is True and summary.get('failure') is not None) or
            (summary.get('complete') is False and (not isinstance(summary.get('failure'),str) or not summary['failure'])) or
            config.get('seed') != worker.SEED or config.get('sampling_seconds') != 1200 or
            summary.get('rollouts_sha256') != sha(raw) or
            summary.get('config_sha256') != file_sha(a.generation/'config.json') or
            summary.get('frozen_weights_verified') is not True or summary.get('optimizer_updates') != 0):
        raise ValueError('Frozen child generation provenance required')
    worker.memory_guard(summary.get('cuda_peak_allocated'),summary.get('cuda_peak_reserved'))
    expected_encodings = [encode_prompt(tokenizer,t) for t in evaluation['tasks']]
    if config.get('encodings') != expected_encodings:
        raise ValueError('Frozen admission prompt encodings changed')
    for label in ('before','after'):
        path = a.generation/('sampling_generator_'+label+'.pt')
        if file_sha(path) != summary['sampling_generator_sha256'][label]:
            raise ValueError('Sampling RNG artifact changed')
        state = torch.load(path, map_location='cpu', weights_only=True)
        if not isinstance(state,torch.Tensor) or state.dtype!=torch.uint8 or state.ndim!=1 or not state.numel():
            raise ValueError('Actual sampling RNG byte state required')
    rows = [json.loads(line) for line in raw.splitlines()]
    validate_rows(evaluation, rows)
    before = bridge.identity(tasks)
    bridge.admit_controls(a.controls, parent, tasks, before)
    a.output.mkdir(parents=True, exist_ok=False)
    dump(a.output/'identity_before.json', before); results=[]; started=time.monotonic()
    for request,row in zip(evaluation['requests'],rows):
        result = dict(sample_id=request['sample_id'], task_id=request['task_id'], status='unmeasured_generation',
            sany=None, finish_reason=row.get('finish_reason',row['status']), evidence={})
        if row['status'] in ('generated','generation_time_limit'):
            prompt = next(t for t in evaluation['tasks'] if t['id']==request['task_id'])
            encoded = encode_prompt(tokenizer,prompt)
            for key in ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256'):
                if row[key]!=encoded[key]: raise ValueError('Exact prompt tokenization mismatch: '+key)
            if decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Exact output decoding mismatch')
            if row['finish_reason']=='eos':
                task=tasks[request['task_id']]; extraction=bridge.extract(row['raw_reply'],task)
                result['evidence']['extraction']=extraction
                remaining=1000-(time.monotonic()-started)
                if extraction.get('fragment') is None:
                    result.update(status='model_extraction',sany=False)
                elif remaining<=0: result['status']='unmeasured_budget'
                else:
                    verdict=bridge.check(task,extraction['fragment'],a.output/'checks'/request['sample_id'],timeout=min(30,remaining))
                    bridge.audit_check(task,extraction['fragment'],verdict,before)
                    result.update(status=verdict['status'],sany=None if verdict['reward'] is None else bool(verdict['reward']))
                    result['evidence']['sany']=verdict
        results.append(result); dump(a.output/'rows.json',results)
    after=bridge.identity(tasks); dump(a.output/'identity_after.json',after)
    check_cpu_runtime(torch)
    if before!=after or source_hashes()!=config['implementation_sha256']:
        raise ValueError('SANY or evaluation runtime changed during assessment')
    result=dict(requested_samples=32, accounted_samples=len(results),
        sany_passes=sum(r['sany'] is True for r in results),
        measured_rejections=sum(r['sany'] is False for r in results),
        unmeasured=sum(r['sany'] is None for r in results),
        distinct_outputs=len({r['raw_reply'] for r in rows if 'raw_reply' in r}),
        rows_sha256=file_sha(a.output/'rows.json'),generation_sha256=sha(raw),
        checkpoint_sha256=CHILD_SHA,scope=SCOPE,partial_sany_only=True,
        proof_success_claim=False,generalization_claim=False,baseline_comparison_performed=False)
    result['generation_complete'] = summary.get('complete') is True
    result['generation_failure'] = summary.get('failure')
    dump(a.output/'summary.json',result)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('generate','verify'))
    for name in ('requests','output'): parser.add_argument('--'+name,type=Path,required=True)
    for name in ('broader-prompts','model-path','checkpoint','generation','controls','admission'):
        parser.add_argument('--'+name,type=Path)
    parser.add_argument('--admit-only',action='store_true')
    args=parser.parse_args()
    required=('broader_prompts','model_path','checkpoint') if args.mode=='generate' else ('generation','controls','checkpoint')
    if any(getattr(args,k) is None for k in required): parser.error('Missing arguments: '+', '.join(required))
    if args.admit_only and args.mode!='generate': parser.error('--admit-only is generation admission')
    if args.mode=='generate' and not args.admit_only and args.admission is None:
        parser.error('--admission is required for actual generation')
    result=admit(args) if args.admit_only else generate(args) if args.mode=='generate' else verify(args)
    print(json.dumps(result))


if __name__=='__main__': main()
