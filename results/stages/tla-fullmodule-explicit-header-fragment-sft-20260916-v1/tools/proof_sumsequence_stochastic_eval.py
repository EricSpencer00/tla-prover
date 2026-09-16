"""Fresh paired TRAIN8/G4 inference contract; no reward labels or training."""
import argparse
import json
import os
from pathlib import Path
import random
import sys
import time

CPU_ENV={n:'4' for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
os.environ.update(CPU_ENV,HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_cuda_train as train
from tools import proof_cuda_broader_eval as common
from tools.proof_token_rl_packet import prepare_requests,validate_rollout,digest,sha,BROADER_SHA,EOS_IDS
from tools.proof_token_rl_sampling import sample_tokens
from harness.proof_owned_process import run_owned,as_runner_tuple

POLICIES=dict(parent='f41f4a147b0fbc4cbd62ba87403d76516b4cd9da96fcc577979b033fa96b1a91',
    child='24d5b18e4f0d79d472adaf01f9a4f9f846e2d3444bd7856a56535b53062360a9')
BUDGET=dict(seed=20261002,temperature=1.,max_new_tokens=3072,max_context=8192,
    group_size=4,requested_groups=8,requested_samples=32,total_seconds=1500,
    per_sample_seconds=180,post_admission_reserve=30,memory_limit=36*1024**3,
    distribution='full_vocabulary_categorical',top_k=0,top_p=1.,forced_eos=False,
    logits_processors=False,optimizer_updates=0,cpu_threads=4)
SOURCES=tuple(sorted(set(common.IMPLEMENTATION)|{'tools/proof_sumsequence_stochastic_eval.py',
    'tools/proof_token_rl_packet.py','tools/proof_token_rl_sampling.py','harness/proof_owned_process.py'}))
NAMES={'model.layers.31.'+n for n in ('input_layernorm.weight','post_attention_layernorm.weight',
    'mlp.down_proj.weight','mlp.gate_proj.weight','mlp.up_proj.weight','self_attn.k_proj.weight',
    'self_attn.o_proj.weight','self_attn.q_proj.weight','self_attn.v_proj.weight')}
PARAMETERS=218112000


def cpu():
    import torch
    torch.set_num_threads(4)
    if {n:os.environ.get(n) for n in CPU_ENV}!=CPU_ENV or torch.get_num_threads()!=4:
        raise ValueError('Frozen CPU4 environment required')


def derive_requests(raw,arm):
    if arm not in POLICIES:raise ValueError('Explicit frozen parent or child arm required')
    original=prepare_requests(raw,reward_stage='strict_tlaps')
    return dict(schema=1,kind='sumsequence_fresh_train8_stochastic_diagnosis',arm=arm,
        policy_sha256=POLICIES[arm],broader_prompts_sha256=BROADER_SHA,budget=BUDGET,
        selection_indices=original['selection_indices'],tasks=original['tasks'],
        requests=[dict(r,policy_sha256=POLICIES[arm]) for r in original['requests']],
        reward_stage='strict_tlaps',reward_labels_exported=False,training_authorized=False,
        reference_answers_exported=False,proof_success_claim=False,generalization_claim=False,
        training_linkage='Hash-pinned previously validated checkpoint; this inference admission does not revalidate its training matrix or reuse a one-update validator')


def checkpoint_state(saved,files):
    import torch
    state=saved['trainable_state']
    if (saved['config']['model_files']!=files or saved['config']['dtype_profile']!=train.PROFILE
        or set(state)!=NAMES or sum(v.numel() for v in state.values())!=PARAMETERS
        or any(not n.startswith('model.layers.31.') or v.dtype!=torch.float32
            or not bool(torch.isfinite(v).all()) for n,v in state.items())):
        raise ValueError('Exact finite frozen final-layer checkpoint required')
    return digest(saved['config'])


def admit(a):
    cpu()
    import torch
    import transformers
    evaluation=derive_requests(a.broader_prompts.read_bytes(),a.arm)
    if train.file_sha(a.checkpoint)!=POLICIES[a.arm]:raise ValueError('Exact arm checkpoint required')
    files=train.model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS:
        raise ValueError('Pinned model/runtime required')
    if json.loads((a.model_path/'generation_config.json').read_bytes())['eos_token_id']!=EOS_IDS:
        raise ValueError('Exact model EOS required')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    config_sha=checkpoint_state(saved,files);del saved
    if train.file_sha(a.checkpoint)!=POLICIES[a.arm]:raise ValueError('Checkpoint changed during admission')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encodings=[common.encode_prompt(tokenizer,t) for t in evaluation['tasks']]
    if any(e['status']!='ready' for e in encodings):raise ValueError('Full3072 output context required')
    return dict(schema=1,evaluation=evaluation,checkpoint_sha256=POLICIES[a.arm],
        checkpoint_config_sha256=config_sha,model_files=files,model_files_sha256=digest(files),
        versions=common.runtime_versions(),dtype_profile=train.PROFILE,eos_token_ids=EOS_IDS,
        encodings=encodings,implementation_sha256={n:train.file_sha(ROOT/n) for n in SOURCES})


def unknown(request,reason='worker_pending',status='unattempted'):
    return dict(request,request_sha256=digest(request),status=status,reason=reason)


def validate_rows(admission,rows,tokenizer=None):
    evaluation=admission['evaluation']
    if evaluation['budget']!=BUDGET or len(rows)!=32 or len(evaluation['requests'])!=32:
        raise ValueError('Frozen32 full accounting required')
    for i,(request,row) in enumerate(zip(evaluation['requests'],rows)):
        validate_rollout(request,row)
        if row['status'] in ('generated','generation_time_limit'):
            encoding=admission['encodings'][i//4]
            for key in ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256'):
                if row[key]!=encoding[key]:raise ValueError('Actual frozen prompt encoding changed')
            if tokenizer is not None and common.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Exact generated decoding changed')
            if row['finish_reason']!='time_limit' and row['elapsed_seconds']>180:
                raise ValueError('Over-budget completion cannot be admitted')


def persist_rows(output,rows):
    # Complete32 snapshot plus append-only sample events; no omitted denominator.
    pending=output/'rollouts.pending'
    pending.write_text(''.join(json.dumps(r)+'\n' for r in rows))
    pending.replace(output/'rollouts.jsonl')


def accounting(rows):
    return dict(requested_samples=32,accounted_samples=len(rows),
        generated_samples=sum(r['status'] in ('generated','generation_time_limit') for r in rows),
        unattempted_sample_ids=[r['sample_id'] for r in rows if r['status']=='unattempted'],
        worker_error_sample_ids=[r['sample_id'] for r in rows if r['status']=='worker_error'],
        eos_complete_samples=sum(r.get('finish_reason')=='eos' for r in rows),
        unknown_samples=sum(r.get('finish_reason')!='eos' for r in rows))


def validate_worker_summary(summary, rows, output, arm):
    """Completion must agree with the raw ledger, not just a worker boolean."""
    counts=accounting(rows)
    if (any(summary.get(k)!=v for k,v in counts.items()) or
        counts['generated_samples']!=32 or summary.get('phase_complete') is not True or
        summary.get('identity_stable') is not True or summary.get('failure') is not None or
        summary.get('optimizer_updates')!=0 or
        summary.get('frozen_weights_verified') is not True or
        summary.get('checkpoint_restored_exactly') is not True or
        summary.get('checkpoint_sha256')!=POLICIES[arm] or
        summary.get('verification_pending') is not True or
        summary.get('generalization_claim') is not False or
        summary.get('rollouts_sha256')!=train.file_sha(output/'rollouts.jsonl')):
        raise ValueError('Complete matching raw worker result required')
    for label in ('before','after'):
        if summary.get('sampling_generator_sha256',{}).get(label)!=train.file_sha(output/('sampling_generator_'+label+'.pt')):
            raise ValueError('Matching saved sampling RNG states required')


def failure_accounting(output, evaluation):
    """Preserve malformed evidence without fabricating unattempted counts."""
    path=output/'rollouts.jsonl'
    try:
        rows=[json.loads(s) for s in path.read_text().splitlines()]
        if len(rows)!=len(evaluation['requests']):raise ValueError('Incomplete ledger')
        for request,row in zip(evaluation['requests'],rows):validate_rollout(request,row)
        return accounting(rows)
    except Exception as exc:
        return dict(requested_samples=32,accounting_unverified=True,
            unknown_sample_ids=[r['sample_id'] for r in evaluation['requests']],
            unattempted_sample_ids=None,accounting_error=type(exc).__name__+': '+str(exc))


def memory():
    import torch
    values=dict(allocated=torch.cuda.max_memory_allocated(),reserved=torch.cuda.max_memory_reserved())
    if not 0<values['allocated']<=values['reserved']<=BUDGET['memory_limit']:
        raise ValueError('Frozen36GiB memory guard: '+str(values))
    return values


def assert_unchanged(selected,initial):
    import torch
    if set(selected)!=set(initial) or any(p.requires_grad or not torch.equal(p.detach().cpu(),initial[n]) for n,p in selected.items()):
        raise ValueError('Frozen restored weights changed')


def save_rng(generator,path):
    import torch
    state=generator.get_state().cpu().clone();torch.save(state,path)
    loaded=torch.load(path,map_location='cpu',weights_only=True)
    if loaded.dtype!=torch.uint8 or loaded.ndim!=1 or not loaded.numel() or not torch.equal(state,loaded):
        raise ValueError('Exact nonempty RNG byte state required')
    return train.file_sha(path)


def worker(a):
    started=time.monotonic()
    if not 30<a.worker_seconds<=1500:raise ValueError('Bounded remaining arm time required')
    frozen=json.loads(a.admission.read_bytes());current=admit(a)
    if current!=frozen:raise ValueError('Saved complete admission changed')
    import torch
    import transformers
    random.seed(20261002);torch.manual_seed(20261002);torch.cuda.manual_seed_all(20261002)
    torch.backends.cuda.matmul.allow_tf32=False;torch.cuda.reset_peak_memory_stats()
    net=train.load_policy(a.model_path)
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    if checkpoint_state(saved,frozen['model_files'])!=frozen['checkpoint_config_sha256']:
        raise ValueError('Restored checkpoint configuration drift')
    selected=train.restore_policy(net,saved,frozen['model_files'])
    initial={n:v.clone() for n,v in saved['trainable_state'].items()};del saved
    assert_unchanged(selected,initial)
    if any(p.requires_grad for p in net.parameters()) or net.generation_config.eos_token_id!=EOS_IDS:
        raise ValueError('Entire inference model must be frozen with original EOS')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    rng=torch.Generator(device='cuda').manual_seed(20261002)
    rng_hashes=dict(before=save_rng(rng,a.output/'sampling_generator_before.pt'))
    rows=[unknown(r) for r in frozen['evaluation']['requests']];failure=None
    with (a.output/'events.jsonl').open('x') as stream:
        for i,request in enumerate(frozen['evaluation']['requests']):
            remaining=a.worker_seconds-(time.monotonic()-started)-30
            if failure or remaining<=0:
                row=unknown(request,failure or 'fixed_arm_sampling_deadline')
            else:
                row=unknown(request,'sampling_started')
                try:
                    encoding=common.encode_prompt(tokenizer,frozen['evaluation']['tasks'][i//4])
                    if encoding!=frozen['encodings'][i//4]:raise ValueError('Encoder drift')
                    result=sample_tokens(net,torch.tensor(encoding['input_token_ids'],dtype=torch.long,device='cuda'),
                        generator=rng,eos_token_ids=EOS_IDS,max_new_tokens=3072,max_context=8192,
                        seconds=min(180,remaining),context_factory=lambda:train.autocast('cuda'))
                    row=dict(request,request_sha256=digest(request),
                        **{k:encoding[k] for k in ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256')},
                        **{k:v for k,v in result.items() if k not in ('forward_calls','do_sample')})
                    reply=common.decode_reply(tokenizer,row['token_ids'])
                    row.update(raw_reply=reply,raw_reply_sha256=sha(reply.encode()),token_ids_sha256=digest(row['token_ids']),
                        status='generation_time_limit' if row['finish_reason']=='time_limit' else 'generated')
                    memory()
                except Exception as exc:
                    failure=type(exc).__name__+': '+str(exc)
                    if row.get('status') not in ('generated','generation_time_limit'):
                        row=unknown(request,failure,status='worker_error')
            validate_rollout(request,row);rows[i]=row
            stream.write(json.dumps(row)+'\n');stream.flush();persist_rows(a.output,rows)
    assert_unchanged(selected,initial)
    rng_hashes['after']=save_rng(rng,a.output/'sampling_generator_after.pt')
    validate_rows(frozen,rows,tokenizer)
    stable=admit(a)==frozen;elapsed=time.monotonic()-started
    counts=accounting(rows)
    summary=dict(phase_complete=failure is None and stable and elapsed<=a.worker_seconds and counts['generated_samples']==32,
        failure=failure,identity_stable=stable,**counts,
        optimizer_updates=0,frozen_weights_verified=True,checkpoint_restored_exactly=True,
        checkpoint_sha256=POLICIES[a.arm],elapsed_seconds=elapsed,memory=memory(),
        sampling_generator_sha256=rng_hashes,rollouts_sha256=train.file_sha(a.output/'rollouts.jsonl'),
        hardware=dict(name=torch.cuda.get_device_name(),capability=list(torch.cuda.get_device_capability())),
        verification_pending=True,generalization_claim=False)
    train.dump(a.output/'worker_summary.json',summary)
    if not summary['phase_complete']:raise RuntimeError('Incomplete generation phase; no policy claims')


def generate(a):
    started=time.monotonic();a.output=a.output.resolve()
    for path in (a.broader_prompts,a.model_path,a.checkpoint,a.admission):
        path=path.resolve()
        if a.output==path or a.output in path.parents or path in a.output.parents:
            raise ValueError('Disjoint immutable inputs and output required')
    evaluation=derive_requests(a.broader_prompts.read_bytes(),a.arm)
    a.output.mkdir(parents=True,exist_ok=False)
    rows=[unknown(r) for r in evaluation['requests']];persist_rows(a.output,rows)
    train.dump(a.output/'summary.json',dict(phase_complete=False,**accounting(rows)))
    try:
        frozen=json.loads(a.admission.read_bytes())
        if admit(a)!=frozen:raise ValueError('Actual complete saved admission mismatch')
        train.dump(a.output/'admission.json',frozen)
        remaining=1500-(time.monotonic()-started)
        if remaining<=30:raise TimeoutError('No bounded worker time after admission')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']
        for key in ('broader_prompts','model_path','checkpoint','output'):
            command+=['--'+key.replace('_','-'),str(getattr(a,key).resolve())]
        command+=['--arm',a.arm,'--admission',str(a.output/'admission.json'),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);train.dump(a.output/'process.json',process)
        rc,_,_,timeout=as_runner_tuple(process)
        rows=[json.loads(s) for s in (a.output/'rollouts.jsonl').read_text().splitlines()]
        validate_rows(frozen,rows)
        if rc!=0 or timeout:raise RuntimeError('Owned generation phase incomplete')
        summary=json.loads((a.output/'worker_summary.json').read_bytes())
        validate_worker_summary(summary,rows,a.output,a.arm)
        elapsed=time.monotonic()-started
        if elapsed>1500:raise TimeoutError('Total arm1500-second deadline exceeded')
        summary.update(total_arm_seconds=elapsed,process_sha256=train.file_sha(a.output/'process.json'))
        train.dump(a.output/'summary.json',summary);return summary
    except BaseException as exc:
        train.dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),phase_complete=False))
        # Preserve any complete atomic ledger snapshot, even when the worker was
        # terminated before its final summary. Invalid rows remain unadmitted.
        train.dump(a.output/'summary.json',dict(phase_complete=False,**failure_accounting(a.output,evaluation),
            failure=type(exc).__name__+': '+str(exc),optimizer_updates=0,verification_pending=True))
        raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','generate','worker'))
    for name in ('broader-prompts','model-path','checkpoint','output'):
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--arm',choices=tuple(POLICIES),required=True);p.add_argument('--admission',type=Path)
    p.add_argument('--worker-seconds',type=float)
    a=p.parse_args()
    if a.mode=='admit':
        with a.output.open('x') as stream:json.dump(admit(a),stream,indent=2);stream.write('\n')
    elif a.admission is None:p.error('Saved full admission required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
