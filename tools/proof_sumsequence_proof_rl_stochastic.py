"""Fresh matched24d5/proof-RL-child TRAIN8/G4 inference; no optimizer or scores."""
import argparse
import json
from pathlib import Path
import random
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_proof_rl_eval as evaluation
from tools.proof_token_rl_sampling import sample_tokens
from tools.proof_token_rl_packet import validate_rollout,digest,sha,INDICES
from harness.proof_owned_process import run_owned

old=evaluation.stochastic;train=evaluation.train;common=evaluation.common
dump=evaluation.dump;load=evaluation.load;file_sha=evaluation.file_sha
ARMS=('parent','child');SECONDS=3420;ARM_SECONDS=1500;SEED=20261003
BUDGET=dict(evaluation.STOCHASTIC_BUDGET)
OVERHEAD=dict(minimum_post_admission_seconds=30,measured_admission_multiplier=1.25,
    policy='Reserve max(30,1.25*measured pre-admission seconds) separately inside worker and arm supervisor; never extend1500/3420.')
SOURCES=tuple(sorted(set(evaluation.SOURCES)|{'tools/proof_sumsequence_proof_rl_stochastic.py',
    'tools/proof_sumsequence_proof_rl_stochastic.pbs'}))


def sources():return {n:file_sha(ROOT/n) for n in SOURCES}


def parent_path(a):
    values=load(a.training_inputs)
    if set(values)!=set(evaluation.training.PATHS):raise ValueError('Exact training input manifest required')
    path=Path(values['checkpoint'])
    if not path.is_absolute() or file_sha(path)!=evaluation.PARENT_SHA:raise ValueError('Immutable24d5 checkpoint required')
    return path.resolve()


def arm_args(a,arm,admission=None):
    values={k:getattr(a,k) for k in evaluation.INPUTS}
    values.update(checkpoint=parent_path(a) if arm=='parent' else a.checkpoint,
        arm=arm,evaluation='stochastic32',output=a.output/arm,admission=admission,
        baseline_remote_root=a.baseline_remote_root,baseline_remote_parent=a.baseline_remote_parent)
    return SimpleNamespace(**values)


def admit(a):
    before=sources();arms={arm:evaluation.admit(arm_args(a,arm)) for arm in ARMS}
    value=dict(schema=1,kind='proof_rl_fresh_matched_train8_g4',seconds=SECONDS,arm_seconds=ARM_SECONDS,
        phase_order=list(ARMS),requested_samples=64,optimizer_updates=0,arms=arms,
        sources=before,overhead=OVERHEAD,verification_pending=True,generalization_claim=False)
    validate_pair(a,value);return value


def validate_pair(a,value):
    if (value.get('schema')!=1 or value.get('kind')!='proof_rl_fresh_matched_train8_g4' or
        value.get('seconds')!=SECONDS or value.get('arm_seconds')!=ARM_SECONDS or
        value.get('phase_order')!=list(ARMS) or value.get('requested_samples')!=64 or
        value.get('optimizer_updates')!=0 or value.get('sources')!=sources() or
        value.get('overhead')!=OVERHEAD or set(value.get('arms',{}))!=set(ARMS)):
        raise ValueError('Exact paired source/order/budget freeze required')
    child=file_sha(a.checkpoint)
    if child==evaluation.PARENT_SHA:raise ValueError('Distinct actual proof-RL child required')
    for arm in ARMS:
        admission=value['arms'][arm];args=arm_args(a,arm)
        if (admission['evaluation']!=evaluation.packet(args,child) or
            admission['evaluation']['budget']!=BUDGET or
            admission['checkpoint_sha256']!=file_sha(args.checkpoint) or
            admission['training_receipt']['child_sha256']!=child or
            admission['training_receipt']['parent_sha256']!=evaluation.PARENT_SHA or
            admission['source_sha256']!=evaluation.source_identity()):
            raise ValueError('Exact policy, original task packet and actual training receipt required')
    for key in ('model_files','model_files_sha256','versions','profile','eos_token_ids','encodings','training_receipt','cpu_environment'):
        if value['arms']['parent'][key]!=value['arms']['child'][key]:raise ValueError('Matched model/runtime/tokenizer/prompts/training lineage required')


def validate_rows(admission,rows,tokenizer=None):
    packet=admission['evaluation']
    if packet['budget']!=BUDGET or len(packet['requests'])!=32 or len(rows)!=32 or len(admission['encodings'])!=8:
        raise ValueError('Exact fresh32 complete accounting required')
    for i,(request,row) in enumerate(zip(packet['requests'],rows)):
        validate_rollout(request,row)
        if row['status'] in ('generated','generation_time_limit'):
            for key in ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256'):
                if row[key]!=admission['encodings'][i//4][key]:raise ValueError('Frozen exact input tokens/rendering required')
            if tokenizer is not None and common.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Exact raw response decoding required')
            if row['finish_reason']!='time_limit' and row['elapsed_seconds']>180:raise ValueError('Per-sample budget exceeded')


def rows_at(path):
    raw=path.read_bytes()
    if not raw.endswith(b'\n'):raise ValueError('Truncated raw rollout ledger')
    return [json.loads(line) for line in raw.splitlines()]


def reserve(seconds):return max(30.,OVERHEAD['measured_admission_multiplier']*seconds)


def failure_accounting(output,admission):
    try:
        rows=rows_at(output/'rollouts.jsonl');validate_rows(admission,rows)
        return old.accounting(rows)
    except Exception as exc:
        return dict(requested_samples=32,accounted_samples=32,accounting_unverified=True,unknown_samples=32,
            unknown_sample_ids=[r['sample_id'] for r in admission['evaluation']['requests']],
            unattempted_sample_ids=None,accounting_error=type(exc).__name__+': '+str(exc))


def worker_sources(a,frozen):
    pair=load(a.output.parent/'admission.json')
    if pair['sources']!=sources() or pair['arms'][a.arm]!=frozen:
        raise ValueError('Current stochastic worker source and exact paired admission required')
    return dict(stochastic_sources_sha256=digest(sources()),pair_admission_sha256=file_sha(a.output.parent/'admission.json'))


def worker(a):
    started=time.monotonic();frozen=load(a.admission)
    if not 30<a.worker_seconds<=ARM_SECONDS:raise ValueError('Bounded arm worker required')
    source_before=worker_sources(a,frozen)
    if evaluation.admit(a)!=frozen:raise ValueError('Full saved admission changed before CUDA load')
    admission_seconds=time.monotonic()-started;post_reserve=reserve(admission_seconds)
    if a.worker_seconds-admission_seconds-post_reserve<=0:raise TimeoutError('Admission exhausted worker; no model load')
    import torch,transformers
    random.seed(SEED);torch.manual_seed(SEED);torch.cuda.manual_seed_all(SEED)
    torch.backends.cuda.matmul.allow_tf32=False;torch.cuda.reset_peak_memory_stats()
    net=train.load_policy(a.model_path,device='cuda');evaluation.record_memory(a.output,'after_model_load')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    if old.checkpoint_state(saved,frozen['model_files'])!=frozen['checkpoint_config_sha256']:raise ValueError('Exact checkpoint configuration required')
    selected=train.restore_policy(net,saved,frozen['model_files'])
    initial={n:v.clone() for n,v in saved['trainable_state'].items()};del saved
    old.assert_unchanged(selected,initial);evaluation.record_memory(a.output,'after_checkpoint_restore')
    if any(p.requires_grad for p in net.parameters()) or net.generation_config.eos_token_id!=common.EOS_IDS:
        raise ValueError('Entire model frozen with original EOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    rng=torch.Generator(device='cuda').manual_seed(SEED)
    hashes=dict(before=old.save_rng(rng,a.output/'sampling_generator_before.pt'))
    rows=[old.unknown(r) for r in frozen['evaluation']['requests']];old.persist_rows(a.output,rows)
    failure=None
    with (a.output/'events.jsonl').open('x') as stream:
        for i,request in enumerate(frozen['evaluation']['requests']):
            remaining=a.worker_seconds-(time.monotonic()-started)-post_reserve
            if failure or remaining<=0:row=old.unknown(request,failure or 'fixed_sampling_deadline')
            else:
                row=old.unknown(request,'sampling_started')
                try:
                    encoded=common.encode_prompt(tokenizer,frozen['evaluation']['tasks'][i//4])
                    if encoded!=frozen['encodings'][i//4]:raise ValueError('Actual encoder changed')
                    result=sample_tokens(net,torch.tensor(encoded['input_token_ids'],dtype=torch.long,device='cuda'),
                        generator=rng,eos_token_ids=common.EOS_IDS,max_new_tokens=3072,max_context=8192,
                        seconds=min(180,remaining),context_factory=lambda:train.autocast('cuda'))
                    row=dict(request,request_sha256=digest(request),
                        **{k:encoded[k] for k in ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256')},
                        **{k:v for k,v in result.items() if k not in ('forward_calls','do_sample')})
                    reply=common.decode_reply(tokenizer,row['token_ids'])
                    row.update(raw_reply=reply,raw_reply_sha256=sha(reply.encode()),token_ids_sha256=digest(row['token_ids']),
                        status='generation_time_limit' if row['finish_reason']=='time_limit' else 'generated')
                    # Persist the candidate and peaks before memory guards may fail.
                    validate_rollout(request,row);rows[i]=row;old.persist_rows(a.output,rows)
                    evaluation.record_memory(a.output,'after_sample_'+str(i))
                except Exception as exc:
                    failure=type(exc).__name__+': '+str(exc)
                    if row.get('status') not in ('generated','generation_time_limit'):row=old.unknown(request,failure,'worker_error')
            validate_rollout(request,row);rows[i]=row;old.persist_rows(a.output,rows)
            stream.write(json.dumps(row)+'\n');stream.flush()
    old.assert_unchanged(selected,initial);hashes['after']=old.save_rng(rng,a.output/'sampling_generator_after.pt')
    validate_rows(frozen,rows,tokenizer)
    stable=evaluation.admit(a)==frozen;elapsed=time.monotonic()-started
    if worker_sources(a,frozen)!=source_before:raise ValueError('Stochastic source or paired admission drift')
    counts=old.accounting(rows);memory=evaluation.record_memory(a.output,'after_final_admission')
    summary=dict(phase_complete=not failure and stable and elapsed<=a.worker_seconds and counts['generated_samples']==32,
        **counts,failure=failure,identity_stable=stable,optimizer_updates=0,frozen_weights_verified=True,
        checkpoint_restored_exactly=True,checkpoint_sha256=frozen['checkpoint_sha256'],elapsed_seconds=elapsed,
        pre_admission_seconds=admission_seconds,post_admission_reserve_seconds=post_reserve,
        memory=memory,sampling_generator_sha256=hashes,rollouts_sha256=file_sha(a.output/'rollouts.jsonl'),
        verification_pending=True,generalization_claim=False,seed=SEED,**source_before)
    dump(a.output/'worker_summary.json',summary)
    if not summary['phase_complete']:raise RuntimeError('Incomplete32; preserved raw attempts, no proof scores')


def validate_worker(admission,rows,summary,output):
    validate_rows(admission,rows)
    if (summary.get('stochastic_sources_sha256')!=digest(sources()) or
        summary.get('pair_admission_sha256')!=file_sha(output.parent/'admission.json')):
        raise ValueError('Frozen stochastic source and paired admission receipt required')
    if (any(summary.get(k)!=v for k,v in old.accounting(rows).items()) or summary.get('generated_samples')!=32 or
        any(summary.get(k) is not True for k in ('phase_complete','identity_stable','frozen_weights_verified','checkpoint_restored_exactly','verification_pending')) or
        summary.get('failure') is not None or summary.get('optimizer_updates')!=0 or summary.get('seed')!=SEED or
        summary.get('generalization_claim') is not False or summary.get('checkpoint_sha256')!=admission['checkpoint_sha256'] or
        summary.get('rollouts_sha256')!=file_sha(output/'rollouts.jsonl') or not 0<summary.get('elapsed_seconds',float('inf'))<=ARM_SECONDS or
        not 0<=summary.get('pre_admission_seconds',float('inf'))<ARM_SECONDS or
        summary.get('post_admission_reserve_seconds')!=reserve(summary['pre_admission_seconds'])):
        raise ValueError('Exact complete frozen32 worker summary required')
    if rows_at(output/'events.jsonl')!=rows:raise ValueError('Exact all32 events required')
    import torch
    for label in ('before','after'):
        path=output/('sampling_generator_'+label+'.pt')
        if summary['sampling_generator_sha256'][label]!=file_sha(path):raise ValueError('Actual RNG file hash changed')
        state=torch.load(path,map_location='cpu',weights_only=True)
        if state.dtype!=torch.uint8 or state.ndim!=1 or not state.numel():raise ValueError('Actual sampling RNG byte snapshot required')
    events=load(output/'memory_events.json')
    if [v['phase'] for v in events]!=['after_model_load','after_checkpoint_restore']+['after_sample_'+str(i) for i in range(32)]+['after_final_admission']:
        raise ValueError('All ordered memory phases required')
    for value in events:
        evaluation.greedy.memory_guard(value['allocated'],value['reserved'])
        if not 0<value['allocated']<=value['reserved']:raise ValueError('Actual positive memory evidence required')
    if summary['memory']!=load(output/'memory.json') or summary['memory']!={k:events[-1][k] for k in ('allocated','reserved')}:
        raise ValueError('Final actual memory must match summary')


def command_args(a):
    result=[]
    for key in evaluation.INPUTS:result+=['--'+key.replace('_','-'),str(getattr(a,key).resolve())]
    return result+['--baseline-remote-root',a.baseline_remote_root,'--baseline-remote-parent',a.baseline_remote_parent]


def generate_arm(a):
    started=time.monotonic();frozen=load(a.admission)
    a.output.mkdir(parents=True,exist_ok=False)
    rows=[old.unknown(r) for r in frozen['evaluation']['requests']];old.persist_rows(a.output,rows)
    dump(a.output/'summary.json',dict(phase_complete=False,**old.accounting(rows)))
    try:
        if evaluation.admit(a)!=frozen:raise ValueError('Exact full admission before worker required')
        pre=time.monotonic()-started;post=reserve(pre);remaining=ARM_SECONDS-pre-post
        if remaining<=30:raise TimeoutError('No sampling budget after admission reserve')
        dump(a.output/'admission.json',frozen)
        command=[sys.executable,str(Path(__file__).resolve()),'worker']+command_args(a)+[
            '--arm',a.arm,'--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);dump(a.output/'process.json',process)
        evaluation.historical.process_ok(process,command,ROOT,remaining)
        rows=rows_at(a.output/'rollouts.jsonl');summary=load(a.output/'worker_summary.json')
        validate_worker(frozen,rows,summary,a.output)
        if summary['elapsed_seconds']>remaining:raise ValueError('Worker exceeded remaining deadline')
        if evaluation.admit(a)!=frozen or load(a.admission)!=frozen or load(a.output/'admission.json')!=frozen:
            raise ValueError('Actual final full admission changed')
        elapsed=time.monotonic()-started
        if elapsed>ARM_SECONDS:raise TimeoutError('Full1500-second arm exceeded')
        summary.update(total_arm_seconds=elapsed,process_sha256=file_sha(a.output/'process.json'),
            supervisor_pre_admission_seconds=pre,supervisor_post_admission_reserve_seconds=post,worker_timeout_seconds=remaining)
        dump(a.output/'summary.json',summary);return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
        dump(a.output/'summary.json',dict(phase_complete=False,**failure_accounting(a.output,frozen),
            optimizer_updates=0,verification_pending=True));raise


def validate_arm_result(a,frozen,arm):
    root=a.output/arm;args=arm_args(a,arm,a.output/(arm+'-admission.json'))
    summary=load(root/'summary.json');worker_summary=load(root/'worker_summary.json')
    rows=rows_at(root/'rollouts.jsonl');validate_worker(frozen['arms'][arm],rows,worker_summary,root)
    extras=('total_arm_seconds','process_sha256','supervisor_pre_admission_seconds','supervisor_post_admission_reserve_seconds','worker_timeout_seconds')
    if {k:v for k,v in summary.items() if k not in extras}!=worker_summary:raise ValueError('Supervisor/raw worker summary mismatch')
    pre=summary['supervisor_pre_admission_seconds'];post=summary['supervisor_post_admission_reserve_seconds']
    seconds=summary['worker_timeout_seconds']
    if not 0<=pre<ARM_SECONDS or post!=reserve(pre) or seconds!=ARM_SECONDS-pre-post or not 30<seconds<=ARM_SECONDS:
        raise ValueError('Actual measured admission/remaining worker budget required')
    if not 0<summary['total_arm_seconds']<=ARM_SECONDS or worker_summary['elapsed_seconds']>seconds:
        raise ValueError('Actual bounded arm elapsed required')
    if load(root/'admission.json')!=frozen['arms'][arm] or load(args.admission)!=frozen['arms'][arm]:
        raise ValueError('Original complete arm admission changed')
    command=[sys.executable,str(Path(__file__).resolve()),'worker']+command_args(args)+[
        '--arm',arm,'--admission',str(root/'admission.json'),'--output',str(root),'--worker-seconds',str(seconds)]
    evaluation.historical.process_ok(load(root/'process.json'),command,ROOT,seconds)
    if summary['process_sha256']!=file_sha(root/'process.json'):raise ValueError('Raw arm process hash required')
    return summary


def initial(a):
    ids=[evaluation.greedy.broader.TRAIN_IDS[i] for i in INDICES]
    return dict(complete=False,phase='pending',requested_samples=64,accounted_samples=64,optimizer_updates=0,
        verification_pending=True,generalization_claim=False,
        unattempted_sample_ids={arm:[task+':sample'+str(i) for task in ids for i in range(4)] for arm in ARMS})


def partial(output,frozen,state):
    state['partial_accounting']={}
    for arm in ARMS:
        path=output/arm/'rollouts.jsonl'
        if path.exists():
            counts=failure_accounting(output/arm,frozen['arms'][arm])
            state['partial_accounting'][arm]=counts;state['unattempted_sample_ids'][arm]=counts.get('unattempted_sample_ids')


def execute(a):
    if not 0<a.worker_seconds<=SECONDS:raise ValueError('Bounded paired owned execution required')
    started=time.monotonic();frozen=load(a.admission);validate_pair(a,frozen)
    state=initial(a);dump(a.output/'summary.json',state)
    try:
        for arm in ARMS:
            if a.worker_seconds-(time.monotonic()-started)<ARM_SECONDS:
                raise TimeoutError('Insufficient time for a full arm; no shortened paired sampling budget')
            validate_pair(a,frozen);path=a.output/(arm+'-admission.json');dump(path,frozen['arms'][arm])
            state['phase']=arm;dump(a.output/'summary.json',state)
            state[arm]=generate_arm(arm_args(a,arm,path))
            if validate_arm_result(a,frozen,arm)!=state[arm]:raise ValueError('Actual arm return differs from saved result')
            state['unattempted_sample_ids'][arm]=[]
            dump(a.output/'summary.json',state)
        validate_pair(a,frozen)
        import torch
        states=[torch.load(a.output/arm/'sampling_generator_before.pt',map_location='cpu',weights_only=True) for arm in ARMS]
        if not torch.equal(*states):raise ValueError('Paired initial same-seed RNG snapshots differ')
        state.update(complete=True,phase='sampled_pending_verification',elapsed_seconds=time.monotonic()-started)
        dump(a.output/'summary.json',state);return state
    except BaseException as exc:
        partial(a.output,frozen,state);state.update(complete=False,error=type(exc).__name__+': '+str(exc))
        dump(a.output/'summary.json',state);raise


def generate(a):
    started=time.monotonic();a.output=a.output.resolve()
    for key in (*evaluation.INPUTS,'admission'):
        path=getattr(a,key).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Isolated immutable inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False);state=initial(a);dump(a.output/'summary.json',state);frozen=None
    try:
        frozen=load(a.admission);validate_pair(a,frozen);dump(a.output/'admission.json',frozen)
        remaining=SECONDS-(time.monotonic()-started)
        command=[sys.executable,str(Path(__file__).resolve()),'_run']+command_args(a)+[
            '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);dump(a.output/'cycle_process.json',process)
        evaluation.historical.process_ok(process,command,ROOT,remaining)
        state=load(a.output/'summary.json')
        if (state.get('complete') is not True or state.get('phase')!='sampled_pending_verification' or
            state.get('requested_samples')!=64 or state.get('accounted_samples')!=64 or state.get('optimizer_updates')!=0 or
            state.get('unattempted_sample_ids')!={arm:[] for arm in ARMS}):raise ValueError('Complete exact64 pair required')
        for arm in ARMS:
            if validate_arm_result(a,frozen,arm)!=state[arm]:raise ValueError('Actual arm supervisor linkage required')
        import torch
        rng=[torch.load(a.output/arm/'sampling_generator_before.pt',map_location='cpu',weights_only=True) for arm in ARMS]
        if not torch.equal(*rng):raise ValueError('Exact same initial sampling RNG required')
        validate_pair(a,frozen)
        if load(a.admission)!=frozen or load(a.output/'admission.json')!=frozen:raise ValueError('Frozen admission file changed')
        elapsed=time.monotonic()-started
        if elapsed>SECONDS:raise TimeoutError('Total3420-second pair exceeded')
        state.update(total_seconds=elapsed,process_sha256=file_sha(a.output/'cycle_process.json'))
        dump(a.output/'summary.json',state);return state
    except BaseException as exc:
        if frozen:partial(a.output,frozen,state)
        state.update(complete=False,error=type(exc).__name__+': '+str(exc))
        dump(a.output/'summary.json',state);dump(a.output/'failure.json',dict(error=state['error']));raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','generate','_run','worker'))
    for name in evaluation.INPUTS:p.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--admission',type=Path)
    p.add_argument('--baseline-remote-root',required=True);p.add_argument('--baseline-remote-parent',required=True)
    p.add_argument('--arm',choices=ARMS);p.add_argument('--worker-seconds',type=float)
    a=p.parse_args();a.evaluation='stochastic32'
    if a.mode=='admit':
        value=admit(a)
        with a.output.open('x') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    elif a.admission is None:p.error('Full target CPU paired admission required')
    elif a.mode=='_run':execute(a)
    else:globals()[a.mode](a)


if __name__=='__main__':main()
