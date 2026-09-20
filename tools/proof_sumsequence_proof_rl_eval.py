"""Post proof-RL frozen admission and greedy40 generation; never a proof score.

Stochastic32 admissions freeze the next paired seed but generation is deliberately
not implemented here. Historical greedy output retains its original child label.
"""
import argparse
import json
import math
import os
from pathlib import Path
import sys
import time
from types import SimpleNamespace

CPU_ENV={n:'4' for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
os.environ.update(CPU_ENV)
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
# The training admission must configure its allocator before numerical imports.
from tools import proof_sumsequence_proof_rl_train as training
from tools import proof_sumsequence_repair_eval as greedy
from tools import proof_sumsequence_repair_verify as historical
from tools import proof_sumsequence_stochastic_eval as stochastic
from tools.proof_token_rl_packet import prepare_requests,validate_rollout,digest,sha
from harness.proof_owned_process import run_owned,as_runner_tuple

common=greedy.common;train=training.train;dump=greedy.dump;file_sha=greedy.file_sha
PARENT_SHA='24d5b18e4f0d79d472adaf01f9a4f9f846e2d3444bd7856a56535b53062360a9'
PROMPTS_SHA=historical.PROMPTS_SHA
GREEDY_BUDGET=dict(greedy.BUDGET)
STOCHASTIC_BUDGET=dict(stochastic.BUDGET,seed=20261003)
SOURCES=tuple(sorted(set(training.packet.SOURCES)|set(greedy.SOURCES)|set(historical.SOURCES)|set(stochastic.SOURCES)|{
    'tools/proof_sumsequence_proof_rl_eval.py','tools/proof_sumsequence_proof_rl_eval.pbs',
    'tools/__init__.py','harness/__init__.py',
    'harness/corpora.py','harness/lmgpa_bench.py','harness/proof_retrieval.py'}))
INPUTS=('prompts','model_path','checkpoint','training_inputs','training_output','baseline_cycle')


def load(path):return json.loads(Path(path).read_bytes())


def inventory(path):
    path=Path(path)
    return {str(p.relative_to(path)):file_sha(p) for p in sorted(path.rglob('*')) if p.is_file()}


def source_identity():return {name:file_sha(ROOT/name) for name in SOURCES}


def training_receipt(a):
    """Actual target-host readmission, optimizer/checkpoint replay and process audit."""
    paths=load(a.training_inputs)
    if set(paths)!=set(training.PATHS) or any(not isinstance(v,str) or not Path(v).is_absolute() for v in paths.values()):
        raise ValueError('Exact absolute training input manifest required')
    args=SimpleNamespace(**{k:Path(v).resolve() for k,v in paths.items()},output=a.training_output.resolve())
    if args.model_path!=a.model_path.resolve() or file_sha(args.checkpoint)!=PARENT_SHA:
        raise ValueError('Immutable24d5 parent and same base model required')
    frozen=load(args.output/'admission.json')
    if training.admit(args)!=frozen:raise ValueError('Current full training admission changed')
    worker=training.validate_output(args,frozen)
    summary=load(args.output/'summary.json');process=load(args.output/'process.json')
    # Evaluation may be staged separately from the immutable training run.
    # Admit the original source bytes, never rewrite its recorded command/cwd.
    record_root=Path(process['cwd']).resolve()
    record_source=record_root/'tools/proof_sumsequence_proof_rl_train.py'
    if file_sha(record_source)!=file_sha(ROOT/'tools/proof_sumsequence_proof_rl_train.py'):
        raise ValueError('Original training worker source differs from admitted source')
    command=[sys.executable,str(record_source),'worker']
    for key in (*training.PATHS,'output'):command+=['--'+key.replace('_','-'),str(getattr(args,key))]
    command+=['--admission',str(args.output/'admission.json'),'--worker-seconds']
    if process['command'][:-1]!=command:raise ValueError('Exact actual training process command required')
    seconds=float(process['command'][-1])
    if not training.CHECKPOINT_RESERVE<seconds<=training.SECONDS:raise ValueError('Bounded training worker required')
    historical.process_ok(process,command+[process['command'][-1]],record_root,seconds)
    if ({k:v for k,v in summary.items() if k not in ('total_seconds','process_sha256')}!=worker or
        summary.get('process_sha256')!=file_sha(args.output/'process.json') or
        not 0<summary.get('total_seconds',float('inf'))<=training.SECONDS):
        raise ValueError('Complete bounded training supervisor receipt required')
    child=file_sha(args.output/'policy_optimizer.pt')
    if child!=worker['checkpoint_sha256'] or child==PARENT_SHA:raise ValueError('Actual distinct one-update checkpoint required')
    return dict(parent_sha256=PARENT_SHA,child_sha256=child,optimizer_updates=1,
        training_inputs_sha256=file_sha(a.training_inputs),training_artifacts=inventory(args.output),
        training_admission_sha256=digest(frozen),validated_worker_sha256=digest(worker),
        training_process_root=str(record_root),training_process_source_sha256=file_sha(record_source))


def packet(a,child_sha):
    if a.evaluation not in ('greedy40','stochastic32') or a.arm not in ('parent','child'):
        raise ValueError('Explicit evaluation and arm required')
    raw=a.prompts.read_bytes()
    if sha(raw)!=PROMPTS_SHA:raise ValueError('Exact unchanged40 prompt packet required')
    portable=load(a.prompts);tasks=greedy.validate_export(portable)
    policy=PARENT_SHA if a.arm=='parent' else child_sha
    if a.evaluation=='greedy40':
        return dict(kind='proof_rl_greedy40_retention',arm=a.arm,policy_sha256=policy,
            prompts_sha256=PROMPTS_SHA,tasks=tasks,budget=GREEDY_BUDGET,
            counts=dict(original_train=32,original_development=4,new_train=4),requested=40)
    original=prepare_requests(portable['original_packet_bytes'].encode(),reward_stage='strict_tlaps')
    return dict(kind='proof_rl_fresh_train8_stochastic_retention',arm=a.arm,policy_sha256=policy,
        prompts_sha256=PROMPTS_SHA,tasks=original['tasks'],selection_indices=original['selection_indices'],
        requests=[dict(r,policy_sha256=policy) for r in original['requests']],
        budget=STOCHASTIC_BUDGET,requested=32,training_authorized=False,reference_answers_exported=False)


def baseline(a,tokenizer,tasks,*,tokenizer_path=None):
    """Audit the original24d5 child40 without converting it to a new parent run."""
    args=SimpleNamespace(generations=a.baseline_cycle,prompts=a.prompts,
        tokenizer_path=tokenizer_path or a.model_path,remote_model=str(a.model_path.resolve()),
        remote_root=a.baseline_remote_root,remote_parent=a.baseline_remote_parent)
    value=historical.validate_arm(args,'child',PARENT_SHA,tasks,tokenizer)
    return dict(original_role='child',policy_sha256=PARENT_SHA,
        provenance='Historical SFT80 child40; no new parent generation',
        artifacts=inventory(a.baseline_cycle/'child'),rows_sha256=digest(value['rows']),
        proof_scores_reused=False,current_sany_and_strict_replay_required=True)


def admit(a):
    os.environ.update(CPU_ENV)
    receipt=training_receipt(a)
    import torch,transformers
    torch.set_num_threads(4)
    evaluation=packet(a,receipt['child_sha256'])
    if file_sha(a.checkpoint)!=evaluation['policy_sha256']:raise ValueError('Exact selected parent or validated child checkpoint required')
    files=train.model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS:
        raise ValueError('Frozen base model/runtime required')
    if load(a.model_path/'generation_config.json')['eos_token_id']!=common.EOS_IDS:raise ValueError('Original actual EOS configuration required')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    config=stochastic.checkpoint_state(saved,files);del saved
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encoded=[common.encode_prompt(tokenizer,t) for t in evaluation['tasks']]
    if any(r['status']!='ready' for r in encoded):raise ValueError('All exact full contexts must fit')
    old=baseline(a,tokenizer,evaluation['tasks']) if a.evaluation=='greedy40' else None
    if file_sha(a.checkpoint)!=evaluation['policy_sha256']:raise ValueError('Checkpoint changed during full admission')
    return dict(schema=1,evaluation=evaluation,checkpoint_sha256=evaluation['policy_sha256'],
        checkpoint_config_sha256=config,model_files=files,model_files_sha256=digest(files),
        versions=common.runtime_versions(),profile=train.PROFILE,eos_token_ids=common.EOS_IDS,
        encodings=encoded,training_receipt=receipt,historical_baseline=old,
        source_sha256=source_identity(),cpu_environment=CPU_ENV,optimizer_updates=0,
        generalization_claim=False,verification_pending=True,stochastic_generation_implemented=False)


def unknown(encoding,reason='worker_pending'):
    return dict(encoding,status='unattempted',reason=reason)


def validate_rows(admission,rows,tokenizer=None):
    if admission['evaluation']['budget']!=GREEDY_BUDGET or admission['evaluation']['kind']!='proof_rl_greedy40_retention':
        raise ValueError('Greedy40 execution contract required')
    encoded=admission['encodings']
    if len(encoded)!=40 or len(rows)!=40:raise ValueError('All40 ordered attempted or unattempted rows required')
    for fixed,row in zip(encoded,rows):
        if any(row.get(k)!=v for k,v in fixed.items() if k!='status'):raise ValueError('Exact ordered prompt/input identity required')
        if row.get('status')=='unattempted':
            if row!=unknown(fixed,row.get('reason')) or not isinstance(row.get('reason'),str) or not row['reason']:
                raise ValueError('Explicit unknown row required')
        else:
            expected=dict(fixed,**greedy.output_fields(row['token_ids'],row['raw_reply'],late=row['deadline_exceeded']))
            if row!=expected:raise ValueError('Exact output tokens, decoded reply and EOS accounting required')
            if tokenizer is not None and common.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Exact decoder reconstruction required')


def accounting(rows):
    return dict(requested_tasks=40,accounted_tasks=len(rows),generated_rows=sum(r['status']!='unattempted' for r in rows),
        eos_complete=sum(r.get('finish_reason')=='eos' for r in rows),
        unknown_tasks=sum(r.get('finish_reason')!='eos' for r in rows),
        unattempted_ids=[r['id'] for r in rows if r['status']=='unattempted'])


def persist(output,rows):
    pending=output/'accounting.pending';dump(pending,rows);pending.replace(output/'accounting.json')


def memory():
    import torch
    return dict(allocated=torch.cuda.max_memory_allocated(),reserved=torch.cuda.max_memory_reserved())


def record_memory(output,phase):
    value=memory()
    dump(output/'memory.json',value)
    path=output/'memory_events.json';events=load(path) if path.exists() else []
    events.append(dict(phase=phase,**value));dump(path,events)
    # Preserve actual peaks before an over-limit guard can throw.
    greedy.memory_guard(**value)
    if not 0<value['allocated']<=value['reserved']:raise ValueError('Actual ordered positive GPU memory required')
    return value


def worker(a):
    started=time.monotonic()
    if a.evaluation!='greedy40' or a.arm!='child' or not 30<a.worker_seconds<=1000:
        raise ValueError('Only bounded newchild greedy40 generation implemented')
    frozen=load(a.admission)
    if admit(a)!=frozen:raise ValueError('Exact worker full admission required')
    import torch,transformers
    torch.manual_seed(GREEDY_BUDGET['seed']);torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats();net=train.load_policy(a.model_path,device='cuda')
    record_memory(a.output,'after_model_load')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    if stochastic.checkpoint_state(saved,frozen['model_files'])!=frozen['checkpoint_config_sha256']:raise ValueError('Checkpoint config changed')
    selected=train.restore_policy(net,saved,frozen['model_files'])
    initial={n:v.clone() for n,v in saved['trainable_state'].items()};del saved
    stochastic.assert_unchanged(selected,initial)
    record_memory(a.output,'after_checkpoint_restore')
    if any(p.requires_grad for p in net.parameters()) or net.generation_config.eos_token_id!=common.EOS_IDS:
        raise ValueError('Entire model must be frozen with exact EOS')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if type(pad) is not int:raise ValueError('Scalar pad required')
    rows=[unknown(r) for r in frozen['encodings']];persist(a.output,rows)
    with (a.output/'events.jsonl').open('x') as stream:
        for i,task in enumerate(frozen['evaluation']['tasks']):
            remaining=a.worker_seconds-(time.monotonic()-started)-30
            if remaining<=0:break
            row=common.encode_prompt(tokenizer,task)
            if row!=frozen['encodings'][i]:raise ValueError('Runtime encoder drift')
            inputs=torch.tensor([row['input_token_ids']],device='cuda');item=time.monotonic();limit=min(180,remaining)
            with torch.inference_mode(),train.autocast('cuda'):
                output=net.generate(input_ids=inputs,attention_mask=torch.ones_like(inputs),do_sample=False,
                    num_beams=1,num_return_sequences=1,max_new_tokens=3072,max_time=limit,pad_token_id=pad)
            torch.cuda.synchronize()
            tokens=common.trim_output(output[0,inputs.shape[1]:].tolist(),set(common.EOS_IDS))
            row.update(greedy.output_fields(tokens,common.decode_reply(tokenizer,tokens),late=time.monotonic()-item>limit))
            rows[i]=row;stream.write(json.dumps(row)+'\n');stream.flush();persist(a.output,rows)
            record_memory(a.output,'after_sample_'+str(i))
    stochastic.assert_unchanged(selected,initial);validate_rows(frozen,rows,tokenizer)
    stable=admit(a)==frozen;elapsed=time.monotonic()-started;counts=accounting(rows)
    summary=dict(complete=stable and counts['generated_rows']==40 and elapsed<=a.worker_seconds,**counts,
        memory=record_memory(a.output,'after_final_admission'),weights_unchanged=True,restore_exact=True,full_admission_stable=stable,
        optimizer_updates=0,checkpoint_sha256=frozen['checkpoint_sha256'],elapsed_seconds=elapsed,
        accounting_sha256=file_sha(a.output/'accounting.json'),verification_pending=True)
    dump(a.output/'worker_summary.json',summary)
    if not summary['complete']:raise RuntimeError('Incomplete40; all requested rows preserved')


def validate_worker_summary(frozen,rows,summary,output):
    validate_rows(frozen,rows)
    if any(summary.get(k)!=v for k,v in accounting(rows).items()) or summary.get('generated_rows')!=40:
        raise ValueError('Complete worker accounting differs from raw40')
    if any(summary.get(k) is not True for k in ('complete','weights_unchanged','restore_exact','full_admission_stable','verification_pending')):
        raise ValueError('Complete frozen-weight worker evidence required')
    if (summary.get('optimizer_updates')!=0 or summary.get('checkpoint_sha256')!=frozen['checkpoint_sha256'] or
        summary.get('accounting_sha256')!=file_sha(output/'accounting.json') or
        not 0<summary.get('elapsed_seconds',float('inf'))<=1000):raise ValueError('Exact bounded worker receipt required')
    values=summary['memory'];greedy.memory_guard(**values)
    if not 0<values['allocated']<=values['reserved']:raise ValueError('Actual memory evidence required')
    if load(output/'memory.json')!=values:raise ValueError('Raw memory evidence differs from summary')
    events=load(output/'memory_events.json')
    required=['after_model_load','after_checkpoint_restore']+['after_sample_'+str(i) for i in range(40)]+['after_final_admission']
    if [r.get('phase') for r in events]!=required:raise ValueError('Complete ordered memory phases required')
    for event in events:
        greedy.memory_guard(event['allocated'],event['reserved'])
        if not 0<event['allocated']<=event['reserved']:raise ValueError('Actual phase memory evidence required')
    if {k:events[-1][k] for k in ('allocated','reserved')}!=values:raise ValueError('Final phase memory mismatch')
    raw=(output/'events.jsonl').read_bytes()
    if not raw.endswith(b'\n') or [json.loads(s) for s in raw.splitlines()]!=rows:raise ValueError('Complete exact40 event ledger required')


def generate(a):
    if a.evaluation!='greedy40' or a.arm!='child':raise ValueError('Only greedy40 newchild execution implemented; stochastic is admission-only')
    started=time.monotonic();a.output=a.output.resolve()
    for name in (*INPUTS,'admission'):
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable inputs/output required')
    # Fixed population keys survive even corrupt prompt/admission input.
    ids=list(greedy.broader.TRAIN_IDS)+list(greedy.broader.DEV_IDS)+list(greedy.extra.TRAIN_IDS)
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'summary.json',dict(complete=False,requested_tasks=40,accounted_tasks=40,unknown_tasks=40,
        unattempted_ids=ids,optimizer_updates=0,verification_pending=True))
    frozen=None
    try:
        if file_sha(a.prompts)!=PROMPTS_SHA:raise ValueError('Exact40 prompts required')
        tasks=greedy.validate_export(load(a.prompts))
        if [t['id'] for t in tasks]!=ids:raise ValueError('Exact ordered40 population keys required')
        frozen=load(a.admission)
        if admit(a)!=frozen:raise ValueError('Saved full production admission changed')
        dump(a.output/'admission.json',frozen);persist(a.output,[unknown(r) for r in frozen['encodings']])
        remaining=1000-(time.monotonic()-started)-30
        if remaining<=30:raise TimeoutError('Full admission exhausted bounded phase')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']
        for name in INPUTS:command+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
        command+=['--baseline-remote-root',a.baseline_remote_root,'--baseline-remote-parent',a.baseline_remote_parent,
            '--evaluation',a.evaluation,'--arm',a.arm,'--admission',str(a.output/'admission.json'),
            '--output',str(a.output),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);dump(a.output/'process.json',process)
        historical.process_ok(process,command,ROOT,remaining)
        rows=load(a.output/'accounting.json');summary=load(a.output/'worker_summary.json')
        validate_worker_summary(frozen,rows,summary,a.output)
        if summary['elapsed_seconds']>remaining:raise ValueError('Worker exceeded its actual remaining deadline')
        if admit(a)!=frozen or load(a.admission)!=frozen or load(a.output/'admission.json')!=frozen:
            raise ValueError('Full post-generation admission changed')
        elapsed=time.monotonic()-started
        if elapsed>1000:raise TimeoutError('Total1000-second greedy phase exceeded')
        summary.update(total_seconds=elapsed,process_sha256=file_sha(a.output/'process.json'),
            admission_sha256=file_sha(a.admission),historical_baseline=frozen['historical_baseline'])
        dump(a.output/'summary.json',summary);return summary
    except BaseException as exc:
        # Keep partial raw files untouched. No unaudited partial ledger supplies a score.
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
        dump(a.output/'summary.json',dict(complete=False,requested_tasks=40,accounted_tasks=40,unknown_tasks=40,
            unattempted_ids=None,requested_ids=ids,accounting_unverified=True,
            optimizer_updates=0,verification_pending=True,total_seconds=time.monotonic()-started))
        raise


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('admit','generate','worker'))
    for name in INPUTS:parser.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--admission',type=Path)
    parser.add_argument('--baseline-remote-root',required=True);parser.add_argument('--baseline-remote-parent',required=True)
    parser.add_argument('--arm',choices=('parent','child'),required=True)
    parser.add_argument('--evaluation',choices=('greedy40','stochastic32'),required=True)
    parser.add_argument('--worker-seconds',type=float)
    a=parser.parse_args()
    if a.mode=='admit':
        value=admit(a)
        with a.output.open('x') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    elif a.admission is None:parser.error('Saved full production admission required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
