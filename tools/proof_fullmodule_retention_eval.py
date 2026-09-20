"""Inference-only new SFT child: unchanged greedy40 and selected repair2 separately."""
import argparse
import json
import math
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_learning_eval as lineage
from tools import proof_sany_repair_learning_eval as historical
learning=lineage.learning
from tools import proof_sumsequence_sany_repair_eval as repair
from harness.proof_owned_process import run_owned,as_runner_tuple
base=repair.base;common=base.common;train=base.train
load=base.load;dump=base.dump;digest=base.digest;file_sha=base.file_sha
PARENT_SHA=lineage.PARENT_SHA
PHASES=('greedy40','repair2')
SECONDS=3000
BUDGETS={'greedy40':dict(base.GREEDY_BUDGET),'repair2':dict(repair.BUDGET)}
BASELINE_SHA='77273044e9222cdc35900f2a831d094e42e1fef100e47fe3c956942b65473614'
BASELINE_ADMISSION_SHA='f536ae40980385e00a176137c1260c9615fa08781d9955a83905b7de65a931db'
PATHS=('prompts','repair_packet','model_path','parent_checkpoint','training_input','training_admission',
       'training_output','baseline_combined','checkpoint')+learning.PARENT_PATHS
SOURCES=tuple(sorted(set(historical.SOURCES)|set(lineage.SOURCES)|{
    'tools/proof_fullmodule_retention_eval.py','tools/proof_fullmodule_retention_eval.pbs'}))



def sources():return {p:file_sha(ROOT/p) for p in sorted(set(SOURCES)|set(lineage.sources()))}
def reserve(seconds):return max(30.,1.25*seconds)
def phase_seconds(phase):return 1000 if phase=='greedy40' else 1200


def requested_ids(phase):
    if phase=='greedy40':
        return list(base.greedy.broader.TRAIN_IDS)+list(base.greedy.broader.DEV_IDS)+list(base.greedy.extra.TRAIN_IDS)
    if phase=='repair2':return list(repair.IDS)
    raise ValueError('Explicit separate phase required')


training_args=lineage.training_args


def baseline(path,phase,tokenizer,tasks):
    """Authentic combined42 child8866 baseline; never old split1bb6 artifacts."""
    if digest(base.inventory(path))!=BASELINE_SHA:raise ValueError('Immutable combined42 baseline tree changed')
    if file_sha(path/'admission.json')!=BASELINE_ADMISSION_SHA:raise ValueError('Authentic collected8866 receipt required')
    frozen=load(path/'admission.json')
    if frozen['checkpoint_sha256']!=PARENT_SHA:raise ValueError('Actual historical8866 checkpoint required')
    if any(file_sha(ROOT/n)!=h for n,h in frozen['source_sha256'].items()):
        raise ValueError('Historical source identity changed')
    if phase not in PHASES or frozen['phases'][phase]['tasks']!=tasks:
        raise ValueError('Exact original phase task bytes required')
    rows=historical.validate_worker(frozen,path)
    for name in PHASES:
        historical.validate_rows(frozen,name,rows[name],tokenizer)
    encoded=[common.encode_prompt(tokenizer,t) if phase=='greedy40' else repair.encode(tokenizer,t) for t in tasks]
    if encoded!=frozen['phases'][phase]['encodings']:raise ValueError('Exact baseline tokenizer/input bytes required')
    summary=load(path/'summary.json');worker=load(path/'worker_summary.json')
    pre=summary['supervisor_pre_admission_seconds'];lineage.finite(pre,SECONDS)
    post=reserve(pre);seconds=SECONDS-pre-post
    if summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds:
        raise ValueError('Historical matched supervisor budget changed')
    process=load(path/'process.json')
    lineage.audit_process(process,process['command'],Path(process['cwd']),seconds)
    extras={'total_seconds','process_sha256','admission_sha256','supervisor_pre_admission_seconds',
        'supervisor_post_admission_reserve_seconds','worker_timeout_seconds'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker
        or summary['process_sha256']!=file_sha(path/'process.json')
        or summary['admission_sha256']!=BASELINE_ADMISSION_SHA or worker['elapsed_seconds']>seconds):
        raise ValueError('Exact historical combined42 supervisor receipt required')
    lineage.finite(summary['total_seconds'],SECONDS)
    return dict(policy_sha256=PARENT_SHA,original_role='child',artifacts_sha256=BASELINE_SHA,
        admission_sha256=BASELINE_ADMISSION_SHA,rows_sha256=digest(rows[phase]),accounted_rows=len(rows[phase]),
        phase=phase,baseline_regenerated=False,proof_scores_reused=False)


def prospective_admit(a):
    before=sources();args=training_args(a)
    training=learning.admit(args)
    if training!=load(a.training_admission):raise ValueError('Saved prospective SFT admission changed')
    if file_sha(a.parent_checkpoint)!=PARENT_SHA:raise ValueError('Immutable actual8866 parent required')
    if file_sha(a.prompts)!=base.PROMPTS_SHA:raise ValueError('Original40 packet bytes changed')
    original=base.greedy.validate_export(load(a.prompts));selected=repair.packet(a.repair_packet)
    import torch,transformers
    torch.set_num_threads(4)
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    files=train.model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS:
        raise ValueError('Exact original target model/runtime required')
    config=load(a.model_path/'config.json')
    if config['max_position_embeddings']<9216 or load(a.model_path/'generation_config.json')['eos_token_id']!=common.EOS_IDS:
        raise ValueError('Unmodified original model context/EOS required')
    phases={}
    for phase,tasks,path in (('greedy40',original,a.baseline_combined),('repair2',selected['tasks'],a.baseline_combined)):
        encoded=[common.encode_prompt(tokenizer,t) if phase=='greedy40' else repair.encode(tokenizer,t) for t in tasks]
        if any(e['status']!='ready' for e in encoded):raise ValueError('Full matched context required, no truncation')
        phases[phase]=dict(tasks=tasks,encodings=encoded,budget=BUDGETS[phase],
            baseline=baseline(path,phase,tokenizer,tasks),requested=40 if phase=='greedy40' else 2)
    if sources()!=before or learning.admit(args)!=training:raise ValueError('Prospective source/training admission drift')
    return dict(schema=1,kind='train169_child_retention_matched40_and_selected2',phases=phases,
        training_admission=training,training_admission_sha256=file_sha(a.training_admission),
        model_files=files,model_files_sha256=digest(files),versions=common.runtime_versions(),profile=train.PROFILE,
        parent_checkpoint_sha256=PARENT_SHA,model_max_position_embeddings=config['max_position_embeddings'],
        eos_token_ids=common.EOS_IDS,source_sha256=before,cpu_environment=base.CPU_ENV,
        seconds=SECONDS,optimizer_updates=0,verification_pending=True,pooled_pass_at1_claim=False,
        execution_scope='One inference-only worker, one model load; separate1000s/1200s sampling clocks,180s/item; '
            'full admission and model-load overhead share3000s supervisor budget with measured post-admission reserve',
        prospective_only=True)


def training_receipt(a,prospective):
    return lineage.training_receipt(a,prospective['training_admission'])


def admit(a):
    prospective=prospective_admit(a)
    if load(a.prospective)!=prospective:raise ValueError('Saved before-launch prospective admission differs')
    receipt=training_receipt(a,prospective)
    import torch
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    config=base.stochastic.checkpoint_state(saved,prospective['model_files'])
    return dict(prospective,prospective_only=False,prospective_sha256=file_sha(a.prospective),
        checkpoint_sha256=receipt['child_sha256'],checkpoint_config_sha256=config,training_receipt=receipt)


def validate_rows(frozen,phase,rows,tokenizer=None):
    if phase not in PHASES:raise ValueError('Separate named phase required')
    value=frozen['phases'][phase];encodings=value['encodings']
    if value['budget']!=BUDGETS[phase] or len(rows)!=value['requested'] or len(encodings)!=value['requested']:
        raise ValueError('Exact phase population and matched budget required')
    if [r['id'] for r in encodings]!=requested_ids(phase):raise ValueError('Original exact ordered phase IDs required')
    for expected,row in zip(encodings,rows):
        if any(row.get(k)!=v for k,v in expected.items() if k!='status'):raise ValueError('Exact phase input/order changed')
        if row.get('status')=='unattempted':
            if row!=base.unknown(expected,row.get('reason')) or not isinstance(row.get('reason'),str) or not row['reason']:
                raise ValueError('Explicit unknown required')
        else:
            fields=base.greedy.output_fields(row['token_ids'],row['raw_reply'],late=row['deadline_exceeded'])
            if row!=dict(expected,**fields):raise ValueError('Exact EOS/output/limit accounting required')
            if tokenizer is not None and common.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Actual decoded bytes changed')


def accounting(rows):
    return dict(requested=len(rows),generated=sum(r['status']!='unattempted' for r in rows),
        eos_complete=sum(r.get('finish_reason')=='eos' for r in rows),
        unknown=sum(r.get('finish_reason')!='eos' for r in rows))


def _worker(a):
    started=time.monotonic();frozen=load(a.admission)
    if not 60<a.worker_seconds<=SECONDS:raise ValueError('Bounded owned worker required')
    if admit(a)!=frozen:raise ValueError('Actual full child admission changed')
    pre=time.monotonic()-started;post=reserve(pre)
    if a.worker_seconds-pre-post<=0:raise TimeoutError('No model budget after measured admission reserve')
    import torch,transformers
    torch.set_num_threads(4);torch.backends.cuda.matmul.allow_tf32=False;torch.cuda.reset_peak_memory_stats()
    torch.manual_seed(BUDGETS['greedy40']['seed']);torch.cuda.manual_seed(BUDGETS['greedy40']['seed'])
    net=train.load_policy(a.model_path,device='cuda');base.record_memory(a.output,'after_model_load')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    if base.stochastic.checkpoint_state(saved,frozen['model_files'])!=frozen['checkpoint_config_sha256']:
        raise ValueError('Actual child state/config changed')
    selected=train.restore_policy(net,saved,frozen['model_files'])
    initial={n:v.clone() for n,v in saved['trainable_state'].items()};del saved
    base.stochastic.assert_unchanged(selected,initial);base.record_memory(a.output,'after_checkpoint_restore')
    if any(p.requires_grad for p in net.parameters()) or net.generation_config.eos_token_id!=common.EOS_IDS:
        raise ValueError('All weights frozen and exact actual EOS required')
    if net.config.max_position_embeddings!=frozen['model_max_position_embeddings']:raise ValueError('Model context changed')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if type(pad) is not int:raise ValueError('Scalar pad required')
    results={};phase_times={};rng={}
    for phase in PHASES:
        directory=a.output/phase;directory.mkdir(exist_ok=True)
        rows=[base.unknown(e) for e in frozen['phases'][phase]['encodings']];base.persist(directory,rows);results[phase]=rows
    for phase in PHASES:
        directory=a.output/phase;value=frozen['phases'][phase];rows=results[phase]
        seed=value['budget']['seed'];torch.manual_seed(seed);torch.cuda.manual_seed(seed)
        torch.save(dict(seed=seed,cpu=torch.get_rng_state(),cuda=torch.cuda.get_rng_state()),directory/'rng_before.pt')
        phase_start=time.monotonic()
        with (directory/'events.jsonl').open('x') as stream:
            for index,task in enumerate(value['tasks']):
                remaining=min(phase_seconds(phase)-(time.monotonic()-phase_start),
                    a.worker_seconds-(time.monotonic()-started)-post)
                if remaining<=0:break
                row=common.encode_prompt(tokenizer,task) if phase=='greedy40' else repair.encode(tokenizer,task)
                if row!=value['encodings'][index]:raise ValueError('Actual phase encoder drift')
                inputs=torch.tensor([row['input_token_ids']],device='cuda');item=time.monotonic();limit=min(180,remaining)
                with torch.inference_mode(),train.autocast('cuda'):
                    output=net.generate(input_ids=inputs,attention_mask=torch.ones_like(inputs),do_sample=False,
                        num_beams=1,num_return_sequences=1,max_new_tokens=3072,max_time=limit,pad_token_id=pad)
                torch.cuda.synchronize()
                tokens=common.trim_output(output[0,inputs.shape[1]:].tolist(),set(common.EOS_IDS))
                row.update(base.greedy.output_fields(tokens,common.decode_reply(tokenizer,tokens),late=time.monotonic()-item>limit))
                rows[index]=row;base.persist(directory,rows);stream.write(json.dumps(row)+'\n');stream.flush()
                base.record_memory(a.output,phase+'_sample_'+str(index))
        phase_times[phase]=time.monotonic()-phase_start
        torch.save(dict(seed=seed,cpu=torch.get_rng_state(),cuda=torch.cuda.get_rng_state()),directory/'rng_after.pt')
        rng[phase]={label:file_sha(directory/('rng_'+label+'.pt')) for label in ('before','after')}
        validate_rows(frozen,phase,rows,tokenizer)
    base.stochastic.assert_unchanged(selected,initial);stable=admit(a)==frozen
    memory=base.record_memory(a.output,'after_final_admission');elapsed=time.monotonic()-started
    counts={phase:accounting(rows) for phase,rows in results.items()}
    summary=dict(complete=stable and elapsed<=a.worker_seconds and all(v['generated']==v['requested'] for v in counts.values()),
        phases=counts,phase_seconds=phase_times,rng_sha256=rng,elapsed_seconds=elapsed,pre_admission_seconds=pre,
        post_admission_reserve_seconds=post,memory=memory,weights_unchanged=True,restore_exact=True,
        full_admission_stable=stable,checkpoint_sha256=frozen['checkpoint_sha256'],optimizer_updates=0,
        verification_pending=True,pooled_pass_at1_claim=False)
    dump(a.output/'worker_summary.json',summary)
    if not summary['complete']:raise RuntimeError('Incomplete matched42; all unknown keys preserved')


def worker(a):
    try:return _worker(a)
    except BaseException as exc:
        try:
            import torch
            if torch.cuda.is_available():base.record_memory(a.output,'worker_failure')
        except Exception:pass
        dump(a.output/'worker_failure.json',dict(error=type(exc).__name__+': '+str(exc),
            requested=42,complete=False,optimizer_updates=0))
        raise


def validate_worker(frozen,output,tokenizer=None):
    summary=load(output/'worker_summary.json');results={}
    for phase in PHASES:
        directory=output/phase;rows=load(directory/'accounting.json');validate_rows(frozen,phase,rows,tokenizer);results[phase]=rows
        raw=(directory/'events.jsonl').read_bytes()
        if not raw.endswith(b'\n') or [json.loads(s) for s in raw.splitlines()]!=rows:raise ValueError('Complete raw phase events required')
        if summary['phases'][phase]!=accounting(rows) or any(r['status']=='unattempted' for r in rows):
            raise ValueError('All42 original and repair attempts required separately')
        if not 0<summary['phase_seconds'][phase]<=phase_seconds(phase):raise ValueError('Matched phase deadline exceeded')
        import torch
        for label in ('before','after'):
            path=directory/('rng_'+label+'.pt')
            if file_sha(path)!=summary['rng_sha256'][phase][label]:raise ValueError('Raw phase RNG changed')
            rng=torch.load(path,map_location='cpu',weights_only=True)
            if set(rng)!=set(('seed','cpu','cuda')) or rng['seed']!=BUDGETS[phase]['seed']:
                raise ValueError('Original separate phase seed required')
            if any(rng[k].dtype!=torch.uint8 or rng[k].ndim!=1 or not rng[k].numel() for k in ('cpu','cuda')):
                raise ValueError('Actual CPU/CUDA RNG snapshots required')
    if (any(summary.get(k) is not True for k in ('complete','weights_unchanged','restore_exact','full_admission_stable','verification_pending'))
        or summary['checkpoint_sha256']!=frozen['checkpoint_sha256'] or summary['optimizer_updates']!=0
        or summary['pooled_pass_at1_claim'] is not False or not 0<summary['elapsed_seconds']<=SECONDS
        or not 0<=summary['pre_admission_seconds']<SECONDS
        or summary['post_admission_reserve_seconds']!=reserve(summary['pre_admission_seconds'])):
        raise ValueError('Actual complete bounded inference-only worker required')
    events=load(output/'memory_events.json')
    expected=['after_model_load','after_checkpoint_restore']+[p+'_sample_'+str(i) for p in PHASES for i in range(40 if p=='greedy40' else 2)]+['after_final_admission']
    if [r['phase'] for r in events]!=expected:raise ValueError('Complete ordered memory record required')
    for row in events:
        base.greedy.memory_guard(row['allocated'],row['reserved'])
        if not 0<row['allocated']<=row['reserved']:raise ValueError('Positive memory evidence required')
    if summary['memory']!=load(output/'memory.json') or summary['memory']!={k:events[-1][k] for k in ('allocated','reserved')}:
        raise ValueError('Final memory binding differs')
    return results


def command_args(a):
    values=[]
    for name in PATHS:values+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
    return values+['--expected-input-sha256',a.expected_input_sha256,'--expected-child-sha256',a.expected_child_sha256,'--prospective',str(a.prospective.resolve())]


def validate_output(a,frozen):
    results=validate_worker(frozen,a.output);worker=load(a.output/'worker_summary.json');summary=load(a.output/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];post=reserve(pre);remaining=SECONDS-pre-post
    if (not 0<=pre<SECONDS or remaining<=60 or summary['supervisor_post_admission_reserve_seconds']!=post
        or summary['worker_timeout_seconds']!=remaining):raise ValueError('Actual measured supervisor reserve required')
    process=load(a.output/'process.json');root=Path(process['cwd']).resolve()
    if file_sha(root/'tools/proof_fullmodule_retention_eval.py')!=file_sha(Path(__file__)):
        raise ValueError('Actual evaluator source mismatch')
    command=[sys.executable,str(root/'tools/proof_fullmodule_retention_eval.py'),'worker']+command_args(a)+[
        '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(remaining)]
    lineage.audit_process(process,command,root,remaining)
    extras={'total_seconds','process_sha256','admission_sha256','supervisor_pre_admission_seconds',
            'supervisor_post_admission_reserve_seconds','worker_timeout_seconds'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker or not 0<summary['total_seconds']<=SECONDS
        or worker['elapsed_seconds']>remaining or summary['process_sha256']!=file_sha(a.output/'process.json')
        or summary['admission_sha256']!=file_sha(a.admission) or load(a.output/'admission.json')!=frozen):
        raise ValueError('Exact bounded supervisor receipt required')
    return results


def generate(a):
    started=time.monotonic();a.output=a.output.resolve()
    for name in (*PATHS,'admission','prospective'):
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable input/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'summary.json',dict(complete=False,phases={'greedy40':dict(requested=40,unknown=40),
        'repair2':dict(requested=2,unknown=2)},optimizer_updates=0,pooled_pass_at1_claim=False))
    for phase in PHASES:
        directory=a.output/phase;directory.mkdir()
        base.persist(directory,[dict(id=name,status='unattempted',reason='admission_pending') for name in requested_ids(phase)])
    try:
        frozen=load(a.admission)
        if admit(a)!=frozen:raise ValueError('Saved actual full child admission changed')
        dump(a.output/'admission.json',frozen)
        for phase in PHASES:
            directory=a.output/phase
            base.persist(directory,[base.unknown(e) for e in frozen['phases'][phase]['encodings']])
        pre=time.monotonic()-started;post=reserve(pre);remaining=SECONDS-pre-post
        if remaining<=60:raise TimeoutError('No worker budget after full admission reserve')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']+command_args(a)+[
            '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);dump(a.output/'process.json',process)
        lineage.audit_process(process,command,ROOT,remaining)
        validate_worker(frozen,a.output)
        if admit(a)!=frozen or load(a.admission)!=frozen:raise ValueError('Final full child admission drift')
        elapsed=time.monotonic()-started
        if elapsed>SECONDS:raise TimeoutError('Total3000-second evaluator deadline exceeded')
        summary=load(a.output/'worker_summary.json')
        summary.update(total_seconds=elapsed,process_sha256=file_sha(a.output/'process.json'),
            admission_sha256=file_sha(a.admission),supervisor_pre_admission_seconds=pre,
            supervisor_post_admission_reserve_seconds=post,worker_timeout_seconds=remaining)
        dump(a.output/'summary.json',summary);validate_output(a,frozen);return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
        dump(a.output/'summary.json',dict(complete=False,phases={'greedy40':dict(requested=40,unknown=40),
            'repair2':dict(requested=2,unknown=2)},optimizer_updates=0,pooled_pass_at1_claim=False,
            accounting_unverified=True,total_seconds=time.monotonic()-started));raise


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('prospective','admit','generate','worker'))
    for name in PATHS:parser.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    parser.add_argument('--expected-input-sha256',required=True);parser.add_argument('--expected-child-sha256',required=True);parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--prospective',type=Path);parser.add_argument('--admission',type=Path);parser.add_argument('--worker-seconds',type=float)
    a=parser.parse_args()
    if a.mode in ('prospective','admit'):
        if a.mode=='admit' and a.prospective is None:parser.error('Before-launch prospective admission required')
        value=prospective_admit(a) if a.mode=='prospective' else admit(a)
        with a.output.open('x') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    elif a.prospective is None or a.admission is None:parser.error('Saved prospective and actual child admissions required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
