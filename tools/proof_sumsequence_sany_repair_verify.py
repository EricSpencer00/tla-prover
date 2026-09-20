"""Local selected2 repair replay; never modifies or pools original40 pass@1."""
import argparse
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_sany_repair_eval as evaluation
from tools import proof_sumsequence_proof_rl_verify as common

checks=common.checks;load=common.load;dump=common.dump;digest=common.digest;file_sha=common.file_sha
SECONDS=180
LOCAL_PATHS=('packet','prompts','tokenizer_path','parent_checkpoint','child_checkpoint','training_output',
    'training_inputs','training_rollouts','generations','target_admission','remote_paths','controls')
REMOTE_KEYS=set(evaluation.INPUTS)|{'output','admission','evaluation_root'}
SOURCES=tuple(sorted(set(evaluation.SOURCES)|set(common.SOURCES)|{'tools/proof_sumsequence_sany_repair_verify.py'}))


def remote_paths(a):
    value=load(a.remote_paths)
    if set(value)!=REMOTE_KEYS or any(not isinstance(v,str) or not Path(v).is_absolute() or str(Path(v))!=v or '..' in Path(v).parts for v in value.values()):
        raise ValueError('Exact observed absolute remote path manifest required')
    return value


def bind_tasks(packet,tasks):
    if len(tasks)!=40 or packet['original_requested_ids']!=[t['id'] for t in tasks]:
        raise ValueError('Original ordered40 denominator must remain unchanged')
    chosen=[]
    for row in packet['tasks']:
        task=tasks[row['original_index']]
        if task['id']!=row['id'] or task['split']!='train' or any(task[k]!=v for k,v in row['context'].items()):
            raise ValueError('Exact original theorem, context and dependencies required')
        chosen.append(task)
    if [t['id'] for t in chosen]!=list(evaluation.IDS):raise ValueError('Exact selected2 original task IDs required')
    return chosen


def target_admission(a,tokenizer):
    if file_sha(a.target_admission)!=a.target_admission_sha256:
        raise ValueError('Explicit authentic target-host receipt hash required')
    value=evaluation.packet(a.packet);frozen=load(a.target_admission)
    if frozen!=load(a.generations/'admission.json'):raise ValueError('Collected admission differs from authentic receipt')
    expected=dict(schema=1,kind='selected2_full_context_repair_diagnostic',budget=evaluation.BUDGET,
        packet_sha256=evaluation.PACKET_SHA,checkpoint_sha256=evaluation.POLICY_SHA,
        model_files_sha256=evaluation.common.MODEL_FILES_SHA,versions=evaluation.common.FIRST_VERSIONS,
        profile=evaluation.train.PROFILE,eos_token_ids=evaluation.common.EOS_IDS,
        encodings=[evaluation.encode(tokenizer,row) for row in value['tasks']],
        original_encoding_sha256=[digest(row['encoding']) for row in value['tasks']],
        original_packet_budget=value['budget'],original_packet_executable_tasks=value['executable_tasks'],
        source_sha256=evaluation.sources(),cpu_environment=evaluation.base.CPU_ENV,optimizer_updates=0,
        original_denominator=40,repair_attempts=2,original_pass_at1_unchanged=True,
        verification_pending=True,generalization_claim=False,gate_claim=False,
        context_change='Explicit new9216 context budget; original8192 packet/overflow evidence unchanged; full prompts verbatim')
    if any(frozen.get(k)!=v for k,v in expected.items()) or file_sha(a.child_checkpoint)!=evaluation.POLICY_SHA:
        raise ValueError('Exact selected2 model/runtime/9216-context/source receipt required')
    if digest(frozen['model_files'])!=evaluation.common.MODEL_FILES_SHA:raise ValueError('Exact complete model file manifest required')
    wanted={n:h for n,h in frozen['model_files'].items() if n.endswith('.json') or n in ('tokenizer.model','chat_template.jinja')}
    actual={p.name:file_sha(p) for p in a.tokenizer_path.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))}
    if actual!=wanted:raise ValueError('Exact complete local tokenizer inventory required')
    model_config=load(a.tokenizer_path/'config.json')
    if (type(frozen['model_max_position_embeddings']) is not int or frozen['model_max_position_embeddings']<9216 or
        frozen['model_max_position_embeddings']!=model_config['max_position_embeddings']):
        raise ValueError('Original unmodified model context capability required')
    import torch
    saved=torch.load(a.child_checkpoint,map_location='cpu',weights_only=False)
    if evaluation.base.stochastic.checkpoint_state(saved,frozen['model_files'])!=frozen['checkpoint_config_sha256']:
        raise ValueError('Actual locally collected1bb6 checkpoint config differs from receipt')
    return frozen


def generation_rows(a,frozen,remote,tokenizer):
    rows=load(a.generations/'accounting.json');evaluation.validate_rows(frozen,rows,tokenizer)
    worker=load(a.generations/'worker_summary.json');evaluation.validate_worker(frozen,rows,worker,a.generations)
    summary=load(a.generations/'summary.json');process=load(a.generations/'process.json')
    extras=('total_seconds','process_sha256','admission_sha256','supervisor_pre_admission_seconds',
            'supervisor_post_admission_reserve_seconds','worker_timeout_seconds')
    if {k:v for k,v in summary.items() if k not in extras}!=worker:
        raise ValueError('Actual supervisor must extend exact raw worker summary')
    pre=summary['supervisor_pre_admission_seconds'];common.finite_budget(pre,1200)
    post=evaluation.reserve(pre);seconds=1200-pre-post
    if (seconds<=30 or summary['supervisor_post_admission_reserve_seconds']!=post or
        summary['worker_timeout_seconds']!=seconds or summary['admission_sha256']!=a.target_admission_sha256 or
        summary['process_sha256']!=file_sha(a.generations/'process.json')):
        raise ValueError('Actual pre/post-admission reserve and complete process linkage required')
    command=[common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_sumsequence_sany_repair_eval.py'),'worker']
    for key in evaluation.INPUTS:command+=['--'+key.replace('_','-'),remote[key]]
    command+=['--admission',str(Path(remote['output'])/'admission.json'),'--output',remote['output'],'--worker-seconds',str(seconds)]
    common.audit_process(process,command,remote['evaluation_root'],seconds)
    common.finite_budget(worker['elapsed_seconds'],seconds);common.finite_budget(summary['total_seconds'],1200)
    return rows


def prepare(a):
    import transformers
    remote=remote_paths(a);packet=evaluation.packet(a.packet)
    tasks=checks.admit_tasks(load(a.prompts));chosen=bind_tasks(packet,tasks)
    current=checks.admit_controls(a.controls,tasks)
    command=[sys.executable,str(Path(checks.__file__).resolve()),'--worker','--prompts',str(a.prompts.resolve()),
             '--output',str((a.controls/'controls').resolve())]
    common.audit_process(load(a.controls/'process.json'),command,str(ROOT),checks.SECONDS)
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    frozen=target_admission(a,tokenizer)
    linkage=common.training_linkage(a,frozen,remote)
    rows=generation_rows(a,frozen,remote,tokenizer)
    return tasks,chosen,rows,current,linkage


def identity(a,tasks):
    files={}
    for name in LOCAL_PATHS:
        path=getattr(a,name)
        for item in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if item.is_file():files[str(item.resolve())]=file_sha(item)
    return dict(files=files,verifier=checks.identity(tasks),sources={n:file_sha(ROOT/n) for n in SOURCES},
        scope='Authentic target receipt and local CPU checkpoint/tokenizer/raw-process replay; no remote model admission rerun')


def summarize(rows,complete):
    if [r['id'] for r in rows]!=list(evaluation.IDS):raise ValueError('All selected2 repair attempts remain in denominator')
    return dict(complete=complete,requested_repairs=2,accounted_repairs=len(rows),original_denominator=40,
        original_pass_at1_unchanged=True,pooled_pass_at1_claim=False,training_authorized=False,gate_claim=False,
        generalization_claim=False,optimizer_updates=0,
        sany_pass=sum(r['sany']==1 for r in rows),proof_pass=sum(r['proof']==1 for r in rows),
        sany_unknown=sum(r['sany'] is None for r in rows),proof_unknown=sum(r['proof'] is None for r in rows),
        generation_cap=sum(r['finish_reason']=='token_limit' for r in rows),
        generation_timeout=sum(r['finish_reason']=='time_limit' for r in rows),
        scope='One selected greedy repair per known TRAIN task; separate from unchanged original40 greedy pass@1, not TLC')


def evaluate(tasks,raws,current,output,*,checker=checks.check,clock=time.monotonic):
    if [t['id'] for t in tasks]!=list(evaluation.IDS) or [r['id'] for r in raws]!=list(evaluation.IDS):
        raise ValueError('Exact ordered selected2 original task/repair binding required')
    rows=[dict(id=t['id'],split='train',repair_attempt=1,policy_sha256=evaluation.POLICY_SHA,
        raw_row_sha256=digest(raw),finish_reason=raw.get('finish_reason'),sany=None,proof=None,
        status='unattempted',evidence=None) for t,raw in zip(tasks,raws)]
    output=Path(output);dump(output/'rows.json',rows);started=clock();complete=True
    for task,raw,row in zip(tasks,raws,rows):
        if raw.get('finish_reason')!='eos':row['status']='unmeasured_generation'
        elif clock()-started>SECONDS-61:row['status']='unmeasured_budget';complete=False
        else:
            value=checker(task,raw['raw_reply'],output/'checks'/task['id'],current)
            row.update(sany=value['sany'],proof=value['proof'],status=value['status'],evidence=value)
        dump(output/'rows.json',rows);dump(output/'summary.json',summarize(rows,False))
    return rows,summarize(rows,complete and clock()-started<=SECONDS)


def audit_rows(tasks,raws,rows,current,output):
    if [r['id'] for r in rows]!=list(evaluation.IDS) or [t['id'] for t in tasks]!=list(evaluation.IDS) or [r['id'] for r in raws]!=list(evaluation.IDS):
        raise ValueError('Exact final selected2 key accounting required')
    for task,raw,row in zip(tasks,raws,rows):
        if (row['raw_row_sha256']!=digest(raw) or row['finish_reason']!=raw.get('finish_reason') or
            row['policy_sha256']!=evaluation.POLICY_SHA or row['split']!='train' or row['repair_attempt']!=1):
            raise ValueError('Actual original selected repair provenance changed')
        if raw.get('finish_reason')!='eos' or row['status']=='unmeasured_budget':
            if row['sany'] is not None or row['proof'] is not None or row['evidence'] is not None:
                raise ValueError('Capped/timed/unattempted repair cannot be scored')
            continue
        value=row['evidence'];extraction=checks.extract(task,raw['raw_reply'])
        if value is None or value['extraction']!=extraction or value['raw_reply_sha256']!=checks.sha(raw['raw_reply'].encode()):
            raise ValueError('Exact original-task extraction and raw reply evidence required')
        if extraction['fragment'] is None:
            if value['sany']!=0 or value['proof']!=0 or value['status']!='model_extraction' or value['evidence'] is not None:
                raise ValueError('Exact model extraction rejection required')
        else:
            checks.audit_check(task,extraction['fragment'],value['evidence'],Path(output)/'checks'/task['id'],current)
            if any(value[k]!=value['evidence'][k] for k in ('sany','proof','status')):raise ValueError('Raw checker classification differs')
        if any(row[k]!=value[k] for k in ('sany','proof','status')):raise ValueError('Final classification differs from checker')


def verify(a):
    a.output=a.output.resolve()
    for name in LOCAL_PATHS:
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    tasks=checks.admit_tasks(load(a.prompts));before=identity(a,tasks);dump(a.output/'identity_before.json',before)
    all_tasks,chosen,raws,current,linkage=prepare(a)
    if all_tasks!=tasks or identity(a,tasks)!=before:raise ValueError('Identity drift during local admission')
    dump(a.output/'config.json',dict(packet_sha256=evaluation.PACKET_SHA,target_admission_sha256=a.target_admission_sha256,
        seconds=SECONDS,budget=evaluation.BUDGET,training_linkage=linkage,original_pass_at1_unchanged=True,
        method='Exact original-task SANY and strict TLAPS; EOS only; selected2 repair, no retries or pooled gate claim'))
    rows,summary=evaluate(chosen,raws,current,a.output);audit_rows(chosen,raws,rows,current,a.output)
    after=identity(a,tasks);dump(a.output/'identity_after.json',after)
    summary.update(identity_stable=before==after,rows_sha256=file_sha(a.output/'rows.json'),training_linkage=linkage)
    summary['complete']=summary['complete'] and before==after;dump(a.output/'summary.json',summary)
    if not summary['complete']:raise ValueError('Incomplete repair replay; all requested keys retained')
    return summary


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in (*LOCAL_PATHS,'output'):p.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    p.add_argument('--target-admission-sha256',required=True)
    print(json.dumps(verify(p.parse_args())))


if __name__=='__main__':main()
