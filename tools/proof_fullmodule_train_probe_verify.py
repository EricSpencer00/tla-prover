"""Local paired TRAIN20 syntax replay; never reads protected evaluation data."""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_train_probe_eval as evaluation
from tools import proof_fullmodule_train_probe_packet as packet
from tools import proof_fullmodule_learning_verify as lineage
from tools import proof_fullmodule_training_checks as controls

checks=controls.common;load=evaluation.load;dump=evaluation.dump;digest=evaluation.digest;file_sha=evaluation.file_sha
LOCAL_PATHS=lineage.LOCAL_PATHS
REMOTE_KEYS=set(evaluation.PATHS)|{'output','admission','evaluation_root'}
SECONDS_PER_ARM=630


def sources():
    names=set(evaluation.sources())|set(lineage.sources())|set(controls.SOURCES)|{'tools/proof_fullmodule_train_probe_verify.py'}
    return {name:file_sha(ROOT/name) for name in sorted(names)}


def admitted_packet(a):
    if (file_sha(a.packet)!=a.expected_packet_sha256 or a.expected_input_sha256!=packet.INPUT_SHA or
        lineage.policy_map(a)!=packet.POLICIES):raise ValueError('Exact selected TRAIN20 packet/input/policies required')
    tasks=packet.validate_export(load(a.packet))
    if packet.select(a.training_input.read_bytes())!=tasks:raise ValueError('Exact target-free selection from original TRAIN169 required')
    return tasks


def bind_tasks(tasks,training_value,control_root):
    candidates=json.loads(training_value['audit_rows_bytes'])
    originals=controls.staged_tasks(candidates,control_root,write=False)
    if originals!=load(control_root/'tasks.json'):raise ValueError('Exact original TRAIN128 staged source/description/config binding required')
    mapping={t['id']:(i,t) for i,t in enumerate(originals)};selected=[]
    for task in tasks:
        order,original=mapping[task['control_task_id']]
        if (original['module_name']!=task['module_name'] or original['source']['sha256']!=task['source_sha256'] or
            original['index']!=task['audit_index'] or original['preparation_row_sha256']!=task['audit_row_sha256'] or
            original['training_blocked'] or original['exclusion_status']!='lexically_clear' or task['split']!='train'):
            raise ValueError('Exact original control/task/module/source/index binding required')
        source=checks.checked(original['source']['path'],original['source']['sha256']).decode()
        module=checks.gen_eval.extract_module(source)
        if module is None or checks.runner.module_name(module)!=task['module_name']:
            raise ValueError('Actual selected reference extractor integration required before scoring')
        selected.append(dict(probe=task,checker_task=original,control_order=order))
    if len(selected)!=20 or len({s['control_order'] for s in selected})!=20:
        raise ValueError('Exactly20 distinct selected TRAIN references required')
    return originals,selected


def admit_controls(a,originals,selected):
    for name,pin in packet.training.CONTROL_PINS.items():
        if file_sha(a.controls/name)!=pin:raise ValueError('Authentic full256 control receipt/ledger bytes required')
    rows=load(a.controls/'rows.json');summary=load(a.controls/'summary.json')
    before=load(a.controls/'identity_before.json')
    current=checks.identity(originals)
    if (before!=load(a.controls/'identity_after.json') or before['runtime']!=current or
        before['sources']!=controls.sources() or before['audit_files']!=controls.PINS):
        raise ValueError('Current TRAIN128 staging/runtime/source identity differs from original controls')
    expected=controls.summarize(originals,rows,summary['elapsed_seconds'],True,True)
    if summary!=dict(expected,rows_sha256=file_sha(a.controls/'rows.json')) or summary['all_controls_accepted'] is not True:
        raise ValueError('Full authentic256 accepted-control accounting required')
    args=SimpleNamespace(audit_root=controls.AUDIT_ROOT,output=a.controls)
    evaluation.audit_process(load(a.controls/'process.json'),controls.command(args),ROOT,controls.WORKER_SECONDS)
    receipt=load(a.controls/'receipt.json')
    if (receipt['complete'] is not True or receipt['process_sha256']!=file_sha(a.controls/'process.json') or
        receipt['summary_sha256']!=file_sha(a.controls/'summary.json')):
        raise ValueError('Authentic completed full256 supervisor receipt required')
    for entry in selected:
        task=entry['checker_task'];order=entry['control_order']
        source=checks.checked(task['source']['path'],task['source']['sha256']).decode()
        for offset,(label,candidate) in enumerate((('reference',source),('syntax_negative',checks.negative(source)))):
            row=rows[2*order+offset];value=row['result']
            checks.audit(task,candidate,value,a.controls/'checks'/f'{order:03d}'/label,current)
            if (row['id']!=task['id'] or row['index']!=task['index'] or row['label']!=label or
                row['sany']!=value['sany'] or row['status']!=value['status'] or row['accepted'] is not True or
                not controls.accepted(task,label,candidate,value)):
                raise ValueError('Actual selected40 control classifications changed')
    return current


def target_admission(a,tasks,tokenizer):
    frozen=lineage.prior.authenticated(a.target_admission,a.target_admission_sha256)
    if frozen!=load(a.generations/'admission.json'):raise ValueError('Collected generation admission differs from target receipt')
    files=frozen['model_files']
    if digest(files)!=evaluation.common.MODEL_FILES_SHA:raise ValueError('Exact frozen base model inventory required')
    lineage.prior.tokenizer_files(a.tokenizer_path,files)
    encoded=[evaluation.encode(tokenizer,t) for t in tasks]
    if any(task.get(k)!=v for task,e in zip(tasks,encoded) for k,v in e.items() if k!='status'):
        raise ValueError('Actual20 full training prompt/token reconstruction required')
    import torch
    policies={}
    for arm,path,pin in [('parent',a.parent_checkpoint,packet.POLICIES['parent']),('child',a.child_checkpoint,packet.POLICIES['child'])]:
        if file_sha(path)!=pin:raise ValueError('Exact actually trained parent/child required')
        state=torch.load(path,map_location='cpu',weights_only=False)
        policies[arm]=dict(checkpoint_sha256=pin,checkpoint_config_sha256=evaluation.base.stochastic.checkpoint_state(state,files))
        del state
    context=max(e['input_tokens'] for e in encoded)+16384
    if load(a.tokenizer_path/'config.json')['max_position_embeddings']!=131072 or context>131072:
        raise ValueError('Exact unmodified model full-context support required')
    expected=dict(schema=1,kind='train20_fullmodule_paired45_sany_diagnostic',budget=evaluation.BUDGET,
        task_ids=[r['id'] for r in tasks],tasks=tasks,encodings=encoded,packet_sha256=a.expected_packet_sha256,
        policies=policies,phase_order=list(evaluation.ARMS),declared_context=context,model_max_position_embeddings=131072,
        model_files=files,model_files_sha256=digest(files),versions=evaluation.common.FIRST_VERSIONS,profile=evaluation.train.PROFILE,
        eos_token_ids=evaluation.common.EOS_IDS,source_sha256=evaluation.sources(),cpu_environment=evaluation.base.CPU_ENV,
        prompt_environment=evaluation.environment(load(a.packet)),training_receipt=frozen['training_receipt'],
        training_admission_sha256=file_sha(a.training_admission),training_input_sha256=a.expected_input_sha256,
        expected_child_sha256=a.expected_child_sha256,optimizer_updates=0,verification_pending=True,training_authorized=False,
        train_only=True,official_gate2_replication=False,tlc_claim=False,gate_claim=False,holdout_claim=False,
        generalization_claim=False,proof_claim=False,
        scope='Fixed TRAIN20 greedy1 system diagnostic only; no holdout, generalization, TLC, proof or G2 claim')
    if frozen!=expected:raise ValueError('Exact authentic TRAIN20 target runtime/source/budget receipt differs')
    return frozen


def generation_rows(a,frozen,remote,tokenizer):
    rows=evaluation.validate_worker(frozen,a.generations,tokenizer)
    worker=load(a.generations/'worker_summary.json');summary=load(a.generations/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];evaluation.finite(pre,3420)
    post=evaluation.reserve(pre);seconds=3420-pre-post
    if (summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds or
        worker['worker_seconds']!=seconds):raise ValueError('Exact shared inference deadline and reserves required')
    command=[lineage.prior.common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_fullmodule_train_probe_eval.py'),'worker']
    for name in evaluation.PATHS:command+=['--'+name.replace('_','-'),remote[name]]
    for name in evaluation.HASH_ARGS:command+=['--'+name.replace('_','-'),getattr(a,name)]
    command+=['--admission',str(Path(remote['output'])/'admission.json'),'--output',remote['output'],'--worker-seconds',str(seconds)]
    evaluation.audit_process(load(a.generations/'process.json'),command,remote['evaluation_root'],seconds)
    extras={'total_seconds','supervisor_pre_admission_seconds','supervisor_post_admission_reserve_seconds',
            'worker_timeout_seconds','process_sha256','admission_sha256'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker or
        summary['process_sha256']!=file_sha(a.generations/'process.json') or summary['admission_sha256']!=a.target_admission_sha256):
        raise ValueError('Actual complete inference supervisor linkage required')
    evaluation.finite(worker['elapsed_seconds'],seconds);evaluation.finite(summary['total_seconds'],3420)
    return rows


def prepare(a):
    from transformers import AutoTokenizer
    tasks=admitted_packet(a);originals,selected=bind_tasks(tasks,load(a.training_input),a.controls)
    current=admit_controls(a,originals,selected)
    tokenizer=AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    remote=lineage.remote_paths(a.remote_paths);frozen=target_admission(a,tasks,tokenizer)
    linkage=lineage.training_linkage(a,frozen,tokenizer,remote)
    raws=generation_rows(a,frozen,remote,tokenizer)
    return tasks,originals,selected,raws,current,linkage


def blank(tasks):
    return [dict(arm=arm,id=t['id'],split='train',policy_sha256=packet.POLICIES[arm],
        raw_row_sha256=None,finish_reason=None,sany=None,status='admission_pending',evidence=None)
        for arm in evaluation.ARMS for t in tasks]


def summarize(rows,complete):
    if (len(rows)!=40 or [(r['arm'],r['id']) for r in rows[:20]]!=[('parent',r['id']) for r in rows[:20]] or
        [r['id'] for r in rows[:20]]!=[r['id'] for r in rows[20:]] or any(r['arm']!='child' for r in rows[20:])):
        raise ValueError('All40 ordered TRAIN attempts required')
    if len({r['id'] for r in rows[:20]})!=20 or any(r['sany'] is not None and (type(r['sany']) is not int or r['sany'] not in (0,1)) for r in rows):
        raise ValueError('Exactly20 distinct tasks and binary syntax or unknown required')
    arms={}
    for arm in evaluation.ARMS:
        items=[r for r in rows if r['arm']==arm]
        arms[arm]=dict(requested=20,accounted=len(items),sany_pass=sum(r['sany']==1 for r in items),
            sany_reject=sum(r['sany']==0 for r in items),sany_unknown=sum(r['sany'] is None for r in items),
            generation_eos=sum(r['finish_reason']=='eos' for r in items),generation_caps=sum(r['finish_reason']=='token_limit' for r in items),
            generation_timeouts=sum(r['finish_reason']=='time_limit' for r in items))
    paired={key:[] for key in ('gain','loss','unchanged','unknown')}
    for left,right in zip(rows[:20],rows[20:]):
        a,b=left['sany'],right['sany'];key='unknown' if a is None or b is None else 'gain' if b>a else 'loss' if b<a else 'unchanged'
        paired[key].append(left['id'])
    return dict(complete=complete,requested_total=40,arms=arms,paired=paired,inference_budget=evaluation.BUDGET,
        train_only=True,syntax_only=True,training_authorized=False,holdout_claim=False,generalization_claim=False,
        gate2_claim=False,tlc_claim=False,proof_claim=False,nonvacuity_claim=False,pooled_score=False)


def validate_keys(tasks,raws):
    if len(tasks)!=20 or [(r['arm'],r['id']) for r in raws]!=[(arm,t['id']) for arm in evaluation.ARMS for t in tasks]:
        raise ValueError('Exactly matched TRAIN20/40 raw ordered keys required')


def evaluate(tasks,selected,raws,current,output,*,checker=checks.check,clock=time.monotonic):
    validate_keys(tasks,raws)
    if [s['probe'] for s in selected]!=tasks:raise ValueError('Exact admitted selected reference adapters required')
    rows=blank(tasks);output=Path(output);complete=True
    for row,raw in zip(rows,raws):row.update(raw_row_sha256=digest(raw),finish_reason=raw.get('finish_reason'),status='unattempted')
    dump(output/'rows.json',rows)
    for arm_index,arm in enumerate(evaluation.ARMS):
        start=clock()
        for index,entry in enumerate(selected):
            row=rows[20*arm_index+index];raw=raws[20*arm_index+index]
            if raw.get('finish_reason')!='eos':row['status']='unmeasured_generation'
            elif clock()-start>SECONDS_PER_ARM-30:row['status']='unmeasured_budget';complete=False
            else:
                value=checker(entry['checker_task'],raw['raw_reply'],output/'checks'/arm/entry['probe']['id'],current,timeout=30)
                row.update(sany=value['sany'],status=value['status'],evidence=value)
            dump(output/'rows.json',rows);dump(output/'summary.json',summarize(rows,False))
        if clock()-start>SECONDS_PER_ARM:complete=False
    return rows,summarize(rows,complete)


def audit_rows(tasks,selected,raws,rows,current,output):
    validate_keys(tasks,raws);summarize(rows,False)
    if [s['probe'] for s in selected]!=tasks:raise ValueError('Reference adapter changed')
    for entry,raw,row in zip(selected*2,raws,rows):
        if (row['arm']!=raw['arm'] or row['id']!=raw['id'] or row['split']!='train' or
            row['policy_sha256']!=packet.POLICIES[raw['arm']] or row['raw_row_sha256']!=digest(raw) or row['finish_reason']!=raw.get('finish_reason')):
            raise ValueError('Exact TRAIN raw output/policy/attempt linkage required')
        if raw.get('finish_reason')!='eos':
            if row['sany'] is not None or row['evidence'] is not None or row['status']!='unmeasured_generation':raise ValueError('Capped/timed generation remains unknown')
        elif row['status']=='unmeasured_budget':
            if row['sany'] is not None or row['evidence'] is not None:raise ValueError('Unattempted checker remains unknown')
        else:
            value=row['evidence'];checks.audit(entry['checker_task'],raw['raw_reply'],value,Path(output)/'checks'/raw['arm']/row['id'],current)
            if row['sany']!=value['sany'] or row['status']!=value['status']:raise ValueError('Raw SANY result differs')


def identity(a,tasks):
    files={}
    for name in LOCAL_PATHS:
        path=getattr(a,name)
        for p in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if p.is_file():files[str(p.resolve())]=file_sha(p)
    return dict(files=files,sources=sources(),verifier=checks.identity(load(a.controls/'tasks.json')),tasks_sha256=digest(tasks))


def verify(a):
    a.output=a.output.resolve()
    for name in LOCAL_PATHS:
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable inputs/output required')
    tasks=admitted_packet(a)  # Portable TRAIN-only bytes; no runtime/target admission yet.
    a.output.mkdir(parents=True,exist_ok=False);rows=blank(tasks)
    dump(a.output/'rows.json',rows);dump(a.output/'summary.json',summarize(rows,False))
    try:
        before=identity(a,tasks);dump(a.output/'identity_before.json',before)
        actual,originals,selected,raws,current,linkage=prepare(a)
        if actual!=tasks or identity(a,tasks)!=before:raise ValueError('Identity drift during admission')
        frozen=digest(dict(tasks=tasks,selected=selected,raws=raws,current=current,linkage=linkage))
        dump(a.output/'config.json',dict(input_sha256=frozen,seconds_per_arm=SECONDS_PER_ARM,timeout_per_check=30,
            training_linkage=linkage,syntax_only=True,train_only=True,control_scope='Selected40 raw controls from authentic full256 receipt'))
        rows,summary=evaluate(tasks,selected,raws,current,a.output);audit_rows(tasks,selected,raws,rows,current,a.output)
        after=identity(a,tasks);dump(a.output/'identity_after.json',after)
        stable=before==after and frozen==digest(dict(tasks=tasks,selected=selected,raws=raws,current=current,linkage=linkage))
        summary.update(identity_stable=stable,training_linkage=linkage,rows_sha256=file_sha(a.output/'rows.json'))
        summary['complete']=summary['complete'] and stable;dump(a.output/'summary.json',summary)
        if not summary['complete']:raise ValueError('Incomplete TRAIN20 paired syntax replay')
        return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
        summary=load(a.output/'summary.json');summary['complete']=False;dump(a.output/'summary.json',summary);raise


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in (*LOCAL_PATHS,'output'):p.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    for name in (*evaluation.HASH_ARGS,'target_admission_sha256'):p.add_argument('--'+name.replace('_','-'),required=True)
    print(json.dumps(verify(p.parse_args())))


if __name__=='__main__':main()
