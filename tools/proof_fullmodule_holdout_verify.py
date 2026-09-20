"""Protected30 paired whole-module syntax replay, never training or semantic proof."""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_holdout_eval as evaluation
from tools import proof_fullmodule_holdout_packet as packet
from tools import proof_fullmodule_sany_checks as checks
from tools import proof_sany_repair_learning_verify as prior

load=evaluation.load;dump=evaluation.dump;digest=evaluation.digest;file_sha=evaluation.file_sha
LOCAL_PATHS=('packet','tokenizer_path','parent_checkpoint','child_checkpoint','training_input',
    'training_admission','training_output','target_admission','generations','remote_paths','controls')
REMOTE_KEYS=set(evaluation.PATHS)|{'output','admission','evaluation_root'}
SECONDS_PER_ARM=930


def sources():
    names=set(evaluation.sources())|set(checks.SOURCES)|set(prior.SOURCES)|{'tools/proof_fullmodule_holdout_verify.py'}
    return {name:file_sha(ROOT/name) for name in sorted(names)}


def remote_paths(path):
    value=load(path)
    if set(value)!=REMOTE_KEYS or any(not isinstance(v,str) or not Path(v).is_absolute()
        or str(Path(v))!=v or '..' in Path(v).parts for v in value.values()):
        raise ValueError('Exact observed absolute remote path manifest required')
    return value


def admitted_packet(a):
    if file_sha(a.packet)!=a.expected_packet_sha256:raise ValueError('Exact frozen protected30 packet bytes required')
    value=load(a.packet);tasks=packet.validate_export(value)
    # Full local oracle/config/dependency inventories, not just portable metadata.
    if packet.inventories()!=value['inventories']:raise ValueError('Current protected corpus/tokenizer inventory changed')
    return tasks


def training_linkage(a,frozen,tokenizer,remote):
    learning=evaluation.learning;admission=load(a.training_admission)
    binding=dict(model_files=frozen['model_files'],training_admission=admission,
                 training_admission_sha256=frozen['training_admission_sha256'])
    admitted=prior.training_admission(a,binding,tokenizer)  # Pure CPU token/state reconstruction only.
    receipt=frozen['training_receipt']
    if (receipt['algorithm']!=learning.ALGORITHM or receipt['optimizer_updates']!=84
        or receipt['parent_sha256']!=evaluation.PARENT_SHA or receipt['child_sha256']!=evaluation.CHILD_SHA
        or receipt['training_artifacts']!=evaluation.base.inventory(a.training_output)):
        raise ValueError('Actual immutable1bb6→8866 SFT84 artifact receipt required')
    summary=learning.validate_output(SimpleNamespace(output=a.training_output,checkpoint=a.parent_checkpoint),admitted)
    if digest(summary)!=receipt['validated_summary_sha256']:raise ValueError('Actual CPU training replay differs')
    root=receipt['process_root']
    if not isinstance(root,str) or not Path(root).is_absolute() or '..' in Path(root).parts:
        raise ValueError('Actual training process root required')
    command=[prior.common.PYTHON,str(Path(root)/'tools/proof_sany_repair_learning_train.py'),'worker']
    for name,key in [('input','training_input'),('model_path','model_path'),('checkpoint','parent_checkpoint'),('output','training_output')]:
        command+=['--'+name.replace('_','-'),remote[key]]
    command+=['--expected-input-sha256',evaluation.TRAIN_SHA,'--admission',str(Path(remote['training_output'])/'admission.json')]
    prior.common.audit_process(load(a.training_output/'process.json'),command,root,learning.BUDGET['seconds'])
    if load(a.training_output/'admitted.json')!=dict(complete=True,summary_sha256=file_sha(a.training_output/'summary.json'),
        process_sha256=file_sha(a.training_output/'process.json')):raise ValueError('Actual SFT supervisor receipt differs')
    if (file_sha(a.child_checkpoint)!=evaluation.CHILD_SHA or summary['checkpoint_sha256']!=evaluation.CHILD_SHA
        or file_sha(a.training_output/'policy_optimizer.pt')!=evaluation.CHILD_SHA):
        raise ValueError('Actual collected SFT child checkpoint required')
    return dict(parent_sha256=evaluation.PARENT_SHA,child_sha256=evaluation.CHILD_SHA,optimizer_updates=84,
        actual_cpu_training_replay=True,target_admission_sha256=a.target_admission_sha256,
        validated_training_summary_sha256=digest(summary),remote_admission_rerun_locally=False)


def target_admission(a,tasks,tokenizer):
    frozen=prior.authenticated(a.target_admission,a.target_admission_sha256)
    if frozen!=load(a.generations/'admission.json'):raise ValueError('Collected target admission differs from authentic receipt')
    files=frozen['model_files']
    if digest(files)!=evaluation.common.MODEL_FILES_SHA:raise ValueError('Exact actual base model manifest required')
    prior.tokenizer_files(a.tokenizer_path,files)
    encodings=[evaluation.encode(tokenizer,t) for t in tasks]
    for task,encoded in zip(tasks,encodings):
        if any(task.get(k)!=v for k,v in encoded.items() if k!='status'):raise ValueError('Full exact protected prompt tokens required')
    import torch
    policies={}
    for arm,path,pin in [('parent',a.parent_checkpoint,evaluation.PARENT_SHA),('child',a.child_checkpoint,evaluation.CHILD_SHA)]:
        if file_sha(path)!=pin:raise ValueError('Exact actual paired checkpoint required')
        saved=torch.load(path,map_location='cpu',weights_only=False)
        config=evaluation.base.stochastic.checkpoint_state(saved,files)
        policies[arm]=dict(checkpoint_sha256=pin,checkpoint_config_sha256=config)
        del saved
    context=max(e['input_tokens'] for e in encodings)+16384
    if load(a.tokenizer_path/'config.json')['max_position_embeddings']!=131072 or context>131072:
        raise ValueError('Unmodified actual complete context capability required')
    expected=dict(schema=1,kind='protected30_fullmodule_paired_sany_diagnostic',budget=evaluation.BUDGET,
        task_ids=[t['id'] for t in tasks],tasks=tasks,encodings=encodings,packet_sha256=a.expected_packet_sha256,
        policies=policies,phase_order=list(evaluation.ARMS),declared_context=context,model_max_position_embeddings=131072,
        model_files=files,model_files_sha256=digest(files),versions=evaluation.common.FIRST_VERSIONS,profile=evaluation.train.PROFILE,
        eos_token_ids=evaluation.common.EOS_IDS,source_sha256=evaluation.sources(),cpu_environment=evaluation.base.CPU_ENV,
        prompt_environment=packet.environment(),training_receipt=frozen['training_receipt'],
        training_admission_sha256=file_sha(a.training_admission),optimizer_updates=0,verification_pending=True,
        training_authorized=False,protected_outputs_never_train=True,official_gate2_replication=False,tlc_claim=False,gate_claim=False,
        scope='Paired greedy1 at fixed30s/item and16384 token ceiling; SANY diagnosis only, not TLC/pass32/G2 completion')
    if frozen!=expected:raise ValueError('Exact authenticated paired task/model/runtime/source receipt differs')
    return frozen


def generation_rows(a,frozen,remote,tokenizer):
    rows=evaluation.validate_worker(frozen,a.generations,tokenizer)
    worker=load(a.generations/'worker_summary.json');summary=load(a.generations/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];evaluation.finite(pre,3000)
    post=evaluation.reserve(pre);seconds=3000-pre-post
    if (summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds
        or worker['worker_seconds']!=seconds):raise ValueError('Exact actual shared supervisor/worker deadline required')
    command=[prior.common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_fullmodule_holdout_eval.py'),'worker']
    for name in evaluation.PATHS:command+=['--'+name.replace('_','-'),remote[name]]
    command+=['--expected-packet-sha256',a.expected_packet_sha256,'--admission',str(Path(remote['output'])/'admission.json'),
        '--output',remote['output'],'--worker-seconds',str(seconds)]
    prior.common.audit_process(load(a.generations/'process.json'),command,remote['evaluation_root'],seconds)
    extras={'total_seconds','supervisor_pre_admission_seconds','supervisor_post_admission_reserve_seconds',
            'worker_timeout_seconds','process_sha256','admission_sha256'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker
        or summary['process_sha256']!=file_sha(a.generations/'process.json')
        or summary['admission_sha256']!=a.target_admission_sha256):raise ValueError('Actual full generation supervisor linkage differs')
    evaluation.finite(worker['elapsed_seconds'],seconds);evaluation.finite(summary['total_seconds'],3000)
    return rows


def prepare(a):
    import transformers
    tasks=admitted_packet(a);current=checks.admit_controls(tasks,a.controls)
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    if packet.make_rows(tokenizer)!=tasks:raise ValueError('Full source/config Framing-A reconstruction differs')
    remote=remote_paths(a.remote_paths);frozen=target_admission(a,tasks,tokenizer)
    linkage=training_linkage(a,frozen,tokenizer,remote)
    rows=generation_rows(a,frozen,remote,tokenizer)
    return tasks,rows,current,linkage


def validate_inputs(tasks,raws):
    if [t['id'] for t in tasks]!=list(packet.IDS) or [(r['arm'],r['id']) for r in raws]!=[
        (arm,ident) for arm in evaluation.ARMS for ident in packet.IDS]:
        raise ValueError('Exact all30 protected tasks and paired60 raw keys required')


def summarize(rows,complete):
    if [(r['arm'],r['id']) for r in rows]!=[(arm,ident) for arm in evaluation.ARMS for ident in packet.IDS]:
        raise ValueError('Complete ordered60 outcomes required')
    if any(r['sany'] is not None and (type(r['sany']) is not int or r['sany'] not in (0,1)) for r in rows):
        raise ValueError('Binary syntax or explicit unknown required')
    arms={}
    for arm in evaluation.ARMS:
        chosen=[r for r in rows if r['arm']==arm]
        arms[arm]=dict(requested=30,accounted=len(chosen),sany_pass=sum(r['sany']==1 for r in chosen),
            sany_reject=sum(r['sany']==0 for r in chosen),sany_unknown=sum(r['sany'] is None for r in chosen),
            generation_eos=sum(r['finish_reason']=='eos' for r in chosen),
            generation_caps=sum(r['finish_reason']=='token_limit' for r in chosen),
            generation_timeouts=sum(r['finish_reason']=='time_limit' for r in chosen))
    transitions={name:[] for name in ('gain','loss','unchanged','unknown')}
    for before,after in zip(rows[:30],rows[30:]):
        left,right=before['sany'],after['sany']
        label='unknown' if left is None or right is None else 'gain' if right>left else 'loss' if right<left else 'unchanged'
        transitions[label].append(before['id'])
    return dict(complete=complete,requested_total=60,arms=arms,paired=transitions,syntax_only=True,
        protected_outputs_never_train=True,training_authorized=False,pooled_score=False,
        tlc_claim=False,non_vacuity_claim=False,tlaps_claim=False,gate2_claim=False,generalization_claim=False)


def evaluate(tasks,raws,current,output,*,checker=checks.check,clock=time.monotonic):
    validate_inputs(tasks,raws);output=Path(output)
    rows=[dict(arm=raw['arm'],id=task['id'],population=task['population'],split='official_holdout30',
        policy_sha256=packet.POLICIES[raw['arm']],raw_row_sha256=digest(raw),finish_reason=raw.get('finish_reason'),
        sany=None,status='unattempted',evidence=None) for task,raw in zip(tasks*2,raws)]
    dump(output/'rows.json',rows);complete=True
    for arm_index,arm in enumerate(evaluation.ARMS):
        start=clock()
        for index,task in enumerate(tasks):
            raw=raws[arm_index*30+index];row=rows[arm_index*30+index]
            if raw.get('finish_reason')!='eos':row['status']='unmeasured_generation'
            elif clock()-start>SECONDS_PER_ARM-30:row['status']='unmeasured_budget';complete=False
            else:
                value=checker(task,raw['raw_reply'],output/'checks'/arm/task['id'],current,timeout=30)
                row.update(sany=value['sany'],status=value['status'],evidence=value)
            dump(output/'rows.json',rows);dump(output/'summary.json',summarize(rows,False))
        if clock()-start>SECONDS_PER_ARM:complete=False
    return rows,summarize(rows,complete)


def audit_rows(tasks,raws,rows,current,output):
    validate_inputs(tasks,raws);summarize(rows,False)
    for task,raw,row in zip(tasks*2,raws,rows):
        if (row['raw_row_sha256']!=digest(raw) or row['finish_reason']!=raw.get('finish_reason')
            or row['policy_sha256']!=packet.POLICIES[raw['arm']] or row['population']!=task['population']
            or row['split']!='official_holdout30'):
            raise ValueError('Exact immutable protected raw output/target/policy linkage required')
        if raw.get('finish_reason')!='eos':
            if row['sany'] is not None or row['evidence'] is not None or row['status']!='unmeasured_generation':
                raise ValueError('Incomplete generation is unknown, never a model negative')
        elif row['status']=='unmeasured_budget':
            if row['sany'] is not None or row['evidence'] is not None:raise ValueError('Unattempted budget cannot be scored')
        else:
            value=row['evidence']
            checks.audit(task,raw['raw_reply'],value,Path(output)/'checks'/raw['arm']/task['id'],current)
            if row['sany']!=value['sany'] or row['status']!=value['status']:raise ValueError('Raw syntax result differs')


def identity(a,tasks):
    files={}
    for name in LOCAL_PATHS:
        path=getattr(a,name)
        for p in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if p.is_file():files[str(p.resolve())]=file_sha(p)
    return dict(files=files,verifier=checks.identity(tasks),sources=sources(),tasks_sha256=digest(tasks))


def verify(a):
    a.output=a.output.resolve()
    for name in LOCAL_PATHS:
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False);dump(a.output/'summary.json',dict(complete=False,requested_total=60,syntax_only=True))
    try:
        initial=admitted_packet(a);before=identity(a,initial);dump(a.output/'identity_before.json',before)
        tasks,raws,current,linkage=prepare(a)
        if tasks!=initial or identity(a,tasks)!=before:raise ValueError('Identity drift during local admission')
        frozen=digest(dict(tasks=tasks,raws=raws,current=current,linkage=linkage))
        dump(a.output/'config.json',dict(input_sha256=frozen,seconds_per_arm=SECONDS_PER_ARM,timeout_per_check=30,
            training_linkage=linkage,protected_outputs_never_train=True,syntax_only=True))
        rows,summary=evaluate(tasks,raws,current,a.output);audit_rows(tasks,raws,rows,current,a.output)
        after=identity(a,tasks);dump(a.output/'identity_after.json',after)
        stable=before==after and frozen==digest(dict(tasks=tasks,raws=raws,current=current,linkage=linkage))
        summary.update(identity_stable=stable,training_linkage=linkage,rows_sha256=file_sha(a.output/'rows.json'))
        summary['complete']=summary['complete'] and stable;dump(a.output/'summary.json',summary)
        if not summary['complete']:raise ValueError('Incomplete paired protected30 syntax replay')
        return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),complete=False))
        summary=load(a.output/'summary.json');summary['complete']=False;dump(a.output/'summary.json',summary);raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in (*LOCAL_PATHS,'output'):parser.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    parser.add_argument('--expected-packet-sha256',required=True);parser.add_argument('--target-admission-sha256',required=True)
    print(json.dumps(verify(parser.parse_args())))


if __name__=='__main__':main()
