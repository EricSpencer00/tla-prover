"""Protected30 paired whole-module syntax replay, never training or semantic proof."""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_learning_eval as evaluation
from tools import proof_fullmodule_holdout_packet as packet
from tools import proof_fullmodule_sany_checks as checks
from tools import proof_sany_repair_learning_verify as prior

load=evaluation.load;dump=evaluation.dump;digest=evaluation.digest;file_sha=evaluation.file_sha
LOCAL_PATHS=('packet','tokenizer_path','parent_checkpoint','child_checkpoint','training_input',
    'training_admission','training_output','target_admission','generations','remote_paths','controls')+evaluation.learning.PARENT_PATHS
REMOTE_KEYS=set(evaluation.PATHS)|{'output','admission','evaluation_root'}
SECONDS_PER_ARM=930


def policy_map(a):
    pin=a.expected_child_sha256
    if not isinstance(pin,str) or len(pin)!=64 or any(c not in '0123456789abcdef' for c in pin) or pin==evaluation.PARENT_SHA:
        raise ValueError('Explicit distinct actual338-update child SHA required')
    return dict(parent=evaluation.PARENT_SHA,child=pin)


def validate_policies(policies):
    if policies!=policy_map(SimpleNamespace(expected_child_sha256=policies.get('child'))):
        raise ValueError('New paired8866/actual338-child policy mapping required; never old packet policies')


def sources():
    names=set(evaluation.sources())|set(checks.SOURCES)|set(prior.SOURCES)|{'tools/proof_fullmodule_learning_verify.py'}
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


def receipt_process(output,receipt,source,paths,input_sha,seconds):
    root=receipt['process_root']
    if not isinstance(root,str) or not Path(root).is_absolute() or '..' in Path(root).parts or str(Path(root))!=root:
        raise ValueError('Exact observed canonical training root required')
    command=[prior.common.PYTHON,str(Path(root)/source),'worker']
    for name,value in paths:command+=['--'+name.replace('_','-'),value]
    command+=['--expected-input-sha256',input_sha,'--admission',str(Path(dict(paths)['output'])/'admission.json')]
    evaluation.audit_process(load(output/'process.json'),command,root,seconds)
    if load(output/'admitted.json')!=dict(complete=True,summary_sha256=file_sha(output/'summary.json'),
        process_sha256=file_sha(output/'process.json')):raise ValueError('Actual successful training supervisor receipt required')


def ancestor_linkage(a,new_admission,files,tokenizer,remote):
    # This authenticates the unchanged old42/84 parent stage, not a new remote
    # model admission and not an assumed one-update RL checkpoint contract.
    old=evaluation.learning.ancestry.learning
    args=SimpleNamespace(training_input=a.parent_training_input,training_admission=a.parent_training_admission,
        training_output=a.parent_training_output,parent_checkpoint=a.parent_parent_checkpoint,tokenizer_path=a.tokenizer_path)
    binding=dict(model_files=files,training_admission=load(a.parent_training_admission),
        training_admission_sha256=new_admission['parent_training_admission_sha256'])
    admitted=prior.training_admission(args,binding,tokenizer)
    receipt=new_admission['parent_training_receipt']
    if (receipt['algorithm']!=old.ALGORITHM or receipt['optimizer_updates']!=84 or
        receipt['parent_sha256']!=evaluation.learning.ancestry.PARENT_SHA or receipt['child_sha256']!=evaluation.PARENT_SHA or
        receipt['training_artifacts']!=evaluation.base.inventory(a.parent_training_output)):
        raise ValueError('Actual old84 ancestor receipt and exact artifacts required')
    summary=old.validate_output(SimpleNamespace(output=a.parent_training_output,checkpoint=a.parent_parent_checkpoint),admitted)
    if (digest(summary)!=receipt['validated_summary_sha256'] or summary['checkpoint_sha256']!=evaluation.PARENT_SHA or
        file_sha(a.parent_training_output/'policy_optimizer.pt')!=evaluation.PARENT_SHA or file_sha(a.parent_checkpoint)!=evaluation.PARENT_SHA):
        raise ValueError('Actual locally collected8866 parent and84-state replay required')
    paths=[('input',remote['parent_training_input']),('model_path',remote['model_path']),
        ('checkpoint',remote['parent_parent_checkpoint']),('output',remote['parent_training_output'])]
    receipt_process(a.parent_training_output,receipt,'tools/proof_sany_repair_learning_train.py',paths,
        file_sha(a.parent_training_input),old.BUDGET['seconds'])
    return receipt


def training_admission(a,frozen,tokenizer,remote):
    import torch
    learning=evaluation.learning;admitted=load(a.training_admission)
    if (file_sha(a.training_admission)!=frozen['training_admission_sha256'] or
        admitted!=load(a.training_output/'admission.json')):raise ValueError('Authentic338 stage admission differs from collected bytes')
    receipt=ancestor_linkage(a,admitted,frozen['model_files'],tokenizer,remote)
    raw=a.training_input.read_bytes();rows=learning.packet_rows(raw);value=json.loads(raw)
    if file_sha(a.training_input)!=a.expected_input_sha256 or value['old_packet_bytes'].encode()!=a.parent_training_input.read_bytes():
        raise ValueError('Exact new169 packet must preserve original42 packet bytes')
    encoded=[learning.helpers.encode_candidate(tokenizer,r['prompt'],r['response'],9216) for r in rows]
    if value['encodings']!=[dict(e,id=r['id'],prompt_sha256=r['prompt_sha256'],response_sha256=r['response_sha256']) for r,e in zip(rows,encoded)]:
        raise ValueError('Actual complete169 TRAIN token/mask reconstruction required')
    for row,e in zip(rows,encoded):
        inference=evaluation.common.encode_prompt(tokenizer,row)
        if inference['input_token_ids']!=e['input_ids'][:e['prompt_tokens']] or inference['rendered_prompt']!=e['rendered_prompt']:
            raise ValueError('Actual169 training/inference prefix mismatch')
    saved=torch.load(a.parent_checkpoint,map_location='cpu',weights_only=False)
    cfg=evaluation.base.stochastic.checkpoint_state(saved,frozen['model_files']);state=saved['trainable_state']
    if (set(state)!=set(learning.EXPECTED_NAMES) or sum(p.numel() for p in state.values())!=learning.PARAMETERS or
        any(p.dtype!=torch.float32 or not bool(torch.isfinite(p).all()) for p in state.values())):
        raise ValueError('Actual finite nine-FP32-tensor8866 parent required')
    expected=dict(schema=1,budget=learning.BUDGET,algorithm=learning.ALGORITHM,dtype_profile=learning.helpers.PROFILE,
        seed=learning.BUDGET['seed'],input_sha256=evaluation.base.sha(raw),parent_checkpoint_sha256=evaluation.PARENT_SHA,
        parent_training_receipt=receipt,parent_training_admission_sha256=file_sha(a.parent_training_admission),
        parent_config_sha256=cfg,parent_admission='Hash-pinned previously fully validated actual84-SFT child; not old one-update policy validator',
        model_max_position_embeddings=load(a.tokenizer_path/'config.json')['max_position_embeddings'],
        model_files=frozen['model_files'],model_files_sha256=digest(frozen['model_files']),versions=evaluation.common.FIRST_VERSIONS,
        train_ids=[r['id'] for r in rows],schedule=learning.schedule(),encodings=encoded,
        optimizer_initialization='fresh AdamW; parent optimizer/RNG deliberately not resumed',
        trainable_names=list(learning.EXPECTED_NAMES),trainable_parameters=learning.PARAMETERS,
        implementation_sha256={n:file_sha(ROOT/n) for n in learning.SOURCES})
    if admitted!=expected:raise ValueError('Exact CPU-reconstructed169 admission differs from authentic target')
    return admitted


def training_linkage(a,frozen,tokenizer,remote):
    learning=evaluation.learning;admitted=training_admission(a,frozen,tokenizer,remote);receipt=frozen['training_receipt']
    if (receipt['algorithm']!=learning.ALGORITHM or receipt['optimizer_updates']!=338 or
        receipt['parent_sha256']!=evaluation.PARENT_SHA or receipt['child_sha256']!=a.expected_child_sha256 or
        receipt['input_sha256']!=a.expected_input_sha256 or receipt['training_artifacts']!=evaluation.base.inventory(a.training_output)):
        raise ValueError('Actual new338 receipt and complete artifact inventory required')
    summary=learning.validate_output(SimpleNamespace(output=a.training_output,checkpoint=a.parent_checkpoint),admitted)
    if (digest(summary)!=receipt['validated_summary_sha256'] or summary['checkpoint_sha256']!=a.expected_child_sha256 or
        file_sha(a.child_checkpoint)!=a.expected_child_sha256 or file_sha(a.training_output/'policy_optimizer.pt')!=a.expected_child_sha256):
        raise ValueError('Actual338 CPU state replay and collected child binding required')
    mapping=dict(input=remote['training_input'],model_path=remote['model_path'],checkpoint=remote['parent_checkpoint'],
        **{n:remote[n] for n in learning.PARENT_PATHS})
    paths=[(name,mapping[name]) for name in learning.PATHS]+[('output',remote['training_output'])]
    receipt_process(a.training_output,receipt,'tools/proof_fullmodule_learning_train.py',paths,a.expected_input_sha256,learning.BUDGET['seconds'])
    return dict(parent_sha256=evaluation.PARENT_SHA,child_sha256=a.expected_child_sha256,optimizer_updates=338,
        ancestor_optimizer_updates=84,actual_cpu_training_replay=True,target_admission_sha256=a.target_admission_sha256,
        validated_training_summary_sha256=digest(summary),remote_admission_rerun_locally=False)


def target_admission(a,tasks,tokenizer):
    policy_map(a)
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
    for arm,path,pin in [('parent',a.parent_checkpoint,evaluation.PARENT_SHA),('child',a.child_checkpoint,a.expected_child_sha256)]:
        if file_sha(path)!=pin:raise ValueError('Exact actual paired checkpoint required')
        saved=torch.load(path,map_location='cpu',weights_only=False)
        config=evaluation.base.stochastic.checkpoint_state(saved,files)
        policies[arm]=dict(checkpoint_sha256=pin,checkpoint_config_sha256=config)
        del saved
    context=max(e['input_tokens'] for e in encodings)+16384
    if load(a.tokenizer_path/'config.json')['max_position_embeddings']!=131072 or context>131072:
        raise ValueError('Unmodified actual complete context capability required')
    expected=dict(schema=1,kind='protected30_fullmodule_learning_paired45_sany_diagnostic',budget=evaluation.BUDGET,
        task_ids=[t['id'] for t in tasks],tasks=tasks,encodings=encodings,packet_sha256=a.expected_packet_sha256,
        policies=policies,phase_order=list(evaluation.ARMS),declared_context=context,model_max_position_embeddings=131072,
        model_files=files,model_files_sha256=digest(files),versions=evaluation.common.FIRST_VERSIONS,profile=evaluation.train.PROFILE,
        eos_token_ids=evaluation.common.EOS_IDS,source_sha256=evaluation.sources(),cpu_environment=evaluation.base.CPU_ENV,
        prompt_environment=packet.environment(),training_receipt=frozen['training_receipt'],
        training_admission_sha256=file_sha(a.training_admission),training_input_sha256=a.expected_input_sha256,
        expected_child_sha256=a.expected_child_sha256,optimizer_updates=0,verification_pending=True,
        training_authorized=False,protected_outputs_never_train=True,official_gate2_replication=False,tlc_claim=False,gate_claim=False,
        scope='New matched45s greedy1 at16384 token ceiling; separate from old30s run, SANY only, no TLC/proof/G2 claim')
    if frozen!=expected:raise ValueError('Exact authenticated paired task/model/runtime/source receipt differs')
    return frozen


def generation_rows(a,frozen,remote,tokenizer):
    rows=evaluation.validate_worker(frozen,a.generations,tokenizer)
    worker=load(a.generations/'worker_summary.json');summary=load(a.generations/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];evaluation.finite(pre,3420)
    post=evaluation.reserve(pre);seconds=3420-pre-post
    if (summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds
        or worker['worker_seconds']!=seconds):raise ValueError('Exact actual shared supervisor/worker deadline required')
    command=[prior.common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_fullmodule_learning_eval.py'),'worker']
    for name in evaluation.PATHS:command+=['--'+name.replace('_','-'),remote[name]]
    for name in evaluation.HASH_ARGS:command+=['--'+name.replace('_','-'),getattr(a,name)]
    command+=['--admission',str(Path(remote['output'])/'admission.json'),
        '--output',remote['output'],'--worker-seconds',str(seconds)]
    evaluation.audit_process(load(a.generations/'process.json'),command,remote['evaluation_root'],seconds)
    extras={'total_seconds','supervisor_pre_admission_seconds','supervisor_post_admission_reserve_seconds',
            'worker_timeout_seconds','process_sha256','admission_sha256'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker
        or summary['process_sha256']!=file_sha(a.generations/'process.json')
        or summary['admission_sha256']!=a.target_admission_sha256):raise ValueError('Actual full generation supervisor linkage differs')
    evaluation.finite(worker['elapsed_seconds'],seconds);evaluation.finite(summary['total_seconds'],3420)
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
        inference_budget=evaluation.BUDGET,scope='New matched45s protected30 diagnostic; no pooling with previous30s results',
        protected_outputs_never_train=True,training_authorized=False,pooled_score=False,
        tlc_claim=False,non_vacuity_claim=False,tlaps_claim=False,gate2_claim=False,generalization_claim=False)


def evaluate(tasks,raws,current,output,policies,*,checker=checks.check,clock=time.monotonic):
    validate_inputs(tasks,raws);validate_policies(policies);output=Path(output)
    rows=[dict(arm=raw['arm'],id=task['id'],population=task['population'],split='official_holdout30',
        policy_sha256=policies[raw['arm']],raw_row_sha256=digest(raw),finish_reason=raw.get('finish_reason'),
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


def audit_rows(tasks,raws,rows,current,output,policies):
    validate_inputs(tasks,raws);validate_policies(policies);summarize(rows,False)
    for task,raw,row in zip(tasks*2,raws,rows):
        if (row['raw_row_sha256']!=digest(raw) or row['finish_reason']!=raw.get('finish_reason')
            or row['policy_sha256']!=policies[raw['arm']] or row['population']!=task['population']
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
        policies=policy_map(a)
        rows,summary=evaluate(tasks,raws,current,a.output,policies);audit_rows(tasks,raws,rows,current,a.output,policies)
        after=identity(a,tasks);dump(a.output/'identity_after.json',after)
        stable=before==after and frozen==digest(dict(tasks=tasks,raws=raws,current=current,linkage=linkage))
        summary.update(identity_stable=stable,training_linkage=linkage,policies=policies,rows_sha256=file_sha(a.output/'rows.json'))
        summary['complete']=summary['complete'] and stable;dump(a.output/'summary.json',summary)
        if not summary['complete']:raise ValueError('Incomplete paired protected30 syntax replay')
        return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),complete=False))
        summary=load(a.output/'summary.json');summary['complete']=False;dump(a.output/'summary.json',summary);raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in (*LOCAL_PATHS,'output'):parser.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    for name in (*evaluation.HASH_ARGS,'target_admission_sha256'):parser.add_argument('--'+name.replace('_','-'),required=True)
    print(json.dumps(verify(parser.parse_args())))


if __name__=='__main__':main()
