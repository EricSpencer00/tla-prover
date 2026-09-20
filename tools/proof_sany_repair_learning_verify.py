"""Local authenticated SFT84 artifact replay and separate matched40/repair2 checks.

Never invokes target-only model admission locally. Authentic target receipts are
explicitly hash pinned, then inputs, decoding, checkpoint and processes audited.
"""
import argparse
import json
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sany_repair_learning_eval as evaluation
from tools import proof_sany_repair_learning_checks as paired
from tools import proof_sumsequence_proof_rl_verify as common
from tools import proof_sumsequence_sany_repair_verify as old_repair

checks=paired.checks;learning=evaluation.learning
load=evaluation.load;dump=evaluation.dump;digest=evaluation.digest;file_sha=evaluation.file_sha
LOCAL_PATHS=('prompts','repair_packet','tokenizer_path','parent_checkpoint','child_checkpoint',
    'training_input','training_admission','training_output','baseline_original','baseline_repairs',
    'prospective_admission','target_admission','generations','remote_paths','controls')
REMOTE_KEYS=set(evaluation.PATHS)|{'output','admission','prospective','evaluation_root'}
SOURCES=tuple(sorted(set(evaluation.SOURCES)|set(checks.SOURCES)|{
    'tools/proof_sany_repair_learning_checks.py','tools/proof_sany_repair_learning_verify.py',
    'tools/proof_sumsequence_proof_rl_verify.py','tools/proof_sumsequence_sany_repair_verify.py'}))


def remote_paths(path):
    value=load(path)
    if set(value)!=REMOTE_KEYS or any(not isinstance(v,str) or not Path(v).is_absolute()
        or str(Path(v))!=v or '..' in Path(v).parts for v in value.values()):
        raise ValueError('Exact observed absolute remote path manifest required')
    return value


def authenticated(path,pin):
    if file_sha(path)!=pin:raise ValueError('Authentic target receipt hash mismatch')
    return load(path)


def tokenizer_files(tokenizer_path,files):
    wanted={n:h for n,h in files.items() if n.endswith('.json') or n in ('tokenizer.model','chat_template.jinja')}
    actual={p.name:file_sha(p) for p in tokenizer_path.iterdir() if p.is_file()
            and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))}
    if actual!=wanted:raise ValueError('Exact complete local tokenizer file inventory required')


def training_admission(a,prospective,tokenizer):
    import torch
    frozen=load(a.training_admission)
    if (file_sha(a.training_admission)!=prospective['training_admission_sha256']
        or frozen!=prospective['training_admission'] or frozen!=load(a.training_output/'admission.json')):
        raise ValueError('Actual SFT admission must match authentic prospective receipt')
    files=prospective['model_files'];raw=a.training_input.read_bytes();rows=learning.packet_rows(raw)
    encoded=[learning.helpers.encode_candidate(tokenizer,r['prompt'],r['response'],9216) for r in rows]
    if json.loads(raw)['encodings']!=[dict(e,id=r['id'],prompt_sha256=r['prompt_sha256'],response_sha256=r['response_sha256']) for r,e in zip(rows,encoded)]:
        raise ValueError('Full actual TRAIN42 tokenization differs from packet')
    for row,e in zip(rows,encoded):
        inference=evaluation.common.encode_prompt(tokenizer,row)
        if inference['input_token_ids']!=e['input_ids'][:e['prompt_tokens']] or inference['rendered_prompt']!=e['rendered_prompt']:
            raise ValueError('Actual train/inference prefix token identity differs')
    saved=torch.load(a.parent_checkpoint,map_location='cpu',weights_only=False)
    config=evaluation.base.stochastic.checkpoint_state(saved,files);state=saved['trainable_state']
    if (set(state)!=set(learning.EXPECTED_NAMES) or sum(p.numel() for p in state.values())!=learning.PARAMETERS
        or any(p.dtype!=torch.float32 or not bool(torch.isfinite(p).all()) for p in state.values())):
        raise ValueError('Exact finite nine-tensor immutable1bb6 parent required')
    expected=dict(schema=1,budget=learning.BUDGET,algorithm=learning.ALGORITHM,dtype_profile=learning.helpers.PROFILE,
        seed=learning.BUDGET['seed'],input_sha256=evaluation.base.sha(raw),parent_checkpoint_sha256=evaluation.PARENT_SHA,
        parent_config_sha256=config,parent_admission='Hash-pinned previously fully validated actual proof-RL child; not old one-update policy validator',
        model_max_position_embeddings=load(a.tokenizer_path/'config.json')['max_position_embeddings'],
        model_files=files,model_files_sha256=digest(files),versions=evaluation.common.FIRST_VERSIONS,
        train_ids=[r['id'] for r in rows],schedule=learning.schedule(),encodings=encoded,
        optimizer_initialization='fresh AdamW; parent optimizer/RNG deliberately not resumed',
        trainable_names=list(learning.EXPECTED_NAMES),trainable_parameters=learning.PARAMETERS,
        implementation_sha256={n:file_sha(ROOT/n) for n in learning.SOURCES})
    if frozen!=expected or file_sha(a.parent_checkpoint)!=evaluation.PARENT_SHA:
        raise ValueError('Exact CPU-reconstructed authentic SFT admission differs')
    return frozen


def receipts(a,tokenizer):
    prospective=authenticated(a.prospective_admission,a.prospective_sha256)
    frozen=authenticated(a.target_admission,a.target_admission_sha256)
    if frozen!=load(a.generations/'admission.json'):raise ValueError('Collected generation admission differs from authentic receipt')
    if file_sha(a.prompts)!=evaluation.base.PROMPTS_SHA:raise ValueError('Original40 prompt bytes changed')
    original=evaluation.base.greedy.validate_export(load(a.prompts));selected=evaluation.repair.packet(a.repair_packet)
    files=prospective['model_files']
    if digest(files)!=evaluation.common.MODEL_FILES_SHA:raise ValueError('Exact full base model manifest required')
    tokenizer_files(a.tokenizer_path,files)
    phases={}
    for phase,tasks,path in (('greedy40',original,a.baseline_original),('repair2',selected['tasks'],a.baseline_repairs)):
        encoded=[evaluation.common.encode_prompt(tokenizer,t) if phase=='greedy40' else evaluation.repair.encode(tokenizer,t) for t in tasks]
        if any(e['status']!='ready' for e in encoded):raise ValueError('Full matched input context required')
        phases[phase]=dict(tasks=tasks,encodings=encoded,budget=evaluation.BUDGETS[phase],
            baseline=evaluation.baseline(path,phase,tokenizer,tasks),requested=40 if phase=='greedy40' else 2)
    train_frozen=training_admission(a,prospective,tokenizer)
    expected=dict(schema=1,kind='sft_newchild_matched40_and_selected2',phases=phases,
        training_admission=train_frozen,training_admission_sha256=file_sha(a.training_admission),
        model_files=files,model_files_sha256=digest(files),versions=evaluation.common.FIRST_VERSIONS,
        profile=evaluation.train.PROFILE,parent_checkpoint_sha256=evaluation.PARENT_SHA,
        model_max_position_embeddings=load(a.tokenizer_path/'config.json')['max_position_embeddings'],
        eos_token_ids=evaluation.common.EOS_IDS,source_sha256=evaluation.sources(),cpu_environment=evaluation.base.CPU_ENV,
        seconds=evaluation.SECONDS,optimizer_updates=0,verification_pending=True,pooled_pass_at1_claim=False,
        execution_scope='One inference-only worker, one model load; separate1000s/1200s sampling clocks,180s/item; '
            'full admission and model-load overhead share3000s supervisor budget with measured post-admission reserve',
        prospective_only=True)
    if prospective!=expected:raise ValueError('Exact prospective phase/runtime/source receipt differs')
    if expected['model_max_position_embeddings']<9216:raise ValueError('Unmodified actual9216 context capability required')
    import torch
    saved=torch.load(a.child_checkpoint,map_location='cpu',weights_only=False)
    config=evaluation.base.stochastic.checkpoint_state(saved,files)
    target_expected=dict(prospective,prospective_only=False,prospective_sha256=a.prospective_sha256,
        checkpoint_sha256=file_sha(a.child_checkpoint),checkpoint_config_sha256=config,
        training_receipt=frozen['training_receipt'])
    if frozen!=target_expected:raise ValueError('Exact actual child configuration and prospective linkage required')
    return prospective,frozen,train_frozen


def training_linkage(a,frozen,train_frozen,remote):
    receipt=frozen['training_receipt']
    if (receipt['algorithm']!=learning.ALGORITHM or receipt['optimizer_updates']!=84
        or receipt['parent_sha256']!=evaluation.PARENT_SHA or receipt['child_sha256']==evaluation.PARENT_SHA
        or receipt['training_artifacts']!=evaluation.base.inventory(a.training_output)):
        raise ValueError('Actual new SFT84 receipt and complete collected artifacts required')
    summary=learning.validate_output(SimpleNamespace(output=a.training_output,checkpoint=a.parent_checkpoint),train_frozen)
    if digest(summary)!=receipt['validated_summary_sha256']:raise ValueError('CPU training replay differs from authenticated result')
    root=receipt['process_root']
    if not isinstance(root,str) or not Path(root).is_absolute() or '..' in Path(root).parts:
        raise ValueError('Actual absolute training process root required')
    command=[common.PYTHON,str(Path(root)/'tools/proof_sany_repair_learning_train.py'),'worker']
    for name,key in [('input','training_input'),('model_path','model_path'),('checkpoint','parent_checkpoint'),('output','training_output')]:
        command+=['--'+name.replace('_','-'),remote[key]]
    command+=['--expected-input-sha256',train_frozen['input_sha256'],'--admission',str(Path(remote['training_output'])/'admission.json')]
    common.audit_process(load(a.training_output/'process.json'),command,root,learning.BUDGET['seconds'])
    expected=dict(complete=True,summary_sha256=file_sha(a.training_output/'summary.json'),process_sha256=file_sha(a.training_output/'process.json'))
    if load(a.training_output/'admitted.json')!=expected:raise ValueError('Actual training supervisor receipt differs')
    child=file_sha(a.child_checkpoint)
    if child!=summary['checkpoint_sha256'] or child!=receipt['child_sha256'] or child!=file_sha(a.training_output/'policy_optimizer.pt'):
        raise ValueError('Actual collected distinct SFT child checkpoint differs')
    return dict(parent_sha256=evaluation.PARENT_SHA,child_sha256=child,optimizer_updates=84,
        local_cpu_artifact_audit=True,remote_model_admission_rerun_locally=False,
        target_admission_sha256=a.target_admission_sha256,prospective_sha256=a.prospective_sha256,
        validated_training_summary_sha256=digest(summary))


def generation_rows(a,frozen,remote,tokenizer):
    rows=evaluation.validate_worker(frozen,a.generations)
    for phase in evaluation.PHASES:evaluation.validate_rows(frozen,phase,rows[phase],tokenizer)
    worker=load(a.generations/'worker_summary.json');summary=load(a.generations/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];common.finite_budget(pre,evaluation.SECONDS)
    post=evaluation.reserve(pre);seconds=evaluation.SECONDS-pre-post
    if (seconds<=60 or summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds):
        raise ValueError('Actual measured pre/post-admission budget required')
    command=[common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_sany_repair_learning_eval.py'),'worker']
    for name in evaluation.PATHS:command+=['--'+name.replace('_','-'),remote[name]]
    command+=['--expected-input-sha256',frozen['training_admission']['input_sha256'],'--prospective',remote['prospective'],
        '--admission',str(Path(remote['output'])/'admission.json'),'--output',remote['output'],'--worker-seconds',str(seconds)]
    common.audit_process(load(a.generations/'process.json'),command,remote['evaluation_root'],seconds)
    common.finite_budget(worker['elapsed_seconds'],seconds);common.finite_budget(summary['total_seconds'],evaluation.SECONDS)
    extras={'total_seconds','process_sha256','admission_sha256','supervisor_pre_admission_seconds',
            'supervisor_post_admission_reserve_seconds','worker_timeout_seconds'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker
        or summary['process_sha256']!=file_sha(a.generations/'process.json')
        or summary['admission_sha256']!=a.target_admission_sha256):
        raise ValueError('Exact actual generation supervisor linkage required')
    return rows


def prepare(a):
    import transformers
    remote=remote_paths(a.remote_paths)
    original=checks.admit_tasks(load(a.prompts));current=checks.admit_controls(a.controls,original)
    command=[sys.executable,str(Path(checks.__file__).resolve()),'--worker','--prompts',str(a.prompts.resolve()),
             '--output',str((a.controls/'controls').resolve())]
    common.audit_process(load(a.controls/'process.json'),command,str(ROOT),checks.SECONDS)
    chosen=old_repair.bind_tasks(evaluation.repair.packet(a.repair_packet),original)
    tasks=dict(greedy40=original,repair2=chosen)
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    _,frozen,train_frozen=receipts(a,tokenizer)
    linkage=training_linkage(a,frozen,train_frozen,remote)
    parent={phase:load(path/'accounting.json') for phase,path in [('greedy40',a.baseline_original),('repair2',a.baseline_repairs)]}
    arms=dict(parent=parent,child=generation_rows(a,frozen,remote,tokenizer))
    policies=dict(parent=evaluation.PARENT_SHA,child=linkage['child_sha256'])
    paired.validate_inputs(tasks,arms,policies)
    return tasks,arms,policies,current,linkage


def identity(a,tasks):
    files={}
    for name in LOCAL_PATHS:
        path=getattr(a,name)
        for p in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if p.is_file():files[str(p.resolve())]=file_sha(p)
    return dict(files=files,verifier=checks.identity(tasks['greedy40']),sources={n:file_sha(ROOT/n) for n in SOURCES},
        scope='Authenticated prospective and actual target receipts plus exact local artifact replay; not remote model admission')


def verify(a):
    a.output=a.output.resolve()
    for name in LOCAL_PATHS:
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable input/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'summary.json',dict(complete=False,requested_outputs=84,pooled_score=False))
    try:
        initial_original=checks.admit_tasks(load(a.prompts))
        initial_tasks=dict(greedy40=initial_original,
            repair2=old_repair.bind_tasks(evaluation.repair.packet(a.repair_packet),initial_original))
        before=identity(a,initial_tasks);dump(a.output/'identity_before.json',before)
        tasks,arms,policies,current,linkage=prepare(a)
        if tasks!=initial_tasks or identity(a,tasks)!=before:raise ValueError('Input/runtime drift during full local admission')
        frozen=digest(dict(tasks=tasks,arms=arms,policies=policies,current=current,linkage=linkage))
        dump(a.output/'config.json',dict(input_sha256=frozen,limits=paired.LIMITS,training_linkage=linkage,
            original_denominator=40,repair_denominator=2,pooled_score=False))
        rows,summary=paired.evaluate(tasks,arms,policies,current,a.output)
        paired.audit_rows(tasks,arms,policies,rows,current,a.output)
        after=identity(a,tasks);dump(a.output/'identity_after.json',after)
        stable=before==after and frozen==digest(dict(tasks=tasks,arms=arms,policies=policies,current=current,linkage=linkage))
        summary.update(identity_stable=stable,rows_sha256=file_sha(a.output/'rows.json'),training_linkage=linkage)
        summary['complete']=summary['complete'] and stable;dump(a.output/'summary.json',summary)
        if not summary['complete']:raise ValueError('Incomplete matched84 replay; no terminal claim')
        return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),complete=False))
        summary=load(a.output/'summary.json');summary['complete']=False;dump(a.output/'summary.json',summary)
        raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in (*LOCAL_PATHS,'output'):parser.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    parser.add_argument('--prospective-sha256',required=True);parser.add_argument('--target-admission-sha256',required=True)
    print(json.dumps(verify(parser.parse_args())))


if __name__=='__main__':main()
