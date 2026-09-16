"""Local matched greedy40 proof-RL retention replay; never remote model admission."""
import argparse
import json
import math
from pathlib import Path
import sys
import time
from types import SimpleNamespace
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_proof_rl_eval as evaluation
from tools import proof_sumsequence_proof_rl_checks as checks
from tools.proof_cuda_train import file_sha,dump
from tools.proof_cuda_eval import digest
from harness.proof_owned_process import as_runner_tuple

SECONDS_PER_ARM=2500
PYTHON='/home/eric-spencer/ChatTLA/.venv/bin/python'
LOCAL_PATHS=('prompts','tokenizer_path','parent_checkpoint','child_checkpoint','training_output',
    'training_inputs','training_rollouts','baseline_cycle','generations','target_admission','remote_paths','controls')
REMOTE_KEYS=set(evaluation.INPUTS)|{'output','admission','baseline_remote_root','baseline_remote_parent','evaluation_root'}
SOURCES=tuple(sorted(set(evaluation.SOURCES)|set(checks.SOURCES)|{'tools/proof_sumsequence_proof_rl_verify.py'}))


def load(path):return json.loads(Path(path).read_bytes())


def finite_budget(value,limit):
    if type(value) not in (int,float) or not math.isfinite(value) or not 0<value<=limit:
        raise ValueError('Finite positive actual bounded duration required')


def remote_paths(a):
    paths=load(a.remote_paths)
    if set(paths)!=REMOTE_KEYS or any(not isinstance(v,str) or not Path(v).is_absolute() or str(Path(v))!=v for v in paths.values()):
        raise ValueError('Observed exact absolute remote path manifest required')
    return paths


def audit_process(process,command,cwd,budget):
    rc,_,seconds,timeout=as_runner_tuple(process)
    if process['command']!=command or process['cwd']!=cwd or rc!=0 or timeout:
        raise ValueError('Exact complete owned process command/cwd required')
    finite_budget(seconds,budget)


def training_linkage(a,frozen,remote):
    training=evaluation.training;receipt=frozen['training_receipt']
    paths=load(a.training_inputs)
    if (set(paths)!=set(training.PATHS) or any(not isinstance(v,str) or not Path(v).is_absolute() for v in paths.values()) or
        file_sha(a.training_inputs)!=receipt['training_inputs_sha256'] or
        file_sha(a.parent_checkpoint)!=evaluation.PARENT_SHA or receipt['parent_sha256']!=evaluation.PARENT_SHA or
        receipt['optimizer_updates']!=1 or paths['model_path']!=remote['model_path']):
        raise ValueError('Authentic training input receipt and exact24d5 parent required')
    if evaluation.inventory(a.training_output)!=receipt['training_artifacts']:
        raise ValueError('Complete collected training byte inventory differs from target receipt')
    admitted=load(a.training_output/'admission.json')
    if (digest(admitted)!=receipt['training_admission_sha256'] or admitted['training_authorized'] is not True or
        admitted['budget']!=training.packet.BUDGET or
        admitted['implementation_sha256']!={n:file_sha(ROOT/n) for n in training.packet.SOURCES}):
        raise ValueError('Exact frozen training admission/source contract required')
    # This is a CPU artifact replay, NOT training.admit/evaluation.admit. Their
    # actual target-host admission is authenticated by the explicit receipt pin.
    local=SimpleNamespace(output=a.training_output,checkpoint=a.parent_checkpoint,rollouts=a.training_rollouts)
    worker=training.validate_output(local,admitted)
    if digest(worker)!=receipt['validated_worker_sha256']:raise ValueError('Locally audited training worker differs from target receipt')
    summary=load(a.training_output/'summary.json');process=load(a.training_output/'process.json')
    root=receipt['training_process_root'];source=str(Path(root)/'tools/proof_sumsequence_proof_rl_train.py')
    if receipt['training_process_source_sha256']!=file_sha(ROOT/'tools/proof_sumsequence_proof_rl_train.py'):
        raise ValueError('Actual original training worker source changed')
    command=[PYTHON,source,'worker']
    for key in training.PATHS:command+=['--'+key.replace('_','-'),paths[key]]
    command+=['--output',remote['training_output'],'--admission',str(Path(remote['training_output'])/'admission.json'),'--worker-seconds']
    if process['command'][:-1]!=command:raise ValueError('Original training command must remain unrewritten')
    seconds=float(process['command'][-1]);finite_budget(seconds,900)
    if seconds<=training.CHECKPOINT_RESERVE:raise ValueError('Training checkpoint reserve absent')
    audit_process(process,command+[process['command'][-1]],root,seconds)
    if ({k:v for k,v in summary.items() if k not in ('total_seconds','process_sha256')}!=worker or
        summary['process_sha256']!=file_sha(a.training_output/'process.json')):
        raise ValueError('Original complete training supervisor linkage required')
    finite_budget(summary['total_seconds'],900)
    child=file_sha(a.child_checkpoint)
    if child!=receipt['child_sha256'] or child!=worker['checkpoint_sha256'] or child!=file_sha(a.training_output/'policy_optimizer.pt'):
        raise ValueError('Actual locally collected one-update child checkpoint required')
    return dict(parent_sha256=evaluation.PARENT_SHA,child_sha256=child,optimizer_updates=1,
        local_cpu_artifact_audit=True,remote_model_admission_rerun_locally=False,
        target_admission_sha256=file_sha(a.target_admission),training_worker_sha256=digest(worker))


def target_admission(a,remote,tokenizer):
    import torch
    if file_sha(a.target_admission)!=a.target_admission_sha256:
        raise ValueError('Explicit authentic target-host receipt hash required')
    frozen=load(a.target_admission)
    if frozen!=load(a.generations/'admission.json'):raise ValueError('Target and generated admissions differ')
    args=SimpleNamespace(prompts=a.prompts,evaluation='greedy40',arm='child')
    expected=evaluation.packet(args,file_sha(a.child_checkpoint))
    if (frozen['evaluation']!=expected or frozen['source_sha256']!=evaluation.source_identity() or
        frozen['checkpoint_sha256']!=file_sha(a.child_checkpoint) or
        frozen['model_files_sha256']!=evaluation.common.MODEL_FILES_SHA or digest(frozen['model_files'])!=evaluation.common.MODEL_FILES_SHA or
        frozen['versions']!=evaluation.common.FIRST_VERSIONS or frozen['profile']!=evaluation.train.PROFILE or
        frozen['eos_token_ids']!=evaluation.common.EOS_IDS or frozen['cpu_environment']!=evaluation.CPU_ENV or
        frozen['optimizer_updates']!=0 or frozen['verification_pending'] is not True or frozen['generalization_claim'] is not False):
        raise ValueError('Exact target model/runtime/source/evaluation receipt required')
    saved=torch.load(a.child_checkpoint,map_location='cpu',weights_only=False)
    if evaluation.stochastic.checkpoint_state(saved,frozen['model_files'])!=frozen['checkpoint_config_sha256']:
        raise ValueError('Actual child checkpoint configuration differs from target receipt')
    expected_files={n:h for n,h in frozen['model_files'].items() if n.endswith('.json') or n in ('tokenizer.model','chat_template.jinja')}
    actual={p.name:file_sha(p) for p in a.tokenizer_path.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))}
    if expected_files!=actual:raise ValueError('Exact complete local tokenizer file inventory required')
    if frozen['encodings']!=[evaluation.common.encode_prompt(tokenizer,t) for t in expected['tasks']]:
        raise ValueError('Actual local tokenizer input reconstruction differs from target')
    return frozen


def generation_rows(a,frozen,remote,tokenizer):
    rows=load(a.generations/'accounting.json');evaluation.validate_rows(frozen,rows,tokenizer)
    worker=load(a.generations/'worker_summary.json');evaluation.validate_worker_summary(frozen,rows,worker,a.generations)
    summary=load(a.generations/'summary.json');process=load(a.generations/'process.json')
    command=[PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_sumsequence_proof_rl_eval.py'),'worker']
    for key in evaluation.INPUTS:command+=['--'+key.replace('_','-'),remote[key]]
    command+=['--baseline-remote-root',remote['baseline_remote_root'],'--baseline-remote-parent',remote['baseline_remote_parent'],
        '--evaluation','greedy40','--arm','child','--admission',str(Path(remote['output'])/'admission.json'),
        '--output',remote['output'],'--worker-seconds']
    if process['command'][:-1]!=command:raise ValueError('Exact observed target generation command required')
    seconds=float(process['command'][-1]);finite_budget(seconds,1000)
    if seconds<=30:raise ValueError('Generation post-admission reserve absent')
    audit_process(process,command+[process['command'][-1]],remote['evaluation_root'],seconds)
    finite_budget(worker['elapsed_seconds'],seconds);finite_budget(summary['total_seconds'],1000)
    if ({k:v for k,v in summary.items() if k not in ('total_seconds','process_sha256','admission_sha256','historical_baseline')}!=worker or
        summary['process_sha256']!=file_sha(a.generations/'process.json') or summary['admission_sha256']!=a.target_admission_sha256 or
        summary['historical_baseline']!=frozen['historical_baseline']):raise ValueError('Complete target generation supervisor receipt required')
    return rows


def prepare(a):
    import transformers
    remote=remote_paths(a);tasks=checks.admit_tasks(load(a.prompts));current=checks.admit_controls(a.controls,tasks)
    # Bind the actual outer control CLI too, in addition to its individual raw
    # SANY and strict process audits performed by the immutable adapter.
    process=load(a.controls/'process.json')
    control_command=[sys.executable,str(Path(checks.__file__).resolve()),'--worker','--prompts',str(a.prompts.resolve()),
                     '--output',str((a.controls/'controls').resolve())]
    audit_process(process,control_command,str(ROOT),checks.SECONDS)
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    frozen=target_admission(a,remote,tokenizer);linkage=training_linkage(a,frozen,remote)
    baseline_args=SimpleNamespace(baseline_cycle=a.baseline_cycle,prompts=a.prompts,model_path=Path(remote['model_path']),
        baseline_remote_root=remote['baseline_remote_root'],baseline_remote_parent=remote['baseline_remote_parent'])
    old=evaluation.baseline(baseline_args,tokenizer,frozen['evaluation']['tasks'],tokenizer_path=a.tokenizer_path)
    if old!=frozen['historical_baseline'] or old['original_role']!='child' or old['policy_sha256']!=evaluation.PARENT_SHA:
        raise ValueError('Authentic historical24d5 child baseline required; do not relabel its original run')
    parent=load(a.baseline_cycle/'child/accounting.json')
    child=generation_rows(a,frozen,remote,tokenizer)
    if [r['id'] for r in parent]!=[r['id'] for r in child]:raise ValueError('Exact paired40 ordering required')
    return tasks,dict(parent=parent,child=child),current,linkage


def identity(a,tasks):
    files={}
    for name in LOCAL_PATHS:
        path=getattr(a,name)
        for item in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if item.is_file():files[str(item.resolve())]=file_sha(item)
    return dict(verifier=checks.identity(tasks),files=files,sources={n:file_sha(ROOT/n) for n in SOURCES},
                scope='Target receipt plus local exact CPU artifact/tokenizer/raw-check audit; no local remote-model admission')


def summarize(rows,tasks,complete):
    populations=dict(original_train=[t['id'] for t in tasks[:32]],original_development=[t['id'] for t in tasks[32:36]],
                     new_train=[t['id'] for t in tasks[36:]])
    result=dict(complete=complete,requested_per_arm=40,populations=populations,arms={},paired={},
        scope='Matched greedy pass@1 on known TRAIN32/DEV4/newTRAIN4; historical baseline retains original child provenance; not unseen generalization, not TLC')
    for arm in ('parent','child'):
        group=[r for r in rows if r['arm']==arm]
        def counts(items):return dict(requested=len(items),sany_pass=sum(r['sany']==1 for r in items),
            proof_pass=sum(r['proof']==1 for r in items),sany_unknown=sum(r['sany'] is None for r in items),
            proof_unknown=sum(r['proof'] is None for r in items),
            generation_cap=sum(r.get('finish_reason')=='token_limit' for r in items),
            generation_timeout=sum(r.get('finish_reason')=='time_limit' for r in items))
        result['arms'][arm]=dict(**counts(group),per_population={n:counts([r for r in group if r['id'] in ids]) for n,ids in populations.items()})
    for field in ('sany','proof'):
        paired=[]
        for task in tasks:
            pair={r['arm']:r for r in rows if r['id']==task['id']}
            before=pair['parent'][field];after=pair['child'][field]
            paired.append(dict(id=task['id'],parent=before,child=after,transition='unknown' if before is None or after is None
                else 'gain' if after>before else 'loss' if after<before else 'unchanged'))
        result['paired'][field]=dict(rows=paired,gains=[r['id'] for r in paired if r['transition']=='gain'],
            losses=[r['id'] for r in paired if r['transition']=='loss'],unknown=[r['id'] for r in paired if r['transition']=='unknown'])
    return result


def evaluate(tasks,arms,current,output,*,checker=checks.check,clock=time.monotonic):
    if len(tasks)!=40 or set(arms)!={'parent','child'} or any([r['id'] for r in arms[arm]]!=[t['id'] for t in tasks] for arm in arms):
        raise ValueError('Exactly matched ordered40 per arm required')
    output=Path(output);rows=[dict(arm=arm,id=t['id'],split=t['split'],sany=None,proof=None,status='unattempted',
        original_generation_role='child',finish_reason=raw.get('finish_reason'),raw_row_sha256=digest(raw),evidence=None)
        for arm in ('parent','child') for t,raw in zip(tasks,arms[arm])]
    dump(output/'rows.json',rows);complete=True
    for arm_index,arm in enumerate(('parent','child')):
        started=clock()
        for index,(task,raw) in enumerate(zip(tasks,arms[arm])):
            row=rows[40*arm_index+index]
            if raw.get('finish_reason')!='eos':row['status']='unmeasured_generation'
            elif clock()-started>SECONDS_PER_ARM-61:row['status']='unmeasured_budget';complete=False
            else:
                value=checker(task,raw['raw_reply'],output/'checks'/arm/task['id'],current)
                row.update(sany=value['sany'],proof=value['proof'],status=value['status'],evidence=value)
            dump(output/'rows.json',rows);dump(output/'summary.json',summarize(rows,tasks,False))
        if clock()-started>SECONDS_PER_ARM:complete=False
    return rows,summarize(rows,tasks,complete)


def audit_rows(tasks,arms,rows,current,output):
    expected=[(arm,t['id']) for arm in ('parent','child') for t in tasks]
    if [(r['arm'],r['id']) for r in rows]!=expected:raise ValueError('Exact final80 raw result keys required')
    for arm_index,arm in enumerate(('parent','child')):
        for index,(task,raw) in enumerate(zip(tasks,arms[arm])):
            row=rows[arm_index*40+index]
            if row['raw_row_sha256']!=digest(raw) or row['finish_reason']!=raw.get('finish_reason') or row['original_generation_role']!='child':
                raise ValueError('Original generation provenance changed')
            if raw.get('finish_reason')!='eos' or row['status']=='unmeasured_budget':
                if row['sany'] is not None or row['proof'] is not None or row['evidence'] is not None:
                    raise ValueError('Incomplete/unattempted generation cannot be measured')
                continue
            value=row['evidence'];extraction=checks.extract(task,raw['raw_reply'])
            if value is None or value['extraction']!=extraction or value['raw_reply_sha256']!=checks.sha(raw['raw_reply'].encode()):
                raise ValueError('Actual extraction/reply evidence changed')
            if extraction['fragment'] is None:
                if value['sany']!=0 or value['proof']!=0 or value['status']!='model_extraction' or value['evidence'] is not None:
                    raise ValueError('Exact model extraction rejection required')
            else:
                checks.audit_check(task,extraction['fragment'],value['evidence'],Path(output)/'checks'/arm/task['id'],current)
                if any(value[k]!=value['evidence'][k] for k in ('sany','proof','status')):
                    raise ValueError('Pipeline wrapper differs from raw checker result')
            if any(row[k]!=value[k] for k in ('sany','proof','status')):
                raise ValueError('Raw checker classification differs from final row')


def verify(a):
    a.output=a.output.resolve()
    for name in LOCAL_PATHS:
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable inputs and verification output required')
    a.output.mkdir(parents=True,exist_ok=False)
    expected_tasks=checks.admit_tasks(load(a.prompts));before=identity(a,expected_tasks)
    dump(a.output/'identity_before.json',before)
    tasks,arms,current,linkage=prepare(a)
    if tasks!=expected_tasks or identity(a,tasks)!=before:raise ValueError('Input identity changed during admission')
    dump(a.output/'config.json',dict(seconds_per_arm=SECONDS_PER_ARM,requested_per_arm=40,training_linkage=linkage,
        target_admission_sha256=a.target_admission_sha256,original_baseline_role='child',replayed_baseline_label='parent',
        method='Exact same current SANY+strict checks; EOS-only, no retries, no pooled success'))
    rows,summary=evaluate(tasks,arms,current,a.output)
    audit_rows(tasks,arms,rows,current,a.output)
    after=identity(a,tasks);dump(a.output/'identity_after.json',after)
    if before!=after:
        summary['complete']=False;summary['identity_stable']=False;dump(a.output/'summary.json',summary)
        raise ValueError('Verification identities changed; no completed comparison admitted')
    summary.update(identity_stable=True,rows_sha256=file_sha(a.output/'rows.json'),training_linkage=linkage)
    dump(a.output/'summary.json',summary)
    if not summary['complete']:raise ValueError('Verification budget incomplete; all80 requested rows preserved')
    return summary


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in (*LOCAL_PATHS,'output'):parser.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    parser.add_argument('--target-admission-sha256',required=True);a=parser.parse_args()
    print(json.dumps(verify(a)))


if __name__=='__main__':main()
