"""Fail-closed local strict replay of matched parent40/SFT80/child40 artifacts."""
import argparse
import json
import re
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_repair_eval as policy,proof_sumsequence_repair_train as train
from tools import proof_sumsequence_repair_cycle as cycle,proof_sumsequence_policy_verify as seq
from tools import proof_token_rl_stochastic_tlaps as strict
from tools.proof_cuda_eval import dump,digest,sha
from tools.proof_cuda_train import file_sha
from harness.proof_owned_process import run_owned,as_runner_tuple
from harness.proof_gen import extract_proof_block
from harness import runner,proof_full_fragment_check as full,proof_fragment_check as legacy
from tools.proof_outcome_audit import classify_outcome

PYTHON='/home/eric-spencer/ChatTLA/.venv/bin/python'
FREEZE_SHA='f11f9cb1934689aa7c9b521cac817a184283cd9917995f79ae37224a74c32319'
PROMPTS_SHA='ba368c52f14d77fff14c55ad66275a6d0ab79a1d3088163a924b851f63fcc360'
SOURCES=tuple(sorted(set(cycle.source_identity())|set(seq.SOURCES)|{
    'tools/proof_sumsequence_repair_verify.py','harness/proof_gen.py','harness/proof_fragment_check.py'}))


def load(path):return json.loads(Path(path).read_bytes())


def process_ok(process,command,cwd,budget):
    rc,_,seconds,timeout=as_runner_tuple(process)
    if process['command']!=command or process['cwd']!=str(cwd) or rc!=0 or timeout or not 0<=seconds<=budget:
        raise ValueError('Exact complete owned process linkage required')


def contexts(tasks):
    """Actual references exercise extractors before any model-error handling."""
    result=[]
    for index,task in enumerate(tasks):
        if index<36:
            context=task;fragment=extract_proof_block(task['reference_fragment'])
        else:
            context=seq.extraction_context(task)
            fragment=seq.extract(task['reference_fragment'],context)['fragment']
        if fragment is None or fragment.strip()!=task['reference_fragment'].strip():
            raise ValueError('Actual reference extractor control failed: '+task['id'])
        (full.validate_fragment if task['split']=='train' else legacy.validate_fragment)(
            task['prefix'],fragment,task['suffix'],task['theorem_name'])
        result.append(context)
    return result


def validate_arm(a,role,expected,tasks,tokenizer):
    root=a.generations/role;admission=load(root/'admission.json');summary=load(root/'summary.json')
    policy.checkpoint_role(role,expected)
    if (admission['role']!=role or admission['checkpoint_sha256']!=expected or
        admission['prompts_sha256']!=file_sha(a.prompts) or admission['budget']!=policy.BUDGET or
        admission['implementation_sha256']!=policy.sources() or
        admission['versions']!=policy.common.FIRST_VERSIONS or
        admission['model_files_sha256']!=policy.common.MODEL_FILES_SHA or
        digest(admission['model_files'])!=policy.common.MODEL_FILES_SHA or
        admission['profile']!=policy.common.BUDGET['profile'] or
        admission['eos_token_ids']!=policy.common.EOS_IDS or admission['optimizer_updates']!=0 or
        admission['cpu_environment']!=policy.CPU_ENV):
        raise ValueError('Exact model/source/checkpoint admission required')
    expected_files={n:h for n,h in admission['model_files'].items() if n.endswith('.json') or n in {'tokenizer.model','chat_template.jinja'}}
    actual={p.name:file_sha(p) for p in a.tokenizer_path.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in {'tokenizer.model','chat_template.jinja'})}
    if expected_files!=actual:raise ValueError('Exact complete tokenizer files required')
    encoded=[policy.common.encode_prompt(tokenizer,t) for t in tasks]
    if admission['input_evidence']!=encoded:raise ValueError('Complete40 exact input evidence required')
    raw=(root/'generations.jsonl').read_bytes()
    if not raw.endswith(b'\n'):raise ValueError('Truncated generation ledger')
    rows=[json.loads(line) for line in raw.splitlines()];policy.validate_rows(admission,rows,complete=True)
    for row in rows:
        if row.get('status') not in ('generated','generation_time_limit') or policy.common.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
            raise ValueError('Exact generated token/reply reconstruction required')
    if load(root/'accounting.json')!=rows:raise ValueError('Complete generation/accounting mismatch')
    remote=Path(a.remote_root);base=remote/'results/cycle';checkpoint=a.remote_parent if role=='parent' else str(base/'training/policy_optimizer.pt')
    command=[PYTHON,str(remote/'tools/proof_sumsequence_repair_eval.py'),'worker','--role',role,
        '--expected-input-sha256',file_sha(a.prompts),'--expected-checkpoint-sha256',expected,
        '--prompts',str(remote/'prompts.json'),'--model-path',a.remote_model,'--checkpoint',checkpoint,
        '--admission',str(base/role/'admission.json'),'--output',str(base/role)]
    process_ok(load(root/'process.json'),command,remote,1000)
    runtime=load(root/'runtime.json');policy.memory_guard(runtime['allocated'],runtime['reserved'])
    if (runtime.get('optimizer_updates')!=0 or runtime.get('restore_exact') is not True or
        runtime.get('weights_unchanged') is not True or runtime.get('cpu_threads')!=4 or
        summary.get('complete') is not True or summary.get('role')!=role or
        summary.get('checkpoint_sha256')!=expected or summary.get('requested_tasks')!=40 or
        summary.get('accounted_tasks')!=40 or summary.get('generated_rows')!=40 or
        summary.get('unattempted_ids')!=[] or summary.get('optimizer_updates')!=0 or
        summary.get('full_admission_stable') is not True or summary.get('memory_guard_passed') is not True or
        summary.get('accounting_sha256')!=file_sha(root/'accounting.json') or
        summary.get('process_sha256')!=file_sha(root/'process.json') or
        summary.get('returncode')!=0 or summary.get('timed_out') is not False or
        not 0<summary.get('worker_timeout_seconds',float('inf'))<=1000 or
        summary.get('eos_complete')!=sum(r['finish_reason']=='eos' for r in rows) or
        not 0<=summary.get('phase_seconds',float('inf'))<=1000):
        raise ValueError('Raw no-update complete40 generation evidence required')
    return dict(rows=rows,admission=admission,summary=summary)


def prepare(a):
    import transformers
    if file_sha(a.prompts)!=PROMPTS_SHA or file_sha(a.generations/'freeze.json')!=FREEZE_SHA:
        raise ValueError('Exact submitted cycle freeze/prompts required')
    if not all(Path(p).is_absolute() for p in (a.remote_root,a.remote_model,a.remote_parent)):
        raise ValueError('Observed absolute remote paths required')
    original,old=policy.broader.export_tasks();new,fresh=policy.extra.export_tasks()
    packet=load(a.prompts);portable=policy.validate_export(packet)
    if json.loads(packet['original_packet_bytes'])!=original or json.loads(packet['new_packet_bytes'])!=new:
        raise ValueError('Exact locally controlled populations required')
    tasks=old+fresh;context=contexts(tasks)
    if file_sha(a.parent_checkpoint)!=policy.PARENT_SHA:raise ValueError('Immutable collected parent required')
    frozen=load(a.generations/'freeze.json')
    if frozen['sources']!=cycle.source_identity() or frozen['prompts_sha']!=file_sha(a.prompts) or frozen['seconds']!=cycle.SECONDS:
        raise ValueError('Current complete frozen cycle source/input identity required')
    training_admission=load(a.generations/'training/admission.json')
    if training_admission!=frozen['training'] or training_admission['implementation_sha256']!={n:file_sha(ROOT/n) for n in train.SOURCES}:
        raise ValueError('Exact frozen training admission required')
    if training_admission['input_sha256']!=frozen['train_sha'] or file_sha(a.generations/'training/train.json')!=frozen['train_sha']:
        raise ValueError('Submitted training packet bytes changed')
    trained=train.validate_training(a.generations/'training',training_admission,a.parent_checkpoint)
    receipt=cycle.validate_training_receipt(a.generations/'training',trained)
    remote=Path(a.remote_root);base=remote/'results/cycle'
    cycle_command=[PYTHON,str(remote/'tools/proof_sumsequence_repair_cycle.py'),'_run',
        '--train-sha',frozen['train_sha'],'--prompts-sha',frozen['prompts_sha'],
        '--input',str(remote/'train.json'),'--prompts',str(remote/'prompts.json'),
        '--model-path',a.remote_model,'--checkpoint',a.remote_parent,'--output',str(base),
        '--freeze',str(base/'freeze.json')]
    process_ok(load(a.generations/'cycle_process.json'),cycle_command,remote,cycle.SECONDS)
    command=[PYTHON,str(remote/'tools/proof_sumsequence_repair_train.py'),'worker',
        '--input',str(remote/'train.json'),'--model-path',a.remote_model,'--checkpoint',a.remote_parent,
        '--output',str(base/'training'),'--expected-input-sha256',frozen['train_sha'],
        '--admission',str(base/'training/admission.json')]
    process_ok(load(a.generations/'training/process.json'),command,remote,900)
    linkage=load(a.generations/'training-linkage.json')
    if (linkage.get('validated') is not True or linkage['child_checkpoint_sha256']!=trained['checkpoint_sha256'] or
        linkage['parent_checkpoint_sha256']!=policy.PARENT_SHA or
        linkage['training_admitted_sha256']!=file_sha(a.generations/'training/admitted.json')):
        raise ValueError('Exact validated80step child linkage required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    training_rows=train.packet_rows((a.generations/'training/train.json').read_bytes())
    if [train.helpers.encode_row(tokenizer,r,8192) for r in training_rows]!=training_admission['encodings']:
        raise ValueError('Actual local training tokenizer reconstruction differs from frozen admission')
    arms={role:validate_arm(a,role,expected,portable,tokenizer) for role,expected in
        [('parent',policy.PARENT_SHA),('child',trained['checkpoint_sha256'])]}
    if arms['parent']['admission']!=frozen['parent']:
        raise ValueError('Original frozen parent admission changed')
    state=load(a.generations/'summary.json')
    if (state.get('complete') is not True or state.get('training')!=trained or state.get('training_admission')!=receipt or
        state.get('requested_parent')!=40 or state.get('requested_child')!=40 or state.get('requested_updates')!=80 or
        state.get('phase')!='evaluated_pending_proof_checks' or
        state.get('unattempted_task_ids')!={'parent':[],'child':[]}):
        raise ValueError('Complete original cycle and training summary required')
    for role in arms:
        if state[role]!=arms[role]['summary'] or load(a.generations/(role+'-admission.json'))!=arms[role]['admission']:
            raise ValueError('Cycle arm linkage changed')
    return tasks,context,arms


def identity(a,tasks):
    from tools.proof_hierarchical_packet import runtime_identity
    paths=[a.prompts,a.parent_checkpoint]+[p for p in a.generations.rglob('*') if p.is_file()]
    paths += [p for p in a.tokenizer_path.iterdir() if p.is_file()]
    paths += [p for p in a.controls.rglob('*') if p.is_file()]
    for t in tasks:paths += [Path(t['source_path'])]+list(map(Path,t['dependencies']))
    return dict(runtime=runtime_identity(),sources={n:file_sha(ROOT/n) for n in SOURCES},
        inputs={str(p.resolve()):file_sha(p) for p in paths},tasks_sha256=digest(tasks))


def original_worker(input_path,output):
    payload=load(input_path);task=payload['task'];output.mkdir(parents=True,exist_ok=False)
    for path,h in task['dependency_sha256'].items():strict.checked(path,h)
    strict.checked(task['source_path'],task['source_sha256'])
    previous=runner.run_cmd
    def command(cmd,cwd,timeout):
        process=run_owned(cmd,cwd,timeout);dump(Path(cwd)/'owned_process.json',process)
        return as_runner_tuple(process)
    runner.run_cmd=command
    try:
        checker=full.certify_fragment if task['split']=='train' else legacy.certify_fragment
        result=checker(task['prefix'],payload['fragment'],task['suffix'],theorem_name=task['theorem_name'],
            dependencies=tuple(map(Path,task['dependencies'])),work_root=output/'check',timeout=28.5)
        dump(output/'result.json',result)
    finally:runner.run_cmd=previous


def audit_original(task,fragment,record):
    if task['split']=='train':return strict.audit_strict(task,fragment,record)
    work=Path(record['workdir']);expected=dict(prefix=task['prefix'],fragment=fragment,suffix=task['suffix'],theorem_name=task['theorem_name'])
    if (load(work/'input.json')!=expected or load(work/'result.json')!=record or
        (work/'tlapm.log').read_text()!=record['output'] or record['sha256']!=sha((task['prefix']+fragment+task['suffix']).encode())):
        raise ValueError('Exact legacy-repair raw input/result required')
    if record.get('command'):
        path=Path(record['candidate_path']);strict.checked(path,record['sha256'])
        deps={Path(p).name:h for p,h in task['dependency_sha256'].items()}
        if path.parent!=work or record['dependency_sha256']!=deps:raise ValueError('Legacy dependency/candidate scope changed')
        for name,h in deps.items():strict.checked(work/name,h)
        cmd=[str(runner.TLAPM),'--strict','--nofp','--cache-dir',str(work/'.tlacache')]
        for library in runner.TLA_LIBRARY.split(':'):cmd+=['-I',library]
        cmd.append(path.name);process=load(work/'owned_process.json')
        if record['command']!=cmd or process['command']!=cmd or process['cwd']!=str(work) or as_runner_tuple(process)!=tuple(record[k] for k in ('returncode','output','seconds','timed_out')):
            raise ValueError('Strict legacy owned process mismatch')
        if legacy.classify_result(record['returncode'],record['output'],record['timed_out'])!=(record['status'],record['proved'],record['total']):
            raise ValueError('Legacy raw classification mismatch')
    return classify_outcome(record,provenance_verified=True)


def check_original(task,fragment,work,timeout=30):
    work=work.resolve();work.mkdir(parents=True,exist_ok=False);payload=dict(task=task,fragment=fragment)
    dump(work/'input.json',payload)
    cmd=[sys.executable,str(Path(__file__).resolve()),'worker','--input',str(work/'input.json'),'--output',str(work/'worker')]
    process=run_owned(cmd,work,30);dump(work/'process.json',process)
    if load(work/'process.json')!=process or load(work/'input.json')!=payload or process['command']!=cmd or process['cwd']!=str(work):
        raise ValueError('Raw dedicated original checker mismatch')
    rc,_,seconds,timed_out=as_runner_tuple(process)
    result=dict(certified=False,measured_model_outcome=False,classification='unmeasured_infrastructure',process=process)
    if rc==0 and not timed_out and seconds<=30:
        record=load(work/'worker/result.json');diagnostic=audit_original(task,fragment,record)
        result.update(strict=record,classification=diagnostic['classification'],
            measured_model_outcome=diagnostic['measured_model_outcome'],certified=diagnostic['classification']=='proof_success')
    return result


def control_tasks():
    from tools.proof_breadth26_manifest import wrong_conclusion
    tasks=policy.broader.combined_tasks(policy.broader.load_manifests())
    contexts(tasks+policy.extra.static_tasks())
    train_task,dev=tasks[0],tasks[32]
    if dev['id']!='crdt-type-step':raise ValueError('Exact legacy control target required')
    # Preserve the top-level theorem and the step's antecedent/local assumptions.
    match=re.search(r"=> TypeOK'(?P<trailing>\s*)\Z",dev['prefix'])
    if match is None:raise ValueError('Exact legacy implication conclusion required')
    negative_dev=dev['prefix'][:match.start()]+'=> FALSE'+match.group('trailing')
    return [(train_task,dict(train_task,prefix=wrong_conclusion(train_task))),
            (dev,dict(dev,prefix=negative_dev))]


def control_identity():
    from tools.proof_hierarchical_packet import runtime_identity
    return dict(runtime=runtime_identity(),sources={n:file_sha(ROOT/n) for n in SOURCES},
        tasks_sha256=digest(control_tasks()))


def negative_control_pass(task,result):
    from tools.proof_sumsequence_controls import intended_false_failure
    if task['split']=='train':return intended_false_failure(result)
    # This legacy hole is an implication step: preserve its TypeOK/Next
    # antecedent, and require that exact FALSE-consequent obligation to fail.
    text=result.get('output','')
    return (task['id']=='crdt-type-step' and result.get('certified') is False and
        result.get('status')=='verifier_reject' and result.get('returncode')==10 and
        result.get('timed_out') is False and
        len(re.findall(r'\[ERROR\]: Could not prove or check:',text))==1 and
        re.findall(r'\[ERROR\]: (\d+)/(\d+) obligations failed\.',text)==[('1','6')] and
        re.search(r'(?m)^\s*PROVE\s+TypeOK /\\ \[Next\]_vars => FALSE\s*$',text) is not None and
        re.search(r'(?i)parse|syntax|unknown operator|not found|exception|cannot find|could not load|segmentation|out of memory',text) is None)


def integration_controls(output):
    from tools.proof_sumsequence_controls import intended_false_failure
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    before=control_identity();dump(output/'identity_before.json',before);rows=[];started=time.monotonic()
    dump(output/'summary.json',dict(complete=False,requested=4,reference_extractor_controls=40))
    for good,bad in control_tasks():
        for label,task in [('reference',good),('false_conclusion',bad)]:
            if time.monotonic()-started>130:raise TimeoutError('Fixed160s controls budget exhausted')
            result=check_original(task,task['reference_fragment'],output/'checks'/task['id']/label)
            accepted=result['certified'] if label=='reference' else ('strict' in result and negative_control_pass(task,result['strict']))
            rows.append(dict(id=task['id'],split=task['split'],label=label,task=task,result=result,accepted=accepted))
            dump(output/'rows.json',rows)
    after=control_identity();dump(output/'identity_after.json',after)
    summary=dict(complete=before==after and all(r['accepted'] for r in rows) and time.monotonic()-started<=160,requested=4,accounted=len(rows),
        accepted=sum(r['accepted'] for r in rows),reference_extractor_controls=40,
        rows_sha256=file_sha(output/'rows.json'),elapsed_seconds=time.monotonic()-started)
    dump(output/'summary.json',summary)
    if not summary['complete']:raise ValueError('Actual full/legacy integration controls not admitted')
    return summary


def admit_integration_controls(directory):
    from tools.proof_sumsequence_controls import intended_false_failure
    current=control_identity();summary=load(directory/'summary.json');rows=load(directory/'rows.json')
    if (summary.get('complete') is not True or summary.get('accepted')!=4 or summary.get('accounted')!=4 or
        summary.get('requested')!=4 or not 0<=summary.get('elapsed_seconds',float('inf'))<=160 or
        summary.get('reference_extractor_controls')!=40 or len(rows)!=4 or
        summary.get('rows_sha256')!=file_sha(directory/'rows.json') or
        load(directory/'identity_before.json')!=current or load(directory/'identity_after.json')!=current):
        raise ValueError('Current actual full/legacy integration controls required')
    expected=[(label,t) for good,bad in control_tasks() for label,t in [('reference',good),('false_conclusion',bad)]]
    for row,(label,task) in zip(rows,expected):
        result=row['result'];record=result['strict'];work=Path(record['workdir']).parents[2]
        if row['task']!=task or row['label']!=label or row['id']!=task['id'] or row['accepted'] is not True:
            raise ValueError('Exact control inputs/order required')
        diagnostic=audit_original(task,task['reference_fragment'],record)
        if (result['classification']!=diagnostic['classification'] or
            result['measured_model_outcome']!=diagnostic['measured_model_outcome'] or
            result['certified']!=(diagnostic['classification']=='proof_success')):
            raise ValueError('Stored control verdict disagrees with raw diagnostic')
        outer=load(work/'process.json')
        cmd=[sys.executable,str(Path(__file__).resolve()),'worker','--input',str(work/'input.json'),'--output',str(work/'worker')]
        process_ok(outer,cmd,work,30)
        if outer!=result['process'] or load(work/'input.json')!=dict(task=task,fragment=task['reference_fragment']):
            raise ValueError('Control raw outer process/input mismatch')
        if not (diagnostic['classification']=='proof_success' if label=='reference' else negative_control_pass(task,record)):
            raise ValueError('Intended strict control outcome missing')
    return current


def evaluate(a,*,clock=time.monotonic):
    a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=False)
    ids=list(policy.broader.TRAIN_IDS)+list(policy.broader.DEV_IDS)+list(policy.extra.TRAIN_IDS)
    rows=[dict(arm=arm,id=key,population='original_train' if i<32 else 'original_development' if i<36 else 'new_train',
        fragment_contract='legacy-repair' if 32<=i<36 else 'full-proof-fragment-v1',
        certified=False,measured=False,status='unmeasured_pending') for arm in ('parent','child') for i,key in enumerate(ids)]
    def save(complete=False):
        dump(a.output/'rows.json',rows)
        summary=dict(complete=complete,requested_samples=80,generalization_claim=False,gate_claim=False,
            per_arm={arm:{pop:dict(requested=n,certified=sum(r['certified'] for r in rows if r['arm']==arm and r['population']==pop) if complete else 0,
                measured=sum(r['measured'] for r in rows if r['arm']==arm and r['population']==pop),
                unknown=n-sum(r['measured'] for r in rows if r['arm']==arm and r['population']==pop))
                for pop,n in [('original_train',32),('original_development',4),('new_train',4)]} for arm in ('parent','child')})
        dump(a.output/'summary.json',summary);return summary
    save()
    try:
        admit_integration_controls(a.controls)
        tasks,context,arms=prepare(a);before=identity(a,tasks);dump(a.output/'identity_before.json',before)
        dump(a.output/'config.json',dict(timeout=30,seconds_per_arm=1250,
            original_extractor='unchanged extract_proof_block',new_extractor='unchanged SumSequence extraction_context/extract',
            original_contracts='TRAIN full-proof-fragment-v1; DEV legacy-repair',
            budget='30s outer,28.5s inner,0.5s cleanup; both arms matched',reference_extractor_controls=40))
        frozen=digest(dict(tasks=tasks,context=context,arms=arms))
        for arm in ('parent','child'):
            started=clock()
            for i,task in enumerate(tasks):
                r=rows[(0 if arm=='parent' else 40)+i];generated=arms[arm]['rows'][i]
                r['status']='unmeasured_generation'
                if generated['finish_reason']!='eos':continue
                fragment=extract_proof_block(generated['raw_reply']) if i<36 else seq.extract(generated['raw_reply'],context[i])['fragment']
                r.update(fragment=fragment,raw_reply_sha256=generated['raw_reply_sha256'])
                if fragment is None:r.update(status='model_extraction',measured=True)
                elif clock()-started>1220:r['status']='unmeasured_budget'
                else:
                    work=a.output/'checks'/arm/task['id']
                    result=check_original(task,fragment,work) if i<36 else strict.check(task,fragment,work,30)
                    if i>=36:seq.audit_result(task,fragment,result,work)
                    r.update(certified=result['certified'],measured=result['measured_model_outcome'],status=result['classification'],evidence=result)
                save()
        after=identity(a,tasks);dump(a.output/'identity_after.json',after)
        if before!=after or frozen!=digest(dict(tasks=tasks,context=context,arms=arms)):
            raise ValueError('Frozen replay input or verifier identity changed')
        return save(True)
    except BaseException as exc:
        save(False);dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)));raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('evaluate','worker','controls'))
    for name in ('input','output','prompts','generations','tokenizer-path','parent-checkpoint','controls'):p.add_argument('--'+name,type=Path)
    for name in ('remote-root','remote-parent','remote-model'):p.add_argument('--'+name)
    a=p.parse_args()
    if a.mode=='worker':original_worker(a.input,a.output)
    elif a.mode=='controls':print(json.dumps(integration_controls(a.output)))
    else:print(json.dumps(evaluate(a)))


if __name__=='__main__':main()
