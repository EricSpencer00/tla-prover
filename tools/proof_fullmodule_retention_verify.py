"""Local authenticated SFT338 artifact replay and separate matched40/repair2 checks.

Never invokes target-only model admission locally. Authentic target receipts are
explicitly hash pinned, then inputs, decoding, checkpoint and processes audited.
"""
import argparse
import json
import time
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_retention_eval as evaluation
from tools import proof_fullmodule_learning_verify as lineage
from tools import proof_sany_repair_learning_checks as paired
from tools import proof_sumsequence_proof_rl_verify as common
from tools import proof_sumsequence_sany_repair_verify as old_repair

checks=paired.checks;learning=evaluation.learning
load=evaluation.load;dump=evaluation.dump;digest=evaluation.digest;file_sha=evaluation.file_sha
LOCAL_PATHS=('prompts','repair_packet','tokenizer_path','parent_checkpoint','child_checkpoint',
    'training_input','training_admission','training_output','baseline_combined',
    'prospective_admission','target_admission','generations','remote_paths','controls')+evaluation.learning.PARENT_PATHS
REMOTE_KEYS=set(evaluation.PATHS)|{'output','admission','prospective','evaluation_root'}
SOURCES=tuple(sorted(set(evaluation.SOURCES)|set(checks.SOURCES)|{
    'tools/proof_sany_repair_learning_checks.py','tools/proof_fullmodule_retention_verify.py','tools/proof_fullmodule_learning_verify.py',
    'tools/proof_sumsequence_proof_rl_verify.py','tools/proof_sumsequence_sany_repair_verify.py'}))


PHASES=paired.PHASES;COUNTS=paired.COUNTS;LIMITS=paired.LIMITS;REPAIR_IDS=paired.REPAIR_IDS
sha=evaluation.base.sha


def validate_inputs(tasks, arms, policies):
    if set(tasks) != set(PHASES) or set(arms) != {'parent', 'child'}:
        raise ValueError('Two separate phases and both matched arms required')
    if (set(policies) != {'parent', 'child'} or policies['parent'] != evaluation.PARENT_SHA
            or policies['child'] == evaluation.PARENT_SHA or len(policies['child']) != 64
            or any(c not in '0123456789abcdef' for c in policies['child'])):
        raise ValueError('Actual immutable8866 parent and distinct child required')
    for phase in PHASES:
        ids = [t['id'] for t in tasks[phase]]
        if ids != evaluation.requested_ids(phase) or len(ids) != COUNTS[phase] or len(set(ids)) != len(ids):
            raise ValueError('Complete distinct original task denominator required')
        for arm in arms:
            if set(arms[arm]) != set(PHASES) or [r['id'] for r in arms[arm][phase]] != ids:
                raise ValueError('Exact matched ordered raw outputs required')
    if tuple(t['id'] for t in tasks['repair2']) != REPAIR_IDS:
        raise ValueError('Exact selected two repair targets required')
    original = {t['id']: t for t in tasks['greedy40']}
    if any(t != original.get(t['id']) or t['split'] != 'train' for t in tasks['repair2']):
        raise ValueError('Repairs retain original immutable TRAIN task bindings')


def summarize(rows, complete):
    if len(rows) != 84 or len({(r['arm'], r['phase'], r['id']) for r in rows}) != 84:
        raise ValueError('All84 unique requested keys required')
    if any(r[f] is not None and (type(r[f]) is not int or r[f] not in (0, 1))
           for r in rows for f in ('sany', 'proof')):
        raise ValueError('Only binary or explicitly unknown outcomes allowed')
    result = dict(complete=complete, requested_outputs=84, phases={},
                  original_denominator=40, repair_denominator=2, pooled_score=False,
                  generalization_claim=False, gate_claim=False, training_authorized=False)
    for phase in PHASES:
        entry = dict(requested_per_arm=COUNTS[phase], arms={}, paired={})
        for arm in ('parent', 'child'):
            chosen = [r for r in rows if r['phase'] == phase and r['arm'] == arm]
            if len(chosen) != COUNTS[phase]:
                raise ValueError('Every phase retains its complete denominator')
            entry['arms'][arm] = dict(accounted=len(chosen),
                **{field + suffix: sum(r[field] == value if value is not None else r[field] is None
                                      for r in chosen)
                   for field in ('sany', 'proof')
                   for suffix, value in (('_pass', 1), ('_reject', 0), ('_unknown', None))},
                generation_caps=sum(r['finish_reason'] == 'token_limit' for r in chosen),
                generation_timeouts=sum(r['finish_reason'] == 'time_limit' for r in chosen))
            populations = ({'original_train': chosen[:32], 'original_development': chosen[32:36],
                            'new_train': chosen[36:]} if phase == 'greedy40' else {'selected_train_repairs': chosen})
            entry['arms'][arm]['per_population'] = {
                name: dict(requested=len(group), sany_pass=sum(r['sany'] == 1 for r in group),
                           proof_pass=sum(r['proof'] == 1 for r in group),
                           sany_unknown=sum(r['sany'] is None for r in group),
                           proof_unknown=sum(r['proof'] is None for r in group))
                for name, group in populations.items()}
        for field in ('sany', 'proof'):
            paired = {k: [] for k in ('gains', 'losses', 'unknown', 'unchanged')}
            left = {r['id']: r[field] for r in rows if r['phase'] == phase and r['arm'] == 'parent'}
            right = {r['id']: r[field] for r in rows if r['phase'] == phase and r['arm'] == 'child'}
            if left.keys() != right.keys():
                raise ValueError('Matched phase task identities required')
            for ident, before in left.items():
                after = right[ident]
                label = ('unknown' if before is None or after is None else
                         'gains' if after > before else 'losses' if after < before else 'unchanged')
                paired[label].append(ident)
            entry['paired'][field] = paired
        result['phases'][phase] = entry
    return result


def evaluate(tasks, arms, policies, current, output, *, checker=checks.check, clock=time.monotonic):
    validate_inputs(tasks, arms, policies)
    output = Path(output)
    rows = [dict(arm=arm, phase=phase, id=t['id'], split=t['split'], policy_sha256=policies[arm],
                 raw_row_sha256=digest(raw), finish_reason=raw.get('finish_reason'),
                 sany=None, proof=None, status='unattempted', evidence=None)
            for arm in ('parent', 'child') for phase in PHASES
            for t, raw in zip(tasks[phase], arms[arm][phase])]
    dump(output / 'rows.json', rows)
    complete = True
    by_key = {(r['arm'], r['phase'], r['id']): r for r in rows}
    for arm in ('parent', 'child'):
        for phase in PHASES:
            started = clock()
            for task, raw in zip(tasks[phase], arms[arm][phase]):
                row = by_key[arm, phase, task['id']]
                if raw.get('finish_reason') != 'eos':
                    row['status'] = 'unmeasured_generation'
                elif clock() - started > LIMITS[phase] - 61:
                    row['status'] = 'unmeasured_budget'; complete = False
                else:
                    value = checker(task, raw['raw_reply'], output / 'checks' / arm / phase / task['id'], current)
                    row.update(sany=value['sany'], proof=value['proof'], status=value['status'], evidence=value)
                dump(output / 'rows.json', rows)
                dump(output / 'summary.json', summarize(rows, False))
            if clock() - started > LIMITS[phase]:
                complete = False
    return rows, summarize(rows, complete)


def audit_rows(tasks, arms, policies, rows, current, output):
    validate_inputs(tasks, arms, policies)
    expected = [(arm, phase, t['id']) for arm in ('parent', 'child') for phase in PHASES for t in tasks[phase]]
    if [(r['arm'], r['phase'], r['id']) for r in rows] != expected:
        raise ValueError('Exact complete84 ordered keys required')
    indexed = {(r['arm'], r['phase'], r['id']): r for r in rows}
    for arm in ('parent', 'child'):
        for phase in PHASES:
            for task, raw in zip(tasks[phase], arms[arm][phase]):
                row = indexed[arm, phase, task['id']]
                if (row['policy_sha256'] != policies[arm] or row['split'] != task['split']
                        or row['raw_row_sha256'] != digest(raw) or row['finish_reason'] != raw.get('finish_reason')):
                    raise ValueError('Immutable raw output/policy/task linkage changed')
                if raw.get('finish_reason') != 'eos' or row['status'] == 'unmeasured_budget':
                    if any(row[k] is not None for k in ('sany', 'proof', 'evidence')):
                        raise ValueError('Unknown generation or budget cannot be scored')
                    continue
                value = row['evidence']; extraction = checks.extract(task, raw['raw_reply'])
                if value is None or value['extraction'] != extraction or value['raw_reply_sha256'] != sha(raw['raw_reply'].encode()):
                    raise ValueError('Actual original task extractor/raw reply required')
                if extraction['fragment'] is None:
                    if any(value[k] != v for k, v in dict(sany=0, proof=0, status='model_extraction', evidence=None).items()):
                        raise ValueError('Exact extraction rejection required')
                else:
                    checks.audit_check(task, extraction['fragment'], value['evidence'],
                                       Path(output) / 'checks' / arm / phase / task['id'], current)
                    if any(value[k] != value['evidence'][k] for k in ('sany', 'proof', 'status')):
                        raise ValueError('Raw checker classification differs')
                if any(row[k] != value[k] for k in ('sany', 'proof', 'status')):
                    raise ValueError('Final classification differs from raw checker')


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
    for phase,tasks,path in (('greedy40',original,a.baseline_combined),('repair2',selected['tasks'],a.baseline_combined)):
        encoded=[evaluation.common.encode_prompt(tokenizer,t) if phase=='greedy40' else evaluation.repair.encode(tokenizer,t) for t in tasks]
        if any(e['status']!='ready' for e in encoded):raise ValueError('Full matched input context required')
        phases[phase]=dict(tasks=tasks,encodings=encoded,budget=evaluation.BUDGETS[phase],
            baseline=evaluation.baseline(path,phase,tokenizer,tasks),requested=40 if phase=='greedy40' else 2)
    train_frozen=lineage.training_admission(a,prospective,tokenizer,remote_paths(a.remote_paths))
    if prospective['training_admission']!=train_frozen:raise ValueError('Embedded training admission differs')
    expected=dict(schema=1,kind='train169_child_retention_matched40_and_selected2',phases=phases,
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
    if frozen['checkpoint_sha256']!=a.expected_child_sha256 or frozen['training_receipt']['child_sha256']!=a.expected_child_sha256:raise ValueError('Explicit actual338 child SHA required')
    lineage.policy_map(a)
    if frozen!=target_expected:raise ValueError('Exact actual child configuration and prospective linkage required')
    return prospective,frozen,train_frozen


def generation_rows(a,frozen,remote,tokenizer):
    rows=evaluation.validate_worker(frozen,a.generations)
    for phase in evaluation.PHASES:evaluation.validate_rows(frozen,phase,rows[phase],tokenizer)
    worker=load(a.generations/'worker_summary.json');summary=load(a.generations/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];common.finite_budget(pre,evaluation.SECONDS)
    post=evaluation.reserve(pre);seconds=evaluation.SECONDS-pre-post
    if (seconds<=60 or summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds):
        raise ValueError('Actual measured pre/post-admission budget required')
    command=[common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_fullmodule_retention_eval.py'),'worker']
    for name in evaluation.PATHS:command+=['--'+name.replace('_','-'),remote[name]]
    command+=['--expected-input-sha256',frozen['training_admission']['input_sha256'],'--expected-child-sha256',a.expected_child_sha256,'--prospective',remote['prospective'],
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
    linkage=lineage.training_linkage(a,frozen,tokenizer,remote)
    parent={phase:load(a.baseline_combined/phase/'accounting.json') for phase in evaluation.PHASES}
    arms=dict(parent=parent,child=generation_rows(a,frozen,remote,tokenizer))
    policies=dict(parent=evaluation.PARENT_SHA,child=linkage['child_sha256'])
    validate_inputs(tasks,arms,policies)
    return tasks,arms,policies,current,linkage


def identity(a,tasks):
    files={}
    for name in LOCAL_PATHS:
        path=getattr(a,name)
        for p in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if p.is_file():files[str(p.resolve())]=file_sha(p)
    return dict(files=files,verifier=checks.identity(tasks['greedy40']),sources={n:file_sha(ROOT/n) for n in set(SOURCES)|set(lineage.sources())},
        scope='Authenticated prospective and actual target receipts plus exact local artifact replay; not remote model admission')


def verify(a):
    a.output=a.output.resolve()
    for name in LOCAL_PATHS:
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable input/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'summary.json',dict(complete=False,requested_outputs=84,pooled_score=False))
    dump(a.output/'rows.json',[dict(arm=arm,phase=phase,id=ident,status='unattempted_admission',sany=None,proof=None)
        for arm in ('parent','child') for phase in PHASES for ident in evaluation.requested_ids(phase)])
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
        rows,summary=evaluate(tasks,arms,policies,current,a.output)
        audit_rows(tasks,arms,policies,rows,current,a.output)
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
    parser.add_argument('--expected-input-sha256',required=True);parser.add_argument('--expected-child-sha256',required=True)
    parser.add_argument('--prospective-sha256',required=True);parser.add_argument('--target-admission-sha256',required=True)
    print(json.dumps(verify(parser.parse_args())))


if __name__=='__main__':main()
