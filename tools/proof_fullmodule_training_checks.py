"""Bounded fresh TRAIN128 SANY controls only; no semantic/training admission."""
import argparse
import json
import math
from pathlib import Path
import re
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_training_audit as preparation
from tools import proof_fullmodule_sany_checks as common
from harness.proof_owned_process import run_owned,as_runner_tuple

load=preparation.load;dump=common.dump;sha=common.sha;digest=common.digest;file_sha=common.file_sha
AUDIT_ROOT=ROOT/'results/runs/proof-fullmodule-training-audit-20260906-v1'
PINS={'rows.json':'45e00ac7e296b33815bc5f0d8afb52d0c1c83ca24197aa5035a5aa15dc855824',
    'summary.json':'2c1014e1c62f7ef9469e73ed682409a52f7c50d45ab7be4647564cbfe39fae32',
    'protected_evidence.json':'801c2d3a1d20563955d03ea6d09e7c41d610201ba3c8117566da4e27bfc134eb',
    'identity_before.json':'d19df70fa9e926595e74a622a4c62b56e01cd75e5d0e2c9c1420e02ab0c9ce00',
    'identity_after.json':'d19df70fa9e926595e74a622a4c62b56e01cd75e5d0e2c9c1420e02ab0c9ce00'}
SOURCES=tuple(sorted(set(preparation.SOURCES)|set(common.SOURCES)|{'tools/proof_fullmodule_training_checks.py'}))
SECONDS=1800;WORKER_SECONDS=1740;CHECK_SECONDS=30
LABELS=('reference','syntax_negative')
STANDARD_IMPORTS={'FiniteSets','Integers','Naturals','Sequences','TLC'}


def sources():return {name:file_sha(ROOT/name) for name in SOURCES}


def inputs(audit_root):
    audit_root=Path(audit_root).resolve()
    for name,pin in PINS.items():common.checked(audit_root/name,pin)
    before=load(audit_root/'identity_before.json')
    if before!=load(audit_root/'identity_after.json'):raise ValueError('Original preparation identity unstable')
    # Hash-only admission; never reread protected theorem/reference bodies or
    # recompute exclusions from protected evaluation outputs in this wrapper.
    if before['sources']!=preparation.source_identity() or before['inputs']!=preparation.inventory():
        raise ValueError('Preparation source/corpus/tokenizer inventory changed')
    rows=load(audit_root/'rows.json');summary=load(audit_root/'summary.json')
    expected=preparation.summarize(rows,True)
    if any(summary.get(k)!=v for k,v in expected.items()) or summary.get('identity_stable') is not True:
        raise ValueError('Exact complete preparation summary required')
    selected=preparation.candidates()
    for row,original in zip(rows,selected):
        if any(row.get(k)!=v for k,v in original.items()):raise ValueError('Exact raw selected source row changed')
        encoded=row['encoded']
        if encoded['response']!=row['raw']['spec_text'] or encoded['response_sha256']!=sha(encoded['response'].encode()):
            raise ValueError('Target must remain the original entire module')
        if row['sany_status']!='unmeasured':raise ValueError('Historical metadata is not fresh SANY evidence')
    return rows


def staged_tasks(rows,output,*,write=False):
    tasks=[];output=Path(output).resolve()
    if len(rows)!=128 or [r['index'] for r in rows]!=preparation.indices():raise ValueError('All128 ordered candidates required')
    for order,row in enumerate(rows):
        raw=row['raw'];name=raw['module'];text=raw['spec_text']
        if not re.fullmatch(r'[A-Za-z_]\w*',name) or common.runner.module_name(text)!=name:
            raise ValueError('Exact target module name required')
        imports=preparation.exclusion.imports(text)
        if not set(imports)<=STANDARD_IMPORTS:
            raise ValueError('Unadmitted dependency; no guessed corpus/reference staging')
        root=output/'targets'/f'{order:03d}'
        content={name+'.tla':text,'description.txt':raw['nl'],'configuration.cfg':raw['cfg_text']}
        if write:root.mkdir(parents=True,exist_ok=False)
        for filename,body in content.items():
            path=root/filename
            if write:path.write_bytes(body.encode())
            common.checked(path,sha(body.encode()))
        blocked=row['exclusions']['status']!='lexically_clear'
        tasks.append(dict(id=row['id'],index=row['index'],module_name=name,
            source=dict(path=str(root/(name+'.tla')),sha256=sha(text.encode())),dependencies={},
            description=dict(path=str(root/'description.txt'),sha256=sha(raw['nl'].encode())),
            config=dict(path=str(root/'configuration.cfg'),sha256=sha(raw['cfg_text'].encode())),
            standard_imports=imports,raw_selected_sha256=row['raw_sha256'],
            preparation_row_sha256=digest(row),exclusion_status=row['exclusions']['status'],
            training_blocked=blocked,training_blocked_reason='unresolved invariant exclusion' if blocked else 'fresh syntax is not semantic/training admission',
            training_authorized=False))
    return tasks


def blank(tasks):
    return [dict(id=t['id'],index=t['index'],label=label,accepted=False,status='unattempted',sany=None,result=None,
        training_blocked=t['training_blocked']) for t in tasks for label in LABELS]


def negative_accepted(task,candidate,value):
    process=value.get('process') or {};output=process.get('output','')
    module=common.gen_eval.extract_module(candidate)
    if module is None:return False
    lines=module.splitlines();locations=[i+1 for i,line in enumerate(lines) if common.NEGATIVE_NAME+' == )' in line]
    if len(locations)!=1:return False
    return (value.get('sany')==0 and value.get('status')=='model_sany_reject' and
        '***Parse Error***' in output and bool(re.search(r'(?i)Encountered[^\n]*\)',output)) and
        bool(re.search(r'(?i)\bline\s+'+str(locations[0])+r'(?:\s|,)',output)) and
        all(process.get(k) is True for k in ('execution_complete','cleanup_complete','output_complete')))


def accepted(task,label,candidate,value):
    return value['sany']==1 if label=='reference' else negative_accepted(task,candidate,value)


def summarize(tasks,rows,elapsed,identity_stable,execution_complete):
    if [(r['id'],r['index'],r['label']) for r in rows]!=[(t['id'],t['index'],label) for t in tasks for label in LABELS]:
        raise ValueError('All256 original control keys required, including incomplete attempts')
    references=rows[::2];negatives=rows[1::2]
    finite=type(elapsed) in (int,float) and math.isfinite(elapsed) and 0<=elapsed<=WORKER_SECONDS
    measured=all(r['sany'] in (0,1) and r['result'] is not None for r in rows)
    return dict(complete=bool(execution_complete and identity_stable and finite and measured and all(r['accepted'] for r in negatives)),
        requested_candidates=128,requested_controls=256,accounted_controls=len(rows),
        attempted_controls=sum(r['result'] is not None for r in rows),
        target_sany_pass=sum(r['sany']==1 for r in references),target_sany_reject=sum(r['sany']==0 for r in references),
        target_sany_unknown=sum(r['sany'] is None for r in references),
        intended_negative_controls=sum(r['accepted'] for r in negatives),
        unknown_controls=sum(r['sany'] is None for r in rows),all_controls_accepted=all(r['accepted'] for r in rows),
        blocked_candidate_ids=[t['id'] for t in tasks if t['training_blocked']],
        identity_stable=identity_stable,elapsed_seconds=elapsed,syntax_only=True,training_ready=False,
        training_authorized=False,training42_unchanged=True,proof_claim=False,nonvacuity_claim=False,generalization_claim=False)


def snapshot(audit_root,tasks,runtime):
    return dict(audit_files={n:file_sha(Path(audit_root)/n) for n in PINS},sources=sources(),runtime=runtime(tasks))


def worker(a,*,checker=common.check,raw_audit=common.audit,runtime=common.identity,clock=time.monotonic):
    started=clock();source_rows=inputs(a.audit_root);tasks=staged_tasks(source_rows,a.output)
    if load(a.output/'tasks.json')!=tasks:raise ValueError('Staged task ledger changed')
    rows=blank(tasks);dump(a.output/'rows.json',rows)
    dump(a.output/'summary.json',summarize(tasks,rows,0,False,False))
    before=snapshot(a.audit_root,tasks,runtime);dump(a.output/'identity_before.json',before)
    current=before['runtime']
    for order,task in enumerate(tasks):
        source=common.checked(task['source']['path'],task['source']['sha256']).decode()
        for label,candidate in [('reference',source),('syntax_negative',common.negative(source))]:
            if clock()-started>WORKER_SECONDS-60:break
            index=2*order+LABELS.index(label);work=a.output/'checks'/f'{order:03d}'/label
            value=checker(task,candidate,work,current,timeout=CHECK_SECONDS)
            raw_audit(task,candidate,value,work,current)
            rows[index].update(result=value,status=value['status'],sany=value['sany'],accepted=accepted(task,label,candidate,value))
            dump(a.output/'rows.json',rows);dump(a.output/'summary.json',summarize(tasks,rows,clock()-started,False,False))
        if clock()-started>WORKER_SECONDS-60:break
    after=snapshot(a.audit_root,tasks,runtime);dump(a.output/'identity_after.json',after)
    if inputs(a.audit_root)!=source_rows or staged_tasks(source_rows,a.output)!=tasks:raise ValueError('Input/staged source drift')
    summary=summarize(tasks,rows,clock()-started,before==after,True)
    summary['rows_sha256']=file_sha(a.output/'rows.json');dump(a.output/'summary.json',summary)
    return summary


def command(a):return [sys.executable,str(Path(__file__).resolve()),'worker','--audit-root',str(a.audit_root.resolve()),'--output',str(a.output.resolve())]


def audit(a,*,runtime=common.identity):
    source_rows=inputs(a.audit_root);tasks=staged_tasks(source_rows,a.output);rows=load(a.output/'rows.json')
    if load(a.output/'tasks.json')!=tasks:raise ValueError('Exact staged task ledger required')
    current=snapshot(a.audit_root,tasks,runtime)
    if current!=load(a.output/'identity_before.json') or current!=load(a.output/'identity_after.json'):raise ValueError('Current runtime/source identity differs')
    for order,task in enumerate(tasks):
        source=common.checked(task['source']['path'],task['source']['sha256']).decode()
        for j,(label,candidate) in enumerate([('reference',source),('syntax_negative',common.negative(source))]):
            row=rows[2*order+j];value=row['result']
            if value is None:
                if row['sany'] is not None or row['accepted'] is not False:raise ValueError('Unattempted control cannot be measured')
            else:
                common.audit(task,candidate,value,a.output/'checks'/f'{order:03d}'/label,current['runtime'])
                if row['sany']!=value['sany'] or row['status']!=value['status'] or row['accepted']!=accepted(task,label,candidate,value):
                    raise ValueError('Raw control outcome classification changed')
            if row['training_blocked']!=task['training_blocked']:raise ValueError('Unresolved exclusion cannot be unblocked by syntax')
    summary=load(a.output/'summary.json');expected=summarize(tasks,rows,summary['elapsed_seconds'],True,True)
    if summary!=dict(expected,rows_sha256=file_sha(a.output/'rows.json')):raise ValueError('Full raw summary reconstruction differs')
    process=load(a.output/'process.json');rc,_,_,timeout=as_runner_tuple(process)
    if (process['command']!=command(a) or Path(process['cwd']).resolve()!=ROOT or rc!=0 or timeout or
        not all(process.get(k) is True for k in ('execution_complete','cleanup_complete','output_complete')) or
        not math.isfinite(process['seconds']) or not 0<=process['seconds']<=WORKER_SECONDS):raise ValueError('Complete exact owned worker process required')
    return summary


def run(a):
    started=time.monotonic();a.output=a.output.resolve();a.audit_root=a.audit_root.resolve()
    if a.output==a.audit_root or a.output in a.audit_root.parents or a.audit_root in a.output.parents:raise ValueError('Disjoint append-only output required')
    a.output.mkdir(parents=True,exist_ok=False);rows=inputs(a.audit_root);tasks=staged_tasks(rows,a.output,write=True)
    dump(a.output/'tasks.json',tasks);dump(a.output/'rows.json',blank(tasks))
    dump(a.output/'summary.json',summarize(tasks,blank(tasks),0,False,False))
    dump(a.output/'receipt.json',dict(complete=False,requested_candidates=128,requested_controls=256,
        training_ready=False,reason='Supervisor has not admitted owned worker completion'))
    dump(a.output/'config.json',dict(seconds=SECONDS,worker_seconds=WORKER_SECONDS,check_seconds=CHECK_SECONDS,
        requested_candidates=128,requested_controls=256,audit_pins=PINS,sources=sources(),training_authorized=False))
    process=run_owned(command(a),ROOT,WORKER_SECONDS);dump(a.output/'process.json',process)
    summary=audit(a);total=time.monotonic()-started
    receipt=dict(complete=summary['complete'] and total<=SECONDS,total_seconds=total,
        process_sha256=file_sha(a.output/'process.json'),summary_sha256=file_sha(a.output/'summary.json'),training_ready=False)
    dump(a.output/'receipt.json',receipt)
    if not receipt['complete']:raise ValueError('Incomplete controls; no training admission, all keys retained')
    return receipt


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=['run','worker','audit'])
    p.add_argument('--audit-root',type=Path,default=AUDIT_ROOT);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    a.output=a.output.resolve();a.audit_root=a.audit_root.resolve()
    try:print(json.dumps({'run':run,'worker':worker,'audit':audit}[a.mode](a)))
    except BaseException as exc:
        if a.mode!='audit' and a.output.is_dir():
            dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),training_ready=False))
        raise


if __name__=='__main__':main()
