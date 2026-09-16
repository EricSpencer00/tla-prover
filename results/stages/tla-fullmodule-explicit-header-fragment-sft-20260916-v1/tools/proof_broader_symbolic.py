#!/usr/bin/env python3
"""Frozen32 source-only symbolic coverage; no DEV, model, optimizer or answers."""
import argparse
import json
from pathlib import Path
import re
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_broader_packet import load_manifests, MANIFEST_SHA256, TRAIN_IDS, MANIFEST6, MANIFEST26
from tools.proof_cuda_eval import sha, digest, dump
from tools.proof_cuda_train import file_sha
from tools.proof_source_scope import top_level_code, named_declarations
from tools.proof_fact_search import proposals
from tools.proof_candidate_coverage import augment
from tools.proof_official_extension import source_aware_candidates
from tools.proof_breadth_manifest import check_dependency
from harness.proof_full_fragment_check import validate_fragment, certify_fragment
from tools.proof_hierarchical_packet import runtime_identity
from harness.runner import TLA_LIBRARY

BUDGET=dict(candidates_per_task=8,timeout=5,seconds=600)
IMPLEMENTATION=('tools/proof_broader_symbolic.py','tools/proof_broader_packet.py',
    'tools/proof_whole_packet.py','tools/proof_source_scope.py','tools/proof_fact_search.py',
    'tools/proof_premise_search.py','tools/proof_candidate_coverage.py','tools/proof_step_candidates.py',
    'tools/proof_official_extension.py','tools/proof_breadth_manifest.py',
    'tools/proof_cuda_eval.py','tools/proof_cuda_train.py','harness/proof_full_fragment_check.py')
FIELDS=('id','prefix','suffix','theorem_name','source_path','source_sha256','dependencies','dependency_sha256')


class BudgetStop(Exception):
    pass


def checked(path,expected):
    raw=Path(path).read_bytes()
    if sha(raw)!=expected:raise ValueError('Source identity changed: '+str(path))
    return raw.decode()


def visible_context(task,roots):
    """Follow EXTENDS only, local frozen dependencies before installed libraries.

    INSTANCE visibility is not flattened. Custom theorem-bearing libraries are
    rejected; standard installed theorem libraries remain explicitly trusted.
    """
    deps={Path(p).stem:Path(p) for p in task['dependencies']}
    if len(deps)!=len(task['dependencies']):raise ValueError('Ambiguous dependency module names')
    texts={str(p):checked(p,task['dependency_sha256'][str(p)]) for p in deps.values()}
    for text in texts.values():check_dependency(text)
    used={};custom=[];libraries=[];seen=set()
    def visit(text,installed=False):
        code=top_level_code(text)
        if re.search(r'\bINSTANCE\b',code) and not installed:raise ValueError('Unsupported INSTANCE visibility')
        for match in re.finditer(r'(?m)^\s*EXTENDS\s+(\w+(?:[ \t]*,[ \t\r\n]*\w+)*)',code):
            for name in re.findall(r'\w+',match[1]):
                if name in seen:continue
                seen.add(name)
                path=deps.get(name) or next((Path(r)/(name+'.tla') for r in roots if (Path(r)/(name+'.tla')).is_file()),None)
                if path is None:
                    if name in {'Naturals','Integers','Reals','Sequences'}:continue
                    raise ValueError('Unresolved visible module: '+name)
                raw=path.read_bytes();body=raw.decode();used[str(path)]=sha(raw)
                if name in deps:
                    if sha(raw)!=task['dependency_sha256'][str(path)]:raise ValueError('Dependency changed')
                    custom.append(body)
                else:libraries.append(body)
                # Installed-library INSTANCE exports are not enumerated; only
                # its directly named exported statements and EXTENDS are used.
                visit(body,installed=name not in deps)
    visit(task['prefix'])
    return custom,libraries,used


def candidates_for(task,roots):
    validate_fragment(task['prefix'],'OBVIOUS',task['suffix'],task['theorem_name'])
    declarations=[d for d in named_declarations(task['prefix']) if d.name==task['theorem_name']]
    if len(declarations)!=1:raise ValueError('Unique immutable target required')
    goal=task['prefix'][declarations[0].body_start:]
    dependencies,libraries,hashes=visible_context(task,roots)
    choices,facts=proposals(task['prefix'],task['theorem_name'],goal,dependencies,libraries)
    choices,visible=source_aware_candidates(choices,[task['prefix'],*dependencies,*libraries])
    choices,steps=augment(dict(task,candidates=choices[:8],context=dict(library_sha256=hashes)),limit=8)
    for choice in choices:validate_fragment(task['prefix'],choice,task['suffix'],task['theorem_name'])
    return dict(candidates=choices,candidate_sha256=[sha(c.encode()) for c in choices],
        target_goal=goal,library_sha256=hashes,statement_context=facts,step_context=steps,
        smt_visible=visible,reference_fragment_used=False)


def prepare():
    manifests=load_manifests()
    # Immediately discard all nonallowlisted fields; no target proof is read by proposals.
    tasks=[{k:t[k] for k in FIELDS} for population in ('original6','broader26')
           for t in manifests[population]['tasks'] if t['split']=='train']
    del manifests
    if [t['id'] for t in tasks]!=TRAIN_IDS:raise ValueError('Exact32 TRAIN required')
    for task in tasks:
        checked(task['source_path'],task['source_sha256'])
        task.update(prefix_sha256=sha(task['prefix'].encode()),suffix_sha256=sha(task['suffix'].encode()))
        if set(task['dependencies'])!=set(task['dependency_sha256']):raise ValueError('Dependency hash coverage')
        for path,expected in task['dependency_sha256'].items():checked(path,expected)
        try:task.update(candidates_for(task,TLA_LIBRARY.split(':')),preparation_status='ready')
        except ValueError as exc:
            task.update(candidates=[],candidate_sha256=[],library_sha256={},preparation_status='unsupported',reason=str(exc))
    return tasks


def source_identity(tasks):
    paths={ROOT/p for p in IMPLEMENTATION}|{MANIFEST6,MANIFEST26}
    for task in tasks:
        paths.add(Path(task['source_path']))
        paths.update(Path(p) for p in task['dependencies'])
        paths.update(Path(p) for p in task['library_sha256'])
    result={str(p):file_sha(p) for p in sorted(paths)}
    for task in tasks:
        expected={task['source_path']:task['source_sha256'],**task['dependency_sha256'],**task['library_sha256']}
        if any(result[str(Path(p))]!=h for p,h in expected.items()):raise ValueError('Pinned source/dependency/library hash changed')
    return result


def admitted(task,fragment,result):
    expected={Path(p).name:h for p,h in task['dependency_sha256'].items()}
    command=result.get('command',[])
    return (result.get('certified') is True and result.get('status')=='pass'
        and result.get('returncode')==0 and result.get('timed_out') is False
        and result.get('contract_version')=='full-proof-fragment-v1'
        and '--strict' in command and '--nofp' in command
        and result.get('sha256')==sha((task['prefix']+fragment+task['suffix']).encode())
        and result.get('dependency_sha256')==expected
        and type(result.get('total')) is int and result['total']>0
        and result.get('proved')==result['total'])


def evaluate(tasks,output,*,checker=certify_fragment,identity=runtime_identity,source_check=source_identity,clock=time.monotonic):
    if [t['id'] for t in tasks]!=TRAIN_IDS:raise ValueError('Exact32 TRAIN denominator required')
    frozen=digest(tasks)
    for task in tasks:
        if len(task['candidates'])>8 or task['candidate_sha256']!=[sha(c.encode()) for c in task['candidates']]:
            raise ValueError('Candidate budget/hash mismatch')
    before=identity();sources=source_check(tasks);started=clock();attempts=[]
    if (output/'config.json').exists():
        config=json.loads((output/'config.json').read_bytes())
        if config.get('source_identity')!=sources or config.get('frozen_sha256')!=frozen:
            raise ValueError('Preparation snapshot changed before evaluation')
    dump(output/'verifier_before.json',before)
    outcomes={t['id']:dict(id=t['id'],certified=False,attempts=0,status='unattempted' if t['candidates'] else 'unsupported') for t in tasks}
    stable=True;termination='complete'
    def save():
        rows=list(outcomes.values())
        dump(output/'outcomes.json',rows)
        summary=dict(**BUDGET,manifest_sha256=MANIFEST_SHA256,requested_tasks=32,
            attempted_tasks=sum(r['attempts']>0 for r in rows),certified_tasks=sum(r['certified'] for r in rows),
            checker_attempts=len(attempts),termination=termination,identity_stable=stable,
            elapsed_seconds=clock()-started,reference_fragment_used=False,parameter_updates=0,
            method='source-only symbolic whole-proof coverage; not model or heldout performance',
            per_population={name:dict(requested_tasks=len(ids),attempted_tasks=sum(outcomes[i]['attempts']>0 for i in ids),
                certified_tasks=sum(outcomes[i]['certified'] for i in ids)) for name,ids in
                [('original6',TRAIN_IDS[:6]),('new26',TRAIN_IDS[6:])]},source_identity=sources)
        dump(output/'summary.json',summary)
        return summary
    save()
    try:
        with (output/'checks.jsonl').open('x') as stream:
            for index in range(8):
                for task in tasks:
                    outcome=outcomes[task['id']]
                    if outcome['certified'] or index>=len(task['candidates']):continue
                    if clock()-started>595:
                        termination='time_budget'
                        raise BudgetStop
                    if source_check(tasks)!=sources or digest(tasks)!=frozen:raise ValueError('Frozen source/candidate drift')
                    fragment=task['candidates'][index]
                    result=checker(task['prefix'],fragment,task['suffix'],theorem_name=task['theorem_name'],
                        dependencies=tuple(map(Path,task['dependencies'])),timeout=5,
                        work_root=output/'checks'/task['id']/str(index))
                    positive=admitted(task,fragment,result)
                    row=dict(result,task=task['id'],candidate_index=index,fragment=fragment,
                             candidate_sha256=sha(fragment.encode()),certified=positive)
                    attempts.append(row);stream.write(json.dumps(row)+'\n');stream.flush()
                    outcome.update(attempts=outcome['attempts']+1,certified=positive,status='pass' if positive else result.get('status','unknown'))
                    if source_check(tasks)!=sources:raise ValueError('Source changed during check')
                    save()
    except BudgetStop:
        pass
    except Exception:
        stable=False;termination='execution_error'
        raise
    finally:
        try:
            after=identity();dump(output/'verifier_after.json',after)
            stable=stable and before==after and source_check(tasks)==sources and digest(tasks)==frozen
        except Exception:
            stable=False
        if not stable:
            termination='identity_or_execution_failure'
            for outcome in outcomes.values():outcome.update(certified=False,status='invalidated')
        save()
    return save()


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    tasks=prepare();a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'frozen.json',tasks)
    dump(a.output/'config.json',dict(**BUDGET,manifest_sha256=MANIFEST_SHA256,frozen_sha256=digest(tasks),
        requested_tasks=32,reference_fragment_used=False,source_identity=source_identity(tasks)))
    for name in IMPLEMENTATION:
        path=a.output/'code'/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((ROOT/name).read_bytes())
    for task in tasks:
        for path,expected in {**task['dependency_sha256'],**task['library_sha256']}.items():
            raw=Path(path).read_bytes()
            if sha(raw)!=expected:raise ValueError('Dependency/library changed before snapshot')
            snapshot=a.output/'sources'/expected/Path(path).name
            snapshot.parent.mkdir(parents=True,exist_ok=True);snapshot.write_bytes(raw)
    if not a.prepare_only:
        result=evaluate(tasks,a.output)
        if not result['identity_stable']:raise SystemExit(1)


if __name__=='__main__':main()
