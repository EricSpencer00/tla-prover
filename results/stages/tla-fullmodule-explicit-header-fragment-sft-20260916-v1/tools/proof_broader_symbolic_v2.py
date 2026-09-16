#!/usr/bin/env python3
"""Local-premise-first fixed-budget ablation; original symbolic runtime unchanged."""
import argparse
import json
from pathlib import Path
import re
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_broader_symbolic as base
from tools.proof_broader_symbolic import (BUDGET, TRAIN_IDS, MANIFEST_SHA256, BudgetStop,
    sha, digest, dump, file_sha, certify_fragment, runtime_identity, admitted, validate_fragment)
from tools.proof_fact_search import tokens, statements
from tools.proof_premise_search import candidates as definition_candidates
from tools.proof_source_scope import top_level_code, named_declarations

BASE_SHA='e4cd385e6f7a3693792ff5ba0b05413d1e4606df7a43ee320397fe56b8b073a8'
IMPLEMENTATION=tuple(dict.fromkeys(('tools/proof_broader_symbolic_v2.py',*base.IMPLEMENTATION,
    'tools/proof_hierarchical_packet.py','harness/proof_fragment_check.py','harness/runner.py',
    'tools/proof_candidate_rl.py','tools/proof_sequence_train.py','tools/proof_repair_pilot.py',
    'tools/proof_candidate_rank.py','tools/proof_family_manifest.py','tools/proof_original18.py')))
UNSUPPORTED={'breadth-Barriers-LockExclusion':'Unsupported INSTANCE visibility',
    **{'breadth26-tcp_proof-'+name:'Unresolved visible module: TLC' for name in
       ('NetworkType','PrefixOneNonEmpty','PrefixTwoNonEmpty')}}


def source_identity(tasks):
    if file_sha(ROOT/'tools/proof_broader_symbolic.py')!=BASE_SHA:
        raise ValueError('Frozen original symbolic implementation changed')
    return {**base.source_identity(tasks),
            **{str(ROOT/p):file_sha(ROOT/p) for p in IMPLEMENTATION}}


def candidate_pool(task,roots):
    """Only immutable prefix and actually imported source statements/definitions."""
    validate_fragment(task['prefix'],'OBVIOUS',task['suffix'],task['theorem_name'])
    targets=[d for d in named_declarations(task['prefix']) if d.name==task['theorem_name']]
    if len(targets)!=1:raise ValueError('Unique target required')
    goal=task['prefix'][targets[0].body_start:]
    dependencies,libraries,hashes=base.visible_context(task,roots)
    local=statements(task['prefix'],task['theorem_name'])+[
        f for text in dependencies for f in statements(text,task['theorem_name'],exported=True)]
    query=tokens(goal)
    relevant=[f for f in local if query & tokens(f['statement'])]
    expanded=query|set().union(*(tokens(f['statement']) for f in relevant))
    imported=[f for text in libraries for f in statements(text,exported=True)]
    def score(f):
        ts=tokens(f['statement'])
        return (4*len(query&ts)+len(expanded&ts))/(len(ts)+4)**.5
    ranked=sorted((f for f in imported if score(f)>0),key=lambda f:(-score(f),f['name']))
    names=list(dict.fromkeys(f['name'] for f in relevant))
    all_defs=next((c[len('BY SMT DEF '):].split(', ') for c in
        definition_candidates(task['prefix'],dependencies) if c.startswith('BY SMT DEF ')),[])
    goal_words=set(re.findall(r'[A-Za-z_]\w*',top_level_code(goal)))
    defs=[name for name in all_defs if name in goal_words]
    proposed=['BY SMT']
    def add(facts,definitions=(),backend=True):
        if not facts and not definitions:return
        candidate='BY '+', '.join((['SMT'] if backend else [])+list(facts))
        if definitions:candidate+=(' DEF ' if facts or backend else 'DEF ')+', '.join(definitions)
        proposed.append(candidate)
    # Reserve source-local options before any imported theorem can consume slots.
    add(names);add(names,defs);add([],defs)
    add(names,backend=False);add(names,defs,backend=False);add([],defs,backend=False)
    for count in (1,2,4):
        group=list(dict.fromkeys(names+[f['name'] for f in ranked[:count]]))
        if not ranked:break
        add(group);add(group,defs);add(group,backend=False)
    # Generic all-definition fallbacks remain available when local slots are empty.
    proposed.extend(list(__import__('itertools').islice(definition_candidates(task['prefix'],dependencies),3)))
    choices,visible=base.source_aware_candidates(proposed,[task['prefix'],*dependencies,*libraries])
    choices=choices[:8]
    for choice in choices:validate_fragment(task['prefix'],choice,task['suffix'],task['theorem_name'])
    return dict(candidates=choices,candidate_sha256=[sha(c.encode()) for c in choices],
        target_goal=goal,library_sha256=hashes,smt_visible=visible,
        candidate_strategy='local-only, local plus goal-mentioned DEF, positive-relevance imports; deterministic eight slots',
        statement_context=dict(visible_facts=local,relevant_local_facts=relevant,
            ranked_imported_facts=ranked,goal_relevant_definitions=defs),
        zero_relevance_imports_omitted=sum(score(f)==0 for f in imported),
        reference_fragment_used=False,step_context=dict(status='unsupported',
            reason='no hierarchical proof step at insertion point',proposed_steps=[]))


def prepare():
    if file_sha(ROOT/'tools/proof_broader_symbolic.py')!=BASE_SHA:raise ValueError('Frozen original changed')
    tasks=base.prepare()
    unsupported={t['id']:t['reason'] for t in tasks if t['preparation_status']!='ready'}
    if unsupported!=UNSUPPORTED:raise ValueError('Ablation requires identical28 ready and4 unsupported')
    for task in tasks:
        task['baseline_candidate_sha256']=task['candidate_sha256']
        if task['preparation_status']=='ready':
            task.update(candidate_pool(task,base.TLA_LIBRARY.split(':')))
    return tasks

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
    stable=True;termination='running';verification_complete=False
    def save():
        rows=list(outcomes.values())
        dump(output/'outcomes.json',rows)
        summary=dict(**BUDGET,manifest_sha256=MANIFEST_SHA256,requested_tasks=32,
            attempted_tasks=sum(r['attempts']>0 for r in rows),certified_tasks=sum(r['certified'] for r in rows),
            checker_attempts=len(attempts),termination=termination,identity_stable=stable,
            verification_complete=verification_complete,
            status_counts={s:sum(r['status']==s for r in rows) for s in sorted({r['status'] for r in rows})},
            elapsed_seconds=clock()-started,reference_fragment_used=False,parameter_updates=0,
            method='local-premise-first symbolic ordering ablation; five-second coverage, not matched30s model verification',
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
                    status=('pass' if positive else 'timeout' if result.get('timed_out') is True
                        else result.get('status') if result.get('status') in {'contract_reject','verifier_reject'} else 'unknown')
                    row=dict(result,task=task['id'],candidate_index=index,fragment=fragment,
                             candidate_sha256=sha(fragment.encode()),certified=positive)
                    attempts.append(row);stream.write(json.dumps(row)+'\n');stream.flush()
                    outcome.update(attempts=outcome['attempts']+1,certified=positive,status=status)
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
        if stable:
            verification_complete=True
            if termination=='running':termination='complete'
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

