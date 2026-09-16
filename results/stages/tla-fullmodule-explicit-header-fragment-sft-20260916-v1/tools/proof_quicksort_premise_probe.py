"""Bounded symbolic premise augmentation of one exact TRAIN proof; never model output."""
import argparse
from dataclasses import asdict
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_proof_rl_checks as checks
from tools.proof_source_scope import named_declarations,top_level_code

ID='breadth26-Quicksort-PermsOfPermsOf'
MANIFEST=ROOT/'results/runs/proof-breadth26-controls-20260905-v1/manifest.json'
MANIFEST_SHA='fa9891e67e8c099e2956d5d9f78a29780f186c132a6446d0ed02e5dc89487526'
ORIGINAL=ROOT/'results/runs/proof-sany-repair-learning-verified-20260906-v1/checks/child/greedy40'/ID/'tlaps/input.json'
ORIGINAL_SHA='e5a179b6c0c585a96109c65fad5d20ab164072935560d07af47b23a4d9a16d81'
MODEL_FRAGMENT='BY PermsOfLemma DEF PermsOf'
CANDIDATES=(
 ('add_composition_fact','BY PermsOfLemma, AutomorphismsCompose DEF PermsOf'),
 ('expand_composition_definitions','BY PermsOfLemma DEF PermsOf, Automorphisms, **'),
 ('add_fact_and_expand_definitions','BY PermsOfLemma, AutomorphismsCompose DEF PermsOf, Automorphisms, **'))
SECONDS=420


def load(path):return json.loads(Path(path).read_bytes())


def prepare():
    manifest=json.loads(checks.checked(MANIFEST,MANIFEST_SHA))
    selected=[t for t in manifest['tasks'] if t['id']==ID]
    if len(selected)!=1:raise ValueError('Exact single TRAIN task required')
    task=selected[0]
    original=json.loads(checks.checked(ORIGINAL,ORIGINAL_SHA))
    if original!=dict(task=task,fragment=MODEL_FRAGMENT) or task['split']!='train' or task['dependencies']:
        raise ValueError('Exact immutable saved TRAIN model candidate required')
    raw=checks.checked(task['source_path'],task['source_sha256']).decode()
    assembly=task['prefix']+task['reference_fragment']+task['suffix']
    if checks.sha(assembly.encode())!=task['assembled_sha256']:
        raise ValueError('Actual original reference assembly changed')
    # Both cited named facts retain their actual source statements AND proofs.
    if not raw.startswith(task['prefix']+task['reference_fragment']):
        raise ValueError('Actual preceding source proof bytes must be preserved')
    declarations=named_declarations(task['prefix'])
    names=[d.name for d in declarations]
    if names!=['ValAssump','AutomorphismsCompose','PermsOfLemma','PermsOfPermsOf']:
        raise ValueError('Exact visible module fact scope required')
    by_name={d.name:d for d in declarations}
    scope=[]
    for name,next_name,proof in [('AutomorphismsCompose','PermsOfLemma','BY DEF Automorphisms, **'),
            ('PermsOfLemma','PermsOfPermsOf','BY DOMAIN t = DOMAIN s DEF PermsOf, Automorphisms, **')]:
        d=by_name[name];section=task['prefix'][d.start:by_name[next_name].start]
        if d.kind!='LEMMA' or proof not in section or name not in top_level_code(section):
            raise ValueError('Actually visible proof-bearing prerequisite required')
        scope.append(dict(name=name,header=asdict(d),exact_statement_and_proof=section,
                          sha256=checks.sha(section.encode())))
    for path,pin in task['standard_library_sha256'].items():
        if not path.startswith('tlapm-builtin:'):checks.checked(path,pin)
    for _,fragment in CANDIDATES:
        checks.full.validate_fragment(task['prefix'],fragment,task['suffix'],task['theorem_name'])
        if fragment==task['reference_fragment'].strip():raise ValueError('Search cannot relabel the reference as generated')
    negative=checks.negative_task(task)
    before_assume=task['prefix'][task['goal_offsets'][0]:].split('PROVE',1)[0]
    after_assume=negative['prefix'][task['goal_offsets'][0]:].split('PROVE',1)[0]
    if before_assume!=after_assume:raise ValueError('FALSE control must preserve exact ASSUME/NEW bindings')
    return task,negative,dict(visible_facts=scope,standard_library_sha256=task['standard_library_sha256'],
        source_sha256=task['source_sha256'],source_commit=task['source_commit'],custom_dependencies=[],
        trust='Existing frozen standard-library trust only; both newly cited module facts are actually proved in the full reference control',
        original_model_fragment=MODEL_FRAGMENT,original_candidate_input_sha256=ORIGINAL_SHA,
        search_variants_model_generated=False,training_authorized=False)


def identity(task):
    return dict(checker=checks.identity([task]),own_source_sha256=checks.file_sha(Path(__file__)),
                manifest_sha256=checks.file_sha(MANIFEST),original_input_sha256=checks.file_sha(ORIGINAL))


def run(output,*,checker=checks.check_fragment,auditor=checks.audit_check,identify=identity,clock=time.monotonic):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    started=clock();task,negative,scope=prepare();before=identify(task);current=before['checker']
    checks.dump(output/'config.json',dict(task=task,negative_task=negative,scope=scope,candidates=CANDIDATES,
        hypothesis='Explicitly exposing actual visible composition facts/definitions repairs the missing-premise proof obligation',
        method='Three ordered symbolic augmentations of exact saved model BY; no resampling, no oracle-output relabel',
        controls=2,requested_candidates=3,maximum_checks=5,sany_seconds=30,strict_seconds=30,total_seconds=SECONDS,
        stop='Both actual reference and assumption-preserving FALSE controls must pass before all three bounded candidates',
        model_generated_claim=False,training_authorized=False,old_scores_unchanged=True))
    checks.dump(output/'identity_before.json',before);rows=[];controls_ok=False
    def execute(name,target,fragment,kind):
        if clock()-started>SECONDS-61:return None
        work=output/'checks'/name
        value=checker(target,fragment,work,current);auditor(target,fragment,value,work,current)
        row=dict(name=name,kind=kind,fragment=fragment,task_sha256=checks.digest(target),result=value,
            model_generated=False,training_authorized=False)
        if kind=='reference_control':row['accepted']=value['sany']==1 and value['proof']==1 and value['status']=='proof_success'
        elif kind=='false_control':row['accepted']=checks.intended_negative(target,value)
        rows.append(row);checks.dump(output/'rows.json',rows);return row
    try:
        good=execute('reference',task,task['reference_fragment'],'reference_control')
        bad=execute('false_conclusion',negative,task['reference_fragment'],'false_control')
        controls_ok=good is not None and bad is not None and good['accepted'] and bad['accepted']
        checks.dump(output/'controls.json',dict(admitted=bool(controls_ok),requested=2,rows=rows[:2],scope=scope))
        if controls_ok:
            for name,fragment in CANDIDATES:
                execute(name,task,fragment,'symbolic_premise_search')
        after=identify(task);checks.dump(output/'identity_after.json',after)
        stable=before==after;elapsed=clock()-started
        candidates=[r for r in rows if r['kind']=='symbolic_premise_search']
        summary=dict(complete=stable and elapsed<=SECONDS and controls_ok and len(candidates)==3,
            controls_admitted=bool(controls_ok),requested_controls=2,requested_candidates=3,attempted_candidates=len(candidates),
            candidates=[dict(name=name,attempted=any(r['name']==name for r in candidates),
                status=next((r['result']['status'] for r in candidates if r['name']==name),'unattempted'),
                sany=next((r['result']['sany'] for r in candidates if r['name']==name),None),
                proof=next((r['result']['proof'] for r in candidates if r['name']==name),None)) for name,_ in CANDIDATES],
            verified_symbolic_proofs=sum(r['result']['proof']==1 for r in candidates),identity_stable=stable,
            elapsed_seconds=elapsed,model_generated_claim=False,training_authorized=False,old_scores_unchanged=True,
            scope='Single known TRAIN target premise-search diagnostic; not model learning, holdout, TLC, or generalization')
        checks.dump(output/'summary.json',summary)
        if not stable:raise ValueError('Source/control/runtime identity drift')
        return summary
    except BaseException as exc:
        checks.dump(output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),complete=False))
        raise


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    print(json.dumps(run(parser.parse_args().output)))
