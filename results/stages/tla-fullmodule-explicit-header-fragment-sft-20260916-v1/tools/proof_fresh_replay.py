#!/usr/bin/env python3
"""Post-hoc paired extraction replay; same frozen outputs, no model or training."""
import argparse
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_fresh_eval import validate_run,CHECKPOINT_SHA,IMPLEMENTATION as GENERATION_SOURCES
from tools.proof_cuda_eval import sha,digest,dump,read_rows,validate_tokenization,decode_reply
from tools.proof_cuda_train import file_sha
from tools.proof_fresh_packet import export_tasks
from tools.proof_hierarchical_packet import runtime_identity
from tools.proof_whole_packet import TOKENIZER,TOKENIZER_HASHES,checked
from harness.proof_full_fragment_check import certify_fragment

PROMPTS=ROOT/'results/runs/proof-fresh14-prepared-20260905-v1/prompts.json'
PROMPTS_SHA='639874882710bcaffaeef7f36edd87c189f00ee204fd451b937f403f66b04c86'
MANIFEST=ROOT/'results/runs/proof-fresh14-controls-20260905-v1/manifest.json'
MANIFEST_SHA='02d7ffcdc291fb33716bc332ea878d400cb4affe8d324494c9203549dd55bb0f'
CYCLE=ROOT/'results/runs/proof-cuda-fresh14-cycle-20260905-v1'
GENERATION_SHA={'base':'ef23e327d3750f248a871bd152c391aace64b00f1e2ef0b7f660532f726aadff',
                'child':'ef05114ae423f8e9330a1a87874181bb245cacdc3948f98488c4ddeedb9808ac'}
BUDGET=dict(requested_tasks_per_arm=14,arms=2,requested_checks=28,seconds=1000,timeout=30)
SOURCES=tuple(dict.fromkeys((*GENERATION_SOURCES,'tools/proof_fresh_replay.py',
    'tools/proof_fenced_extract.py','tools/proof_outcome_audit.py',
    'tools/proof_fresh_selection.py','tools/proof_hierarchical_packet.py',
    'harness/proof_full_fragment_check.py','harness/proof_fragment_check.py','harness/runner.py')))


def prepare():
    from transformers import AutoTokenizer
    from tools.proof_fenced_extract import extract
    packet,original=export_tasks(MANIFEST,MANIFEST_SHA)
    raw=checked(PROMPTS,PROMPTS_SHA)
    if raw!=(json.dumps(packet,indent=2)+'\n').encode():raise ValueError('Exact controlled export required')
    for name,h in TOKENIZER_HASHES.items():checked(TOKENIZER/name,h)
    tokenizer=AutoTokenizer.from_pretrained(TOKENIZER,local_files_only=True)
    fields=('id','prefix','suffix','target_goal','theorem_name','source_path','source_sha256',
            'dependencies','dependency_sha256','source_family')
    tasks=[{k:t[k] for k in fields} for t in original]
    del original
    arms={}
    for arm in ('base','child'):
        path=CYCLE/arm;checked(path/'generations.jsonl',GENERATION_SHA[arm])
        config=json.loads((path/'config.json').read_bytes());rows=read_rows(path/'generations.jsonl')
        validated=validate_run(raw,PROMPTS_SHA,CHECKPOINT_SHA if arm=='child' else None,
            config,rows,json.loads((path/'summary.json').read_bytes()))
        if len(rows)!=14:raise ValueError('Full paired14 outputs required')
        extracted=[]
        for prompt,task,row in zip(validated,tasks,rows):
            validate_tokenization(tokenizer,prompt,row)
            if row['status']!='generated' or decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Exact complete generated replies required')
            result=extract(row['raw_reply'],task)
            if result.get('raw_sha256')!=row['raw_reply_sha256']:
                raise ValueError('Extractor raw reply identity mismatch')
            if result.get('fragment') is not None:
                start,end=result['fragment_offsets']
                if (type(start) is not int or type(end) is not int or not 0<=start<=end<=len(row['raw_reply'])
                        or row['raw_reply'][start:end]!=result['fragment']
                        or sha(result['fragment'].encode())!=result['fragment_sha256']):
                    raise ValueError('Extracted proof must be an exact original reply substring')
            extracted.append(dict(result,id=task['id'],raw_reply_sha256=row['raw_reply_sha256']))
        arms[arm]=extracted
    return tasks,arms


def identity(tasks):
    checked(PROMPTS,PROMPTS_SHA);checked(MANIFEST,MANIFEST_SHA)
    for arm,h in GENERATION_SHA.items():checked(CYCLE/arm/'generations.jsonl',h)
    for task in tasks:
        checked(task['source_path'],task['source_sha256'])
        for path,h in task['dependency_sha256'].items():checked(path,h)
    paths={ROOT/p for p in SOURCES}|{PROMPTS,MANIFEST}
    paths.update(TOKENIZER/p for p in TOKENIZER_HASHES)
    for arm in ('base','child'):
        paths.update(CYCLE/arm/p for p in ('config.json','generations.jsonl','summary.json','runtime.json'))
    for task in tasks:paths.update(Path(p) for p in [task['source_path'],*task['dependencies']])
    return dict(runtime=runtime_identity(),inputs_and_code={str(p):file_sha(p) for p in sorted(paths)})


def bound(task,fragment,result):
    """Verify raw input/module/dependencies/log binding before outcome attribution."""
    work=Path(result['workdir'])
    expected=sha((task['prefix']+fragment+task['suffix']).encode())
    if result.get('sha256')!=expected:raise ValueError('Candidate hash mismatch')
    if json.loads((work/'input.json').read_bytes())!=dict(prefix=task['prefix'],fragment=fragment,
        suffix=task['suffix'],theorem_name=task['theorem_name'],contract_version='full-proof-fragment-v1'):
        raise ValueError('Raw immutable input mismatch')
    if (work/'tlapm.log').read_text()!=result['output']:raise ValueError('Raw log mismatch')
    if result.get('command'):
        candidate=Path(result['candidate_path'])
        if (candidate.parent.resolve()!=work.resolve() or candidate.name!=result['command'][-1]
                or file_sha(candidate)!=expected):raise ValueError('Checked module mismatch')
        deps={Path(p).name:h for p,h in task['dependency_sha256'].items()}
        if result.get('dependency_sha256')!=deps:raise ValueError('Checked dependencies mismatch')
        for name,h in deps.items():checked(work/name,h)
    return True


def evaluate(tasks,arms,output,*,checker=certify_fragment,attest=identity,clock=time.monotonic):
    from tools.proof_outcome_audit import classify_outcome
    if len(tasks)!=14 or set(arms)!={'base','child'}:raise ValueError('Full paired population required')
    for rows in arms.values():
        if [r['id'] for r in rows]!=[t['id'] for t in tasks]:raise ValueError('Ordered full14 extraction ledger required')
    frozen=digest(dict(tasks=tasks,arms=arms));started=clock();before=attest(tasks);results=[]
    dump(output/'verifier_before.json',before)
    complete=False;stable=False
    def save():
        dump(output/'summary.json',dict(**BUDGET,verification_complete=complete,identity_stable=stable,
            post_hoc_extraction_replay=True,model_sampling=False,parameter_updates=0,reference_answers_used=False,
            accounted_attempts=len(results),elapsed_seconds=clock()-started,
            per_arm={arm:dict(requested_tasks=14,accounted_tasks=sum(r['arm']==arm for r in results),
                certified_tasks=sum(r['arm']==arm and r['certified'] for r in results) if complete and stable else 0,
                classifications={c:sum(r['arm']==arm and r['audit']['classification']==c for r in results)
                    for c in sorted({r['audit']['classification'] for r in results if r['arm']==arm})})
                for arm in ('base','child')}))
    save()
    with (output/'rows.jsonl').open('x') as stream:
        for index,task in enumerate(tasks):
            for arm in ('base','child'):
                extraction=arms[arm][index];fragment=extraction.get('fragment')
                result=dict(certified=False,status='extraction_reject')
                remaining=BUDGET['seconds']-(clock()-started)
                if fragment is not None and remaining>=1:
                    result=checker(task['prefix'],fragment,task['suffix'],theorem_name=task['theorem_name'],
                        dependencies=tuple(map(Path,task['dependencies'])),timeout=min(30,remaining),
                        work_root=output/'checks'/arm/task['id'])
                    provenance=bound(task,fragment,result)
                    if result.get('command') and Path(result['command'][0]).resolve()!=Path(before['runtime']['tlapm_path']).resolve():
                        raise ValueError('Unattested checker executable')
                    audit=classify_outcome(result,provenance_verified=provenance)
                else:
                    if fragment is not None:result['status']='unmeasured_budget'
                    audit=dict(classification=result['status'],measured_model_outcome=False,reward_eligible=False)
                row=dict(result,id=task['id'],arm=arm,fragment=fragment,extraction=extraction,audit=audit)
                row['certified']=result.get('certified') is True and audit['classification']=='proof_success'
                row['training_authorized']=False
                results.append(row);stream.write(json.dumps(row)+'\n');stream.flush();save()
    after=attest(tasks);dump(output/'verifier_after.json',after)
    stable=before==after and frozen==digest(dict(tasks=tasks,arms=arms))
    complete=stable and len(results)==28;save()
    if not stable:raise ValueError('Runtime/input identity changed; replay not verified')
    return results


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    tasks,arms=prepare();a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'extractions.json',arms)
    dump(a.output/'config.json',dict(**BUDGET,hypothesis='Fence-bounded extraction removes presentation artifacts without changing target or proof bytes',
        comparison='Same14 stored outputs per arm; post-hoc interface correction, not fresh sampling or model training',
        stop='28 accounted attempts or1000seconds; retain every rejection/unknown; no fallback proof or target relaxation',
        model_sampling=False,training_authorized=False,original_generation_sha256=GENERATION_SHA,
        frozen_sha256=digest(dict(tasks=tasks,arms=arms))))
    try:evaluate(tasks,arms,a.output)
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=repr(exc),verification_complete=False));raise


if __name__=='__main__':main()
