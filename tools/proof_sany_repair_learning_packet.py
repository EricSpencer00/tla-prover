"""TRAIN42 supervised packet: immutable TRAIN40 plus two verified repair targets.

Packet preparation is not authorization to train and does not revise any score.
"""
import argparse
import json
import os
from pathlib import Path
import sys
import time

for _name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[_name]='4'
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_repair_packet as original
from tools import proof_sumsequence_sany_repair_packet as repair
from tools import proof_sumsequence_sany_repair_verify as replay
from tools.proof_candidate_rank import encode_candidate

load=repair.load;sha=original.sha;digest=original.digest;file_sha=repair.file_sha;dump=repair.dump
checks=replay.checks;RUNS=ROOT/'results/runs'
ORIGINAL=RUNS/'proof-sumsequence-repair-packet-20260906-main-v2/train.json'
ORIGINAL_SHA='90291cd9488a835d95247a09ccc3e6c2ddd2f2e45add3f85b4f1c704487f7a0c'
REPAIR=RUNS/'proof-sumsequence-sany-repair-packet-20260906-v1/packet.json'
REPAIR_SHA='9bf035b22be90997769396a9ec94918e7cc6bd00e003baceecd374fe99b12d77'
VERIFIED=RUNS/'proof-sany-repair-verified-20260906-v1'
GENERATIONS=RUNS/'proof-sany-repair-eval-20260906-v1'
COLLECTION=RUNS/'proof-sany-repair-collection-20260906-v1.json'
PARENT_SHA=repair.POLICY_SHA
KIND='supervised_retained40_verified_syntax_repair2'
SHORT='BY DEF Front, Tail'
PINS={ORIGINAL:ORIGINAL_SHA,REPAIR:REPAIR_SHA,
    COLLECTION:'2fe9a593fb3bda69ec06abf137c4504171e5888a4a85a8abb1db8bfcba15f4ea',
    VERIFIED/'rows.json':'4e03cf6ade3f685bf900b69a005d64e7eea609bb16afa1116cecefb5ad6fbcee',
    VERIFIED/'summary.json':'5c547e15d3c6c42df8db2b86d17857b6849443ef7d09e48bcb5bf2f95f772ff4'}
SOURCES=tuple(sorted(set(replay.SOURCES)|set(repair.SOURCES)|{
    'tools/proof_sumsequence_repair_packet.py','tools/proof_candidate_rank.py',
    'tools/proof_sany_repair_learning_packet.py'}))
CONTRACT=dict(schema=1,packet_kind=KIND,algorithm='supervised_reference_and_verified_model_repair',
    split='train',requested_rows=42,retained_rows=40,whole_rows=36,repair_rows=6,
    parent_checkpoint_sha256=PARENT_SHA,max_tokens=9216,truncation=False,
    training_authorized=False,model_training_performed=False,on_policy_rewards=False,
    gate_claim=False,generalization_claim=False,original_evaluation_denominator=40,
    original_pass_at1_unchanged=True)


def exact_bytes(text,pin):
    if not isinstance(text,str) or sha(text.encode())!=pin:raise ValueError('Exact frozen packet bytes required')
    return json.loads(text)


def compose(old_bytes,repair_bytes):
    old=exact_bytes(old_bytes,ORIGINAL_SHA);rows=list(original.validate_training_packet(old))
    packet=exact_bytes(repair_bytes,REPAIR_SHA)
    if [r['id'] for r in packet['tasks']]!=list(repair.IDS):raise ValueError('Exact ordered selected2 required')
    if (rows[3]['id']!=repair.IDS[0] or rows[3]['source_sha256']!=packet['tasks'][0]['context']['source_sha256']):
        raise ValueError('Original Reachable1 reference/source positional binding changed')
    for index,item in enumerate(packet['tasks']):
        response=rows[3]['response'] if index==0 else SHORT
        context=item['context'];prompt=item['prompt']
        rows.append(dict(id=item['id']+'-syntax-repair',split='train',
            source_family=context['source_family'],source_sha256=context['source_sha256'],
            assembled_sha256=sha((context['prefix']+response+context['suffix']).encode()),
            prompt=prompt,prompt_sha256=sha(prompt.encode()),response=response,response_sha256=sha(response.encode())))
    return rows


def validate_training_packet(value):
    if not isinstance(value,dict) or any(value.get(k)!=v or type(value.get(k)) is not type(v) for k,v in CONTRACT.items()):
        raise ValueError('Exact TRAIN42 supervised/no-claim contract required')
    rows=compose(value['original_packet_bytes'],value['repair_packet_bytes'])
    if value.get('rows')!=rows or value.get('rows_sha256')!=digest(rows):
        raise ValueError('Unchanged TRAIN40 plus exact two targets required')
    encodings=value.get('encodings')
    if not isinstance(encodings,list) or len(encodings)!=42:raise ValueError('All42 complete encodings required')
    for row,encoding in zip(rows,encodings):
        ids=encoding['input_ids'];labels=encoding['labels'];n=encoding['prompt_tokens']
        if (encoding['id']!=row['id'] or encoding['prompt_sha256']!=row['prompt_sha256'] or
            encoding['response_sha256']!=row['response_sha256'] or type(n) is not int or not 0<n<len(ids)<=9216 or
            any(type(t) is not int or t<0 for t in ids) or labels!=[-100]*n+ids[n:] or
            encoding['response_tokens']!=len(ids)-n or ids[-1]!=value['eos_token_id']):
            raise ValueError('Exact complete prefix/response/EOS encoding required')
    proof=value.get('target_controls',{})
    if proof.get('complete') is not True or proof.get('requested_controls')!=4 or proof.get('accepted_controls')!=4:
        raise ValueError('All four actual target controls required')
    expected=[(r['id'],label,r['response_sha256']) for r in rows[-2:] for label in ('positive','false_conclusion')]
    controls=proof.get('rows',[])
    if [(r['id'],r['label'],r['response_sha256']) for r in controls]!=expected or any(r.get('accepted') is not True for r in controls):
        raise ValueError('Exact positive and intended-FALSE target bindings required')
    if value.get('exclusions',{}).get('protected_populations')!=['official119','official30','original18','development']:
        raise ValueError('Reconstructed protected population exclusions required')
    return rows


validate_export=validate_training_packet


def encode_rows(tokenizer,rows):
    encodings=[]
    for index,row in enumerate(rows):
        encoded=encode_candidate(tokenizer,row['prompt'],row['response'],9216)
        rendered=tokenizer.apply_chat_template([dict(role='user',content=row['prompt'])],tokenize=False,add_generation_prompt=True)
        ids=tokenizer(rendered,add_special_tokens=False,truncation=False)['input_ids']
        if encoded['rendered_prompt']!=rendered or encoded['input_ids'][:len(ids)]!=ids:
            raise ValueError('Actual inference prefix differs from training')
        if index<40 and encoded!=encode_candidate(tokenizer,row['prompt'],row['response'],8192):
            raise ValueError('Original40 training encoding changed')
        encodings.append(dict(encoded,id=row['id'],prompt_sha256=row['prompt_sha256'],response_sha256=row['response_sha256']))
    return encodings


def identity(tasks):
    files={}
    for path in (ORIGINAL,REPAIR,COLLECTION,repair.PROMPTS,repair.TOKENIZER,VERIFIED,GENERATIONS,repair.CONTROLS):
        for item in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if item.is_file():files[str(item.resolve())]=file_sha(item)
    return dict(files=files,sources={n:file_sha(ROOT/n) for n in SOURCES},verifier=checks.identity(tasks))


def admit():
    for path,pin in PINS.items():original.checked(path,pin)
    if original.export_packet()!=load(ORIGINAL):raise ValueError('Original40 current full admission differs')
    tasks,_,_,_,tokenizer,_=repair.admit()
    current=checks.admit_controls(repair.CONTROLS,tasks)
    before=load(VERIFIED/'identity_before.json')
    if before!=load(VERIFIED/'identity_after.json') or before['verifier']!=current:
        raise ValueError('Selected repair current runtime identity differs')
    for path,pin in before['files'].items():original.checked(path,pin)
    if before['sources']!={n:file_sha(ROOT/n) for n in replay.SOURCES}:raise ValueError('Selected repair source drift')
    for name,pin in load(COLLECTION)['files'].items():original.checked(GENERATIONS/name,pin)
    packet=load(REPAIR);chosen=replay.bind_tasks(packet,tasks);raw=load(GENERATIONS/'accounting.json')
    rows=load(VERIFIED/'rows.json');replay.audit_rows(chosen,raw,rows,current,VERIFIED)
    summary=load(VERIFIED/'summary.json')
    if any(summary.get(k)!=v for k,v in replay.summarize(rows,True).items()) or summary.get('identity_stable') is not True:
        raise ValueError('Actual selected2 summary differs from raw evidence')
    if (raw[1]['raw_reply']!=SHORT or rows[1]['sany']!=1 or rows[1]['proof']!=1 or
        summary['training_linkage']['child_sha256']!=PARENT_SHA):raise ValueError('Actual verified short model reply/current policy required')
    return tasks,chosen,current,tokenizer,repair.exclusion_bindings(tasks)


def target_controls(tasks,chosen,rows,current,output,checker=checks.check_fragment,clock=time.monotonic):
    requested=[(task,row,label) for task,row in zip(chosen,rows[-2:]) for label in ('positive','false_conclusion')]
    records=[dict(id=r['id'],label=label,response_sha256=r['response_sha256'],accepted=False,status='unattempted') for t,r,label in requested]
    started=clock();dump(output/'control_rows.json',records)
    for index,(task,row,label) in enumerate(requested):
        if clock()-started>300-65:break
        target=task if label=='positive' else checks.negative_task(task)
        value=checker(target,row['response'],output/'checks'/str(index),current)
        checks.audit_check(target,row['response'],value,output/'checks'/str(index),current)
        accepted=value['sany']==1 and value['proof']==1 if label=='positive' else checks.intended_negative(target,value)
        records[index].update(accepted=accepted,status=value['status'],task_sha256=digest(target),evidence=value)
        dump(output/'control_rows.json',records)
    elapsed=clock()-started
    return dict(requested_controls=4,accepted_controls=sum(r['accepted'] for r in records),rows=records,
        complete=all(r['accepted'] for r in records) and elapsed<=300,elapsed_seconds=elapsed,seconds=300)


def build(output):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    dump(output/'summary.json',dict(complete=False,requested_rows=42,admitted_rows=0,requested_controls=4))
    tasks=checks.admit_tasks(load(repair.PROMPTS));before=identity(tasks);dump(output/'identity_before.json',before)
    tasks,chosen,current,tokenizer,exclusions=admit()
    old_bytes=ORIGINAL.read_text();repair_bytes=REPAIR.read_text();rows=compose(old_bytes,repair_bytes)
    encodings=encode_rows(tokenizer,rows)
    controls=target_controls(tasks,chosen,rows,current,output);dump(output/'controls.json',controls)
    after=identity(tasks);dump(output/'identity_after.json',after)
    if before!=after:raise ValueError('Source/runtime/artifact drift during packet preparation')
    packet=dict(CONTRACT,original_packet_bytes=old_bytes,repair_packet_bytes=repair_bytes,rows=rows,
        rows_sha256=digest(rows),encodings=encodings,eos_token_id=tokenizer.eos_token_id,
        target_controls=controls,exclusions=exclusions,identity=before,
        provenance={str(p):h for p,h in PINS.items()},target_origins=['immutable independently verified reference','actual independently verified current-policy reply'])
    validate_training_packet(packet);dump(output/'train.json',packet)
    summary=dict(complete=True,requested_rows=42,admitted_rows=42,retained_rows=40,
        whole_rows=36,repair_rows=6,max_full_tokens=max(len(e['input_ids']) for e in encodings),
        new_targets=[dict(id=e['id'],prompt_tokens=e['prompt_tokens'],response_tokens=e['response_tokens'],full_tokens=len(e['input_ids'])) for e in encodings[-2:]],
        target_controls=4,train_sha256=file_sha(output/'train.json'),rows_sha256=digest(rows),
        training_authorized=False,model_training_performed=False,original_pass_at1_unchanged=True)
    dump(output/'summary.json',summary);return summary


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:print(json.dumps(build(args.output)))
    except BaseException as exc:
        if args.output.is_dir():dump(args.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),admitted_rows=0))
        raise


if __name__=='__main__':main()
