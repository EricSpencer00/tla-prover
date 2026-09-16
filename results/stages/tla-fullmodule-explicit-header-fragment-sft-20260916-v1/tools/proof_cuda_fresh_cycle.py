#!/usr/bin/env python3
"""Matched BASE/exposure512 evaluation on frozen14; no optimizer or repairs."""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_cuda_fresh_eval as probe
from tools.proof_cuda_cycle import run_processes,dump
from tools.proof_cuda_train import file_sha

MODEL=Path('/grand/EVITA/eric-spencer/hf-cache/hub/models--meta-llama--Llama-3.1-8B-Instruct/snapshots/0e9e39f249a16976918f6564b8830bc894c89659')
SOURCES=('tools/proof_cuda_fresh_cycle.py','tools/proof_cuda_fresh_cycle.pbs','tools/proof_cuda_cycle.py')


def freeze(prompts,prompts_sha,model,checkpoint):
    """Exact production admission, also callable read-only on the target host."""
    if model.resolve()!=MODEL.resolve():raise ValueError('Pinned model snapshot path required')
    admissions={}
    for arm,path in (('base',None),('child',checkpoint)):
        args=SimpleNamespace(prompts=prompts,expected_input_sha256=prompts_sha,
            model_path=model,checkpoint=path,
            expected_checkpoint_sha256=probe.CHECKPOINT_SHA if path else None)
        admissions[arm]=probe.admit(args)
    if admissions['base']['input_evidence']!=admissions['child']['input_evidence']:
        raise ValueError('Matched exact input tokens required')
    return dict(prompts_sha256=prompts_sha,checkpoint_sha256=probe.CHECKPOINT_SHA,
        admissions=admissions,implementation_sha256={n:file_sha(ROOT/n) for n in SOURCES})


def check_arm(path,raw,frozen,arm):
    from transformers import AutoTokenizer
    from tools.proof_cuda_eval import read_rows,validate_tokenization,decode_reply
    config=json.loads((path/'config.json').read_bytes())
    rows=read_rows(path/'generations.jsonl');summary=json.loads((path/'summary.json').read_bytes())
    expected=frozen['admissions'][arm]
    if any(config.get(k)!=v for k,v in expected.items() if k!='restore_exact'):
        raise ValueError('Arm differs from frozen production admission')
    tasks=probe.validate_run(raw,frozen['prompts_sha256'],expected['checkpoint_sha256'],config,rows,summary)
    tokenizer=AutoTokenizer.from_pretrained(MODEL,local_files_only=True)
    for task,row in zip(tasks,rows):
        validate_tokenization(tokenizer,task,row)
        if decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
            raise ValueError('Exact generated reply reconstruction required')
    if summary['termination']!='complete' or len(rows)!=14:
        raise ValueError('Incomplete generation preserved, not advanced')
    return dict(arm=arm,requested_tasks=14,completed_rows=len(rows),
        generated_tasks=sum(r['status']=='generated' for r in rows),
        unmeasured_time_limits=sum(r['status']=='generation_time_limit' for r in rows),
        generations_sha256=file_sha(path/'generations.jsonl'),verification_pending=True)


def execute(output,prompts,model,checkpoint,frozen):
    commands=[]
    for arm,path in (('base',None),('child',checkpoint)):
        cmd=[sys.executable,str(ROOT/'tools/proof_cuda_fresh_eval.py'),'generate',
            '--prompts',str(prompts),'--expected-input-sha256',frozen['prompts_sha256'],
            '--model-path',str(model),'--output',str(output/arm)]
        if path:cmd+=['--checkpoint',str(path),'--expected-checkpoint-sha256',probe.CHECKPOINT_SHA]
        commands.append(cmd)
    run_processes(commands,[output/'base.log',output/'child.log'],1260)
    if freeze(prompts,frozen['prompts_sha256'],model,checkpoint)!=frozen:
        raise ValueError('Runtime/input/checkpoint changed during paired evaluation')
    return [check_arm(output/arm,prompts.read_bytes(),frozen,arm) for arm in ('base','child')]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('prompts','model-path','checkpoint','output'):p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--prompts-sha256',required=True);a=p.parse_args()
    a.output=a.output.resolve()
    for value in (a.prompts,a.model_path,a.checkpoint):
        path=value.resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:
            raise ValueError('Output must be isolated from immutable inputs')
    a.output.mkdir(parents=True,exist_ok=False);started=time.monotonic()
    try:
        frozen=freeze(a.prompts,a.prompts_sha256,a.model_path,a.checkpoint)
        dump(a.output/'config.json',dict(frozen=frozen,
            hypothesis='Broader32 SFT512 transfers to14 prospective source-disjoint proof targets versus untuned BASE',
            measurement='Matched greedy pass@1; unchanged statements; local strict TLAPS after collection',
            budget=dict(tasks_per_arm=14,arms=2,generation_seconds_per_arm=1200,total_supervisor_seconds=3420),
            training_authorized=False,optimizer_updates=0,repairs=0,
            stop='Full28 attempts or declared deadlines; no retries, substitutions, answer feedback or training',
            scope='Locally proof-training-excluded scaffolded targets; unknown pretraining; additional diagnostic, not G2 gate'))
        arms=execute(a.output,a.prompts,a.model_path,a.checkpoint,frozen)
        dump(a.output/'summary.json',dict(status='paired_fresh14_generation_complete',arms=arms,
            elapsed_seconds=time.monotonic()-started,verification_pending=True,proof_success_claim=False))
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=repr(exc),elapsed_seconds=time.monotonic()-started,
            verification_pending=True,proof_success_claim=False));raise


if __name__=='__main__':main()
