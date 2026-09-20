#!/usr/bin/env python3
"""Matched32-TRAIN/four-DEV broader SFT experiment; no gate or RL claim."""
import argparse
import json
import math
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_cycle import run_processes, dump
from tools.proof_cuda_train import file_sha, validate_packet, encode_row, PROFILE
from tools.proof_cuda_eval import read_rows, validate_tokenization, digest

MODEL_PATH=Path('/grand/EVITA/eric-spencer/hf-cache/hub/models--meta-llama--Llama-3.1-8B-Instruct/snapshots/0e9e39f249a16976918f6564b8830bc894c89659')
PARENT_SHA='b2ff2b9ed7d9a5e6c8f9b82b11f56a91a17f110ecbc57ad5d3d1e64c29179c21'
SEED=20260928
CACHE_POLICY='release_unused_after_each_optimizer_step'
TRAIN_SOURCES=('tools/proof_cuda_train.py','tools/proof_sequence_train.py',
    'tools/proof_candidate_rank.py','tools/proof_repair_pilot.py',
    'tools/proof_whole_packet.py','tools/proof_broader_packet.py')


def check_encodings(tokenizer,packet,tasks):
    from tools.proof_cuda_broader_eval import encode_prompt
    expected={r['id']:r for r in packet['token_feasibility']['rows']}
    train={r['id']:r for r in packet['rows']}
    if set(expected)!={r['id'] for r in tasks}:
        raise ValueError('All36 token evidence rows required')
    for task in tasks:
        actual=encode_prompt(tokenizer,task); want=expected[task['id']]
        if (actual['status']!='ready' or actual['input_tokens']!=want['prompt_tokens']
                or digest(actual['input_token_ids'])!=want['input_token_ids_sha256']):
            raise ValueError('Target inference differs from frozen token evidence')
        if task['id'] in train:
            encoded=encode_row(tokenizer,train[task['id']])
            if (encoded['input_ids'][:encoded['prompt_tokens']]!=actual['input_token_ids']
                    or encoded['response_tokens']!=want['response_tokens']
                    or len(encoded['input_ids'])!=want['total_tokens']):
                raise ValueError('Training/inference token mismatch')


def freeze(train,prompts,model,parent,train_sha,prompts_sha):
    """Actual production read-only admission; execute on target before qsub."""
    from tools import proof_cuda_broader_eval as probe
    from tools.proof_broader_packet import validate_export
    if file_sha(train)!=train_sha or file_sha(prompts)!=prompts_sha:
        raise ValueError('Exact locally frozen packet hashes required')
    packet=json.loads(train.read_bytes()); rows=validate_packet(packet)
    tasks=validate_export(json.loads(prompts.read_bytes()))
    if packet.get('packet_kind')!='frozen32_broader_whole_target_proofs' or len(rows)!=32 or len(tasks)!=36:
        raise ValueError('Exact32 TRAIN and four DEV required')
    if {r['id']:r['prompt'] for r in rows}!={r['id']:r['prompt'] for r in tasks if r['split']=='train'}:
        raise ValueError('TRAIN/probe prompt mismatch')
    if model.resolve()!=MODEL_PATH.resolve() or file_sha(parent)!=PARENT_SHA:
        raise ValueError('Pinned model and immutable whole6 parent required')
    if (probe.BUDGET['max_new_tokens']!=3072 or probe.BUDGET['seconds']!=1200
            or probe.BUDGET['seed']!=SEED or probe.BUDGET['profile']!=PROFILE):
        raise ValueError('Frozen broader probe budget changed')
    admissions={arm:probe.admit(prompts,prompts_sha,model,checkpoint)
                for arm,checkpoint in (('base',None),('parent',parent))}
    import transformers
    tokenizer=transformers.AutoTokenizer.from_pretrained(model,local_files_only=True)
    check_encodings(tokenizer,packet,tasks)
    sources=sorted(set(probe.IMPLEMENTATION)|set(TRAIN_SOURCES)|{
        'tools/proof_cuda_broader_cycle.py','tools/proof_cuda_broader_cycle.pbs','tools/proof_cuda_cycle.py'})
    return dict(train_input_sha256=train_sha,prompts_sha256=prompts_sha,
        parent_checkpoint_sha256=PARENT_SHA,model_files=admissions['base']['model_files'],
        eos_token_ids=admissions['base']['eos_token_ids'],admissions=admissions,
        train_ids=[r['id'] for r in rows],train_evidence=packet['evidence'],profile=PROFILE,
        implementation_sha256={n:file_sha(ROOT/n) for n in sources})


def check_probe(path,raw,frozen,checkpoint_sha,tokenizer):
    from tools.proof_cuda_broader_eval import validate_run, IMPLEMENTATION
    config=json.loads((path/'config.json').read_bytes()); rows=read_rows(path/'generations.jsonl')
    summary=json.loads((path/'summary.json').read_bytes());tasks=validate_run(raw,config,rows,summary)
    if (summary.get('returncode')!=0 or summary.get('termination')!='complete'
            or len(rows)!=36 or any(r['status']!='generated' for r in rows)):
        raise ValueError('All36 measured generations required before advancement')
    expected=dict(model_files=frozen['model_files'],prompts_sha256=frozen['prompts_sha256'],
        checkpoint_sha256=checkpoint_sha,eos_token_ids=frozen['eos_token_ids'],
        implementation_sha256={n:frozen['implementation_sha256'][n] for n in IMPLEMENTATION})
    for key,value in expected.items():
        if config.get(key)!=value:raise ValueError('Probe identity mismatch: '+key)
    for key in ('torch_version','transformers_version'):
        if config.get(key)!=frozen['admissions']['base'][key]:raise ValueError('Runtime version mismatch')
    for task,row in zip(tasks,rows):validate_tokenization(tokenizer,task,row)
    return dict(generated=36,train_generated=32,development_generated=4,checkpoint_sha256=checkpoint_sha,
        files_sha256={n:file_sha(path/n) for n in ('config.json','summary.json','generations.jsonl')})


def check_training(path,frozen):
    config=json.loads((path/'config.json').read_bytes());summary=json.loads((path/'summary.json').read_bytes())
    expected=dict(model_files=frozen['model_files'],input_sha256=frozen['train_input_sha256'],
        train_ids=frozen['train_ids'],evidence=frozen['train_evidence'],dtype_profile=PROFILE,
        requested_updates=100,seconds=600,seed=SEED,lr=1e-5,max_tokens=8192,cuda_cache_policy=CACHE_POLICY,
        implementation_sha256={n:frozen['implementation_sha256'][n] for n in TRAIN_SOURCES})
    for key,value in expected.items():
        if config.get(key)!=value:raise ValueError('Training identity mismatch: '+key)
    for key,value in dict(reload_tensors_exact=True,reload_logits_exact=True,evaluation_responses_forwarded=0,
                         train_tasks=32,attempted_train_tasks=32,updates=100,requested_updates=100).items():
        if summary.get(key)!=value:raise ValueError('Incomplete training/reload: '+key)
    for key in ('parameter_delta_l2','cuda_peak_allocated','cuda_peak_reserved'):
        value=summary.get(key)
        if type(value) not in (int,float) or not math.isfinite(value) or value<=0:
            raise ValueError('Invalid training health: '+key)
    if max(summary['cuda_peak_allocated'],summary['cuda_peak_reserved'])>36*1024**3:
        raise ValueError('Memory headroom exceeded')
    for key in ('torch_version','transformers_version'):
        if config.get(key)!=frozen['admissions']['base'][key]:raise ValueError('Training runtime changed')
    steps=read_rows(path/'steps.jsonl')
    if (len(steps)!=100 or [r['step'] for r in steps]!=list(range(1,101))
            or {r['task'] for r in steps}!=set(frozen['train_ids'])
            or any(not math.isfinite(r[k]) for r in steps for k in ('loss','gradient_norm'))):
        raise ValueError('Actual optimizer ledger incomplete/unhealthy')
    if file_sha(path/'policy_optimizer.pt')!=summary['checkpoint_sha256']:
        raise ValueError('Checkpoint bytes changed')
    return summary


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('train-input','prompts','model-path','parent-checkpoint','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    for name in ('train-input-sha256','prompts-sha256'):parser.add_argument('--'+name,required=True)
    a=parser.parse_args();a.output=a.output.resolve()
    for original in (a.train_input,a.prompts,a.parent_checkpoint,a.model_path):
        original=original.resolve()
        if a.output==original or a.output in original.parents or original in a.output.parents:
            raise ValueError('Output must be isolated from immutable inputs')
    a.output.mkdir(parents=True,exist_ok=False);started=time.monotonic();progress=[]
    def record(phase,result):
        progress.append(dict(phase=phase,result=result));dump(a.output/'progress.json',progress)
    try:
        def current():return freeze(a.train_input,a.prompts,a.model_path,a.parent_checkpoint,
                                    a.train_input_sha256,a.prompts_sha256)
        frozen=current();raw=a.prompts.read_bytes()
        import transformers
        tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
        def guard():
            if current()!=frozen:raise ValueError('Frozen runtime/inputs/model changed')
        dump(a.output/'config.json',dict(frozen=frozen,
            hypothesis='Broader seven-family whole-proof supervision improves transfer over six-target, three-family memorization',
            training='Fresh immutable base, fresh optimizer,100 final-layer SFT updates; no RL or parent resume',
            measurement='Matched greedy3072:32TRAIN/four reused DEV per policy. Report old6/new26/fourDEV separately, not G2.',
            confounds='32 versus6 examples changes exposures per example at fixed100updates; seeds differ; not isolated diversity causality',
            budgets=dict(parent_parallel_seconds=1200,training_seconds=600,child_seconds=1200,total_supervisor_seconds=3420),
            stop='Any incomplete generation, time limit, identity drift, incomplete update coverage/reload or36GiB memory breach stops advancement',
            strict_verification='Local serial30s per task after artifact collection',proof_success_claim=False))
        def command(name,checkpoint=None):
            cmd=[sys.executable,str(ROOT/'tools/proof_cuda_broader_eval.py'),'generate',
                '--prompts',str(a.prompts),'--expected-input-sha256',a.prompts_sha256,
                '--model-path',str(a.model_path),'--output',str(a.output/name)]
            if checkpoint:cmd+=['--checkpoint',str(checkpoint)]
            return cmd
        run_processes([command('base'),command('parent',a.parent_checkpoint)],
                      [a.output/'base.log',a.output/'parent.log'],1220)
        guard();record('matched_parent_probes',dict(base=check_probe(a.output/'base',raw,frozen,None,tokenizer),
                    parent=check_probe(a.output/'parent',raw,frozen,PARENT_SHA,tokenizer)))
        train=a.output/'training'
        run_processes([[sys.executable,str(ROOT/'tools/proof_cuda_train.py'),'train','--input',str(a.train_input),
            '--expected-input-sha256',a.train_input_sha256,'--model-path',str(a.model_path),'--output',str(train),
            '--seed',str(SEED),'--steps','100','--seconds','600','--max-tokens','8192','--lr','1e-5']],
            [a.output/'training.log'],620)
        guard();trained=check_training(train,frozen);record('fresh_broader_sft',trained)
        run_processes([command('child',train/'policy_optimizer.pt')],[a.output/'child.log'],1220)
        guard();record('child_probe',check_probe(a.output/'child',raw,frozen,trained['checkpoint_sha256'],tokenizer))
        dump(a.output/'summary.json',dict(status='developmental_generation_cycle_complete',
            elapsed_seconds=time.monotonic()-started,verification_pending=True,proof_success_claim=False,
            train_retention_tasks=32,reused_development_tasks=4,official_evaluation_tasks=0))
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=repr(exc),elapsed_seconds=time.monotonic()-started,
             completed_phases=[r['phase'] for r in progress],proof_success_claim=False))
        raise


if __name__=='__main__':main()
