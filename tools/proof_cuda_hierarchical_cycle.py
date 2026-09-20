#!/usr/bin/env python3
"""Bounded developmental repair comparison: BASE, leaf SFT, fresh hierarchical SFT."""
import argparse
import json
import math
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_cycle import run_processes, dump
from tools.proof_cuda_train import file_sha, model_files, validate_packet, PROFILE
from tools.proof_cuda_eval import read_rows, validate_tokenization
from tools.proof_cuda_repair_eval import validate_export, validate_run, IMPLEMENTATION, BUDGET

LEAF_SHA='12b519c75077405be176b9d5bae69aabc7d54c8bcf77f24c6d59db405cb692d5'
TRAIN_SHA='b105e352f5cfdda5fe878ea5d9760a5bc220d17c0c7f511a875577acbff00e06'
PROMPTS_SHA='f9447f45ca36323cb3c251fd36ad7d68bb8b988e813c3ad7bf237224d7d6c2a5'
MODEL_PATH=Path('/grand/EVITA/eric-spencer/hf-cache/hub/models--meta-llama--Llama-3.1-8B-Instruct/snapshots/0e9e39f249a16976918f6564b8830bc894c89659')
SOURCES=tuple(sorted(set(IMPLEMENTATION)|{'tools/proof_cuda_hierarchical_cycle.py',
    'tools/proof_cuda_hierarchical_cycle.pbs','tools/proof_cuda_cycle.py','tools/proof_candidate_rank.py'}))
TRAIN_SOURCES=('tools/proof_cuda_train.py','tools/proof_sequence_train.py',
               'tools/proof_candidate_rank.py','tools/proof_repair_pilot.py')


def validate_model_path(model):
    # Polaris exposes /grand as an alias for /lus/grand/projects. Normalize
    # both sides; comparing one resolved side to an unresolved pin rejects
    # the exact intended snapshot before any model operation.
    if model.resolve(strict=True)!=MODEL_PATH.resolve(strict=True):
        raise ValueError('Exact original Llama8B snapshot required')


def freeze(train,prompts,model,leaf):
    if file_sha(train)!=TRAIN_SHA or file_sha(prompts)!=PROMPTS_SHA:
        raise ValueError('Exact fresh TRAIN and repair21 input packets required')
    packet=json.loads(train.read_bytes());rows=validate_packet(packet)
    if packet.get('packet_kind')!='frozen17_hierarchical_repair_spans' or len(rows)!=17:
        raise ValueError('Only the fresh controlled17 hierarchical TRAIN packet is allowed')
    tasks=validate_export(json.loads(prompts.read_bytes()))
    train_prompts={r['id']:r['prompt'] for r in rows}
    if train_prompts!={r['id']:r['prompt'] for r in tasks if r['split']=='train'}:
        raise ValueError('Training and retention prompts/IDs must match exactly')
    if file_sha(leaf)!=LEAF_SHA:raise ValueError('Exact frozen leaf checkpoint required')
    validate_model_path(model)
    if BUDGET['seconds']!=600 or BUDGET['profile']!=PROFILE:
        raise ValueError('Repair probe contract changed')
    return dict(train_input_sha256=file_sha(train),prompts_sha256=file_sha(prompts),
        leaf_checkpoint_sha256=LEAF_SHA,model_files=model_files(model),
        implementation_sha256={name:file_sha(ROOT/name) for name in SOURCES},
        train_ids=[r['id'] for r in rows],train_evidence=packet['evidence'],profile=PROFILE)


def unchanged(frozen,train,prompts,model,leaf):
    if freeze(train,prompts,model,leaf)!=frozen:
        raise ValueError('Frozen model/input/checkpoint/runtime source changed between phases')


def check_probe(path,raw,frozen,checkpoint_sha,tokenizer):
    config=json.loads((path/'config.json').read_bytes())
    rows=read_rows(path/'generations.jsonl')
    summary=json.loads((path/'summary.json').read_bytes())
    tasks=validate_run(raw,config,rows,summary)
    if (summary.get('returncode')!=0 or summary.get('termination')!='complete' or
            len(rows)!=21 or any(r['status']!='generated' for r in rows)):
        raise ValueError('Complete21 generation required; no partial comparison or retry')
    expected=dict(model_files=frozen['model_files'],prompts_sha256=frozen['prompts_sha256'],
        checkpoint_sha256=checkpoint_sha,arm='base' if checkpoint_sha is None else 'checkpoint',
        implementation_sha256={name:frozen['implementation_sha256'][name] for name in IMPLEMENTATION})
    for key,value in expected.items():
        if config.get(key)!=value:raise ValueError('Probe identity changed: '+key)
    for task,row in zip(tasks,rows):validate_tokenization(tokenizer,task,row)
    return dict(generated=21,train_generated=17,development_generated=4,
        checkpoint_sha256=checkpoint_sha,model_files=frozen['model_files'],
        prompts_sha256=frozen['prompts_sha256'],torch_version=config['torch_version'],
        transformers_version=config['transformers_version'],
        files_sha256={name:file_sha(path/name) for name in ('config.json','summary.json','generations.jsonl')})


def check_training(path,frozen):
    config=json.loads((path/'config.json').read_bytes())
    summary=json.loads((path/'summary.json').read_bytes())
    expected=dict(model_files=frozen['model_files'],input_sha256=frozen['train_input_sha256'],
        train_ids=frozen['train_ids'],evidence=frozen['train_evidence'],dtype_profile=PROFILE,
        requested_updates=100,seconds=600,seed=20260925,lr=1e-5,max_tokens=8192,
        implementation_sha256={name:frozen['implementation_sha256'][name] for name in TRAIN_SOURCES})
    for key,value in expected.items():
        if config.get(key)!=value:raise ValueError('Training identity changed: '+key)
    if (summary.get('reload_tensors_exact') is not True or summary.get('reload_logits_exact') is not True
            or summary.get('evaluation_responses_forwarded')!=0
            or summary.get('train_tasks')!=17 or summary.get('attempted_train_tasks')!=17
            or not 17<=summary.get('updates',0)<=100 or summary.get('requested_updates')!=100):
        raise ValueError('Fresh17 SFT coverage/reload contract failed')
    for name in ('parameter_delta_l2','cuda_peak_allocated','cuda_peak_reserved'):
        value=summary.get(name)
        if not isinstance(value,(int,float)) or not math.isfinite(value) or value<=0:
            raise ValueError('Nonfinite or missing training health metric: '+name)
    if max(summary['cuda_peak_allocated'],summary['cuda_peak_reserved'])>36*1024**3:
        raise ValueError('CUDA memory headroom exceeded')
    steps=read_rows(path/'steps.jsonl')
    if (len(steps)!=summary['updates'] or {r['task'] for r in steps}!=set(frozen['train_ids'])):
        raise ValueError('Actual optimizer ledger must cover all17 TRAIN tasks')
    if ([r['step'] for r in steps]!=list(range(1,len(steps)+1)) or
            any(not math.isfinite(r[k]) for r in steps for k in ('loss','gradient_norm'))):
        raise ValueError('Optimizer steps must be sequential and finite')
    if file_sha(path/'policy_optimizer.pt')!=summary['checkpoint_sha256']:
        raise ValueError('Saved child checkpoint hash mismatch')
    return summary


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('train-input','prompts','leaf-checkpoint','output'):
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--model-path',type=Path,default=MODEL_PATH)
    a=p.parse_args()
    a.output=a.output.resolve()
    if a.leaf_checkpoint.resolve() in a.output.parents or a.output in a.leaf_checkpoint.resolve().parents:
        raise ValueError('New output must not contain original checkpoint')
    a.output.mkdir(parents=True,exist_ok=False)
    started=time.monotonic();progress=[]
    def record(phase,result):
        progress.append(dict(phase=phase,elapsed_seconds=time.monotonic()-started,result=result))
        dump(a.output/'progress.json',progress);print(json.dumps(progress[-1]),flush=True)
    try:
        frozen=freeze(a.train_input,a.prompts,a.model_path,a.leaf_checkpoint)
        dump(a.output/'config.json',dict(frozen=frozen,
            hypothesis='Task-shaped hierarchical SFT repairs generated proof structure versus leaf SFT and BASE',
            training='Fresh-base final-layer response SFT, fresh optimizer; not RL and not leaf-checkpoint resume',
            confounds='New arm changes response shape and TRAIN population17 versus50, the seeded100-update schedule, and fixes duplicated BOS relative to the old leaf checkpoint; any gain cannot be attributed to hierarchy alone',
            measurement='Greedy1024 free repair:17 TRAIN retention and4 reused DEV, reported separately; not G2',
            budgets=dict(parent_parallel_seconds=600,training_seconds=600,child_seconds=600,total_supervisor_seconds=2100),
            stop='Incomplete parents, changed provenance, failed reload, insufficient coverage or excess memory stop advancement',
            proof_success_claim=False,strict_verification='Local strict30s per module after collection'))
        import transformers
        tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
        raw=a.prompts.read_bytes()
        def guard():unchanged(frozen,a.train_input,a.prompts,a.model_path,a.leaf_checkpoint)
        def command(name,checkpoint=None):
            result=[sys.executable,str(ROOT/'tools/proof_cuda_repair_eval.py'),'generate',
                '--prompts',str(a.prompts),'--model-path',str(a.model_path),'--output',str(a.output/name)]
            if checkpoint:result+=['--checkpoint',str(checkpoint)]
            return result
        guard()
        run_processes([command('base'),command('leaf',a.leaf_checkpoint)],
                      [a.output/'base.log',a.output/'leaf.log'],620)
        guard()
        base=check_probe(a.output/'base',raw,frozen,None,tokenizer)
        leaf=check_probe(a.output/'leaf',raw,frozen,LEAF_SHA,tokenizer)
        if any(base[k]!=leaf[k] for k in ('model_files','prompts_sha256','torch_version','transformers_version')):
            raise ValueError('Parent comparisons require identical model/input/runtime')
        record('matched_parent_probes',dict(base=base,leaf=leaf))
        train=a.output/'training'
        guard()
        run_processes([[sys.executable,str(ROOT/'tools/proof_cuda_train.py'),'train',
            '--input',str(a.train_input),'--expected-input-sha256',frozen['train_input_sha256'],
            '--model-path',str(a.model_path),'--output',str(train),'--seed','20260925',
            '--steps','100','--seconds','600']],[a.output/'training.log'],620)
        guard();trained=check_training(train,frozen);record('fresh_hierarchical_sft',trained)
        checkpoint=train/'policy_optimizer.pt'
        run_processes([command('hierarchical',checkpoint)],[a.output/'hierarchical.log'],620)
        guard();child=check_probe(a.output/'hierarchical',raw,frozen,trained['checkpoint_sha256'],tokenizer)
        if any(base[k]!=child[k] for k in ('model_files','prompts_sha256','torch_version','transformers_version')):
            raise ValueError('Child comparison requires identical model/input/runtime')
        record('hierarchical_probe',child)
        dump(a.output/'summary.json',dict(status='developmental_generation_cycle_complete',
            elapsed_seconds=time.monotonic()-started,verification_pending=True,proof_success_claim=False,
            train_retention_tasks=17,reused_development_tasks=4,official_evaluation_tasks=0))
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=repr(exc),elapsed_seconds=time.monotonic()-started,
            completed_phases=[r['phase'] for r in progress],proof_success_claim=False))
        raise


if __name__=='__main__':main()
