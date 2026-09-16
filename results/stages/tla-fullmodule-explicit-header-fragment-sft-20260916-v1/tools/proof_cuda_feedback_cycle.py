#!/usr/bin/env python3
"""One matched, non-training feedback round on four reused DEV tasks per policy."""
import argparse
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_cycle import run_processes,dump
from tools.proof_cuda_train import file_sha
from tools.proof_cuda_eval import read_rows,validate_tokenization
from tools import proof_cuda_feedback_eval as probe

# Filled only from locally prepared, reviewed immutable prompt packets.
PACKET_HASHES = {
    'base':'abbdc58a0c3f76c1cddad530a76760d5d8e80b1fb1eadeb2da5dab32f0bcf485',
    'parent':'c48199844ba92e0dbf88c2414d724cc529d3cd995711ea2026caed62e6ee6bb8',
    'child':'d9f4cfbf981708c13f47780e8cd9c0dbd053377b61f51859956f86c02635e37d',
}
ARMS=('base','parent','child')


def freeze(inputs,model,parent,child):
    if set(PACKET_HASHES)!=set(ARMS):
        raise ValueError('All three locally prepared packet hashes must be frozen before execution')
    checkpoints=dict(base=None,parent=parent,child=child)
    admissions={arm:probe.admit(inputs/arm/'prompts.json',PACKET_HASHES[arm],model,checkpoints[arm]) for arm in ARMS}
    sources=sorted(set(probe.IMPLEMENTATION)|{'tools/proof_cuda_feedback_cycle.py',
        'tools/proof_cuda_feedback_cycle.pbs','tools/proof_cuda_cycle.py'})
    return dict(admissions=admissions,implementation_sha256={n:file_sha(ROOT/n) for n in sources},
                packet_sha256=PACKET_HASHES,checkpoint_sha256=probe.CHECKPOINTS)


def check_arm(path,arm,raw,frozen,tokenizer):
    config=json.loads((path/'config.json').read_bytes())
    rows=read_rows(path/'generations.jsonl')
    summary=json.loads((path/'summary.json').read_bytes())
    tasks=probe.validate_run(raw,config,rows,summary)
    if summary.get('returncode')!=0 or summary.get('termination')!='complete' or len(rows)!=4 or any(r['status']!='generated' for r in rows):
        raise ValueError('Complete four measured feedback outputs required: '+arm)
    for key in ('model_files','prompts_sha256','checkpoint_sha256','experiment_arm','implementation_sha256'):
        if config.get(key)!=frozen['admissions'][arm][key]:
            raise ValueError('Feedback identity changed: '+arm+':'+key)
    for task,row in zip(tasks,rows):validate_tokenization(tokenizer,task,row)
    return dict(requested_tasks=4,generated_tasks=4,checkpoint_sha256=config['checkpoint_sha256'],
                files_sha256={n:file_sha(path/n) for n in ('config.json','summary.json','generations.jsonl')},
                verified_proof_claim=False)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('inputs','model-path','parent-checkpoint','child-checkpoint','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    args=parser.parse_args(); args.output=args.output.resolve()
    for original in (args.inputs,args.parent_checkpoint,args.child_checkpoint):
        original=original.resolve()
        if args.output==original or args.output in original.parents or original in args.output.parents:
            raise ValueError('Output must be isolated from immutable inputs/checkpoints')
    args.output.mkdir(parents=True,exist_ok=False); started=time.monotonic()
    try:
        def current():return freeze(args.inputs,args.model_path,args.parent_checkpoint,args.child_checkpoint)
        frozen=current()
        dump(args.output/'config.json',dict(frozen=frozen,
            hypothesis='One strict-verifier feedback repair improves measured DEV proof success versus each policy first attempt',
            method='Three separate policies; one initial attempt plus one adaptive repair; no model updates or oracle DEV answers',
            measurement='Four reused DEV tasks per arm, adaptive pass@2 and conditional repair rate; not G2 or best symbolic search',
            budgets=dict(arms_parallel_seconds=600,batch_seconds=180,outer_seconds=900,strict_local_seconds_per_task=30),
            stop='Twelve complete measured outputs or declared deadlines; no hidden retry or success claims from process exit'))
        commands=[]; checkpoints=dict(base=None,parent=args.parent_checkpoint,child=args.child_checkpoint)
        for arm in ARMS:
            command=[sys.executable,str(ROOT/'tools/proof_cuda_feedback_eval.py'),'generate',
                '--prompts',str(args.inputs/arm/'prompts.json'),'--expected-input-sha256',PACKET_HASHES[arm],
                '--model-path',str(args.model_path),'--output',str(args.output/arm)]
            if checkpoints[arm]:command+=['--checkpoint',str(checkpoints[arm])]
            commands.append(command)
        run_processes(commands,[args.output/(arm+'.log') for arm in ARMS],620)
        if current()!=frozen:raise ValueError('Frozen feedback runtime/input/model changed')
        import transformers
        tokenizer=transformers.AutoTokenizer.from_pretrained(args.model_path,local_files_only=True)
        results={arm:check_arm(args.output/arm,arm,(args.inputs/arm/'prompts.json').read_bytes(),frozen,tokenizer) for arm in ARMS}
        dump(args.output/'summary.json',dict(status='complete_generation_only',arms=results,parameter_updates=0,
            requested_tasks_per_arm=4,requested_feedback_generations=12,strict_verification_pending=True,
            elapsed_seconds=time.monotonic()-started,proof_success_claim=False))
    except BaseException as exc:
        dump(args.output/'failure.json',dict(error=repr(exc),elapsed_seconds=time.monotonic()-started,
            proof_success_claim=False,parameter_updates=0))
        raise


if __name__=='__main__':main()
