#!/usr/bin/env python3
"""Frozen32 exposure ablation: reuse completed100-step probes, fresh512-step SFT."""
import argparse
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_cycle import run_processes,dump
from tools.proof_cuda_train import file_sha,validate_packet
from tools.proof_cuda_broader_cycle import MODEL_PATH,check_encodings,check_probe,check_training
from tools import proof_cuda_broader_eval as probe
from tools.proof_broader_packet import validate_export

PARENT_SHA='cd554adea8ee1095408d4502ce61230e198faddbcacae3f89e34808ed057c955'
SEED=20260928


def artifact_hashes(path):
    return {str(p.relative_to(path)):file_sha(p) for p in sorted(path.rglob('*')) if p.is_file()}


def freeze(train,prompts,model,prior,train_sha,prompts_sha):
    """Production read-only admission, including exact completed predecessor outputs."""
    from tools import proof_cuda_exposure_train as trainer
    import transformers
    if file_sha(train)!=train_sha or file_sha(prompts)!=prompts_sha:
        raise ValueError('Exact prepared packet hashes required')
    if model.resolve()!=MODEL_PATH.resolve():raise ValueError('Pinned model path required')
    packet=json.loads(train.read_bytes());rows=validate_packet(packet)
    raw=prompts.read_bytes();tasks=validate_export(json.loads(raw))
    if len(rows)!=32 or packet.get('packet_kind')!='frozen32_broader_whole_target_proofs':
        raise ValueError('Exact broader32 TRAIN required')
    if {r['id']:r['prompt'] for r in rows}!={r['id']:r['prompt'] for r in tasks if r['split']=='train'}:
        raise ValueError('Training/probe prompt mismatch')
    parent=prior/'training/policy_optimizer.pt'
    if file_sha(parent)!=PARENT_SHA:raise ValueError('Immutable100-step parent required')
    prior_summary=json.loads((prior/'summary.json').read_bytes())
    if (prior_summary.get('status')!='developmental_generation_cycle_complete'
            or prior_summary.get('train_retention_tasks')!=32
            or prior_summary.get('reused_development_tasks')!=4 or (prior/'failure.json').exists()):
        raise ValueError('Completed prior cycle required')
    previous=json.loads((prior/'config.json').read_bytes())['frozen']
    if (previous['train_input_sha256']!=train_sha or previous['prompts_sha256']!=prompts_sha
            or previous['train_ids']!=[r['id'] for r in rows]):
        raise ValueError('Prior training population/input changed')
    for name,expected in previous['implementation_sha256'].items():
        if file_sha(ROOT/name)!=expected:raise ValueError('Original runtime changed: '+name)
    check_training(prior/'training',previous)
    admissions={arm:probe.admit(prompts,prompts_sha,model,checkpoint)
                for arm,checkpoint in (('base',None),('parent',parent))}
    tokenizer=transformers.AutoTokenizer.from_pretrained(model,local_files_only=True)
    check_encodings(tokenizer,packet,tasks)
    for arm,checkpoint in (('base',None),('child',PARENT_SHA)):
        check_probe(prior/arm,raw,previous,checkpoint,tokenizer)
    sources=sorted(set(previous['implementation_sha256'])|set(trainer.SOURCES)|{
        'tools/proof_cuda_exposure_cycle.py','tools/proof_cuda_exposure_cycle.pbs'})
    return dict(train_input_sha256=train_sha,prompts_sha256=prompts_sha,
        parent_checkpoint_sha256=PARENT_SHA,model_files=admissions['base']['model_files'],
        eos_token_ids=admissions['base']['eos_token_ids'],admissions=admissions,
        train_ids=[r['id'] for r in rows],train_evidence=packet['evidence'],
        profile=probe.BUDGET['profile'],prior_artifacts_sha256=artifact_hashes(prior),
        implementation_sha256={n:file_sha(ROOT/n) for n in sources})


def execute(output,train,prompts,model,prior,frozen,guard,tokenizer):
    from tools import proof_cuda_exposure_train as trainer
    progress=[]
    def record(phase,result):
        progress.append(dict(phase=phase,result=result));dump(output/'progress.json',progress)
    record('reused_complete100step_probes',dict(prior_cycle=str(prior),
        artifacts_sha256=frozen['prior_artifacts_sha256'],parent_checkpoint_sha256=PARENT_SHA))
    trained_path=output/'training'
    run_processes([[sys.executable,str(ROOT/'tools/proof_cuda_exposure_train.py'),'train',
        '--input',str(train),'--expected-input-sha256',frozen['train_input_sha256'],
        '--model-path',str(model),'--output',str(trained_path),'--steps','512',
        '--seed',str(SEED),'--seconds','600','--max-tokens','8192','--lr','1e-5']],
        [output/'training.log'],620)
    guard();trained=trainer.validate_training(trained_path,frozen)
    record('fresh512step_sft',trained)
    run_processes([[sys.executable,str(ROOT/'tools/proof_cuda_broader_eval.py'),'generate',
        '--prompts',str(prompts),'--expected-input-sha256',frozen['prompts_sha256'],
        '--model-path',str(model),'--checkpoint',str(trained_path/'policy_optimizer.pt'),
        '--output',str(output/'child')]], [output/'child.log'],1220)
    guard();result=check_probe(output/'child',prompts.read_bytes(),frozen,trained['checkpoint_sha256'],tokenizer)
    record('child_probe',result)
    return progress


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('train-input','prompts','model-path','prior-cycle','output'):
        p.add_argument('--'+name,type=Path,required=True)
    for name in ('train-input-sha256','prompts-sha256'):p.add_argument('--'+name,required=True)
    a=p.parse_args();a.output=a.output.resolve()
    for path in (a.train_input,a.prompts,a.model_path,a.prior_cycle):
        path=path.resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:
            raise ValueError('Output must be isolated from all immutable inputs')
    a.output.mkdir(parents=True,exist_ok=False);started=time.monotonic()
    try:
        def current():return freeze(a.train_input,a.prompts,a.model_path,a.prior_cycle,
                                    a.train_input_sha256,a.prompts_sha256)
        frozen=current()
        def guard():
            if current()!=frozen:raise ValueError('Frozen runtime/input/prior artifacts changed')
        import transformers
        tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
        dump(a.output/'config.json',dict(frozen=frozen,
            hypothesis='Sixteen exposures per TRAIN task restore whole-proof fit lost with only3or4; measure DEV separately',
            training='Fresh same base and optimizer,512 response-only SFT updates; no RL or checkpoint resume',
            comparison='Reuse exact completed100-step36-probes; greedy3072/context8192 unchanged; no DEV answers in training',
            budgets=dict(updates=512,epochs=16,training_seconds=600,child_seconds=1200,total_supervisor_seconds=3420),
            stop='Incomplete coverage/reload,identity drift,36GiB memory breach or incomplete generation stops advancement',
            limitations='32 supervised TRAIN tasks and4 repeatedly used DEV; not clean generalization/G2',
            verification_pending=True,proof_success_claim=False))
        execute(a.output,a.train_input,a.prompts,a.model_path,a.prior_cycle,frozen,guard,tokenizer)
        dump(a.output/'summary.json',dict(status='exposure_generation_cycle_complete',
            elapsed_seconds=time.monotonic()-started,verification_pending=True,proof_success_claim=False,
            train_retention_tasks=32,reused_development_tasks=4,official_evaluation_tasks=0))
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=repr(exc),elapsed_seconds=time.monotonic()-started,
                                        proof_success_claim=False));raise


if __name__=='__main__':main()
