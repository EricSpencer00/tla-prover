#!/usr/bin/env python3
"""One bounded Polaris proof-SFT cycle; strict verification is collected locally."""
import argparse
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_train import file_sha, validate_packet, model_files, PROFILE
from tools.proof_cuda_eval import validate_export, merge_shards, read_rows, BUDGET, validate_tokenization


def dump(path,value):
    path.write_text(json.dumps(value,indent=2)+'\n')


def run_processes(commands,logs,seconds):
    """Own all supervisors; their TERM handlers also reap CUDA workers."""
    started=time.monotonic(); processes=[]; streams=[]
    previous=signal.getsignal(signal.SIGTERM)
    def terminated(signum,frame):raise SystemExit(128+signum)
    signal.signal(signal.SIGTERM,terminated)
    try:
        for index,command in enumerate(commands):
            stream=logs[index].open('w');streams.append(stream)
            env=dict(os.environ,CUDA_VISIBLE_DEVICES=str(index),PYTHONUNBUFFERED='1',
                     HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
            processes.append(subprocess.Popen(command,stdout=stream,stderr=subprocess.STDOUT,
                                               env=env,start_new_session=True))
        for process in processes:
            code=process.wait(timeout=max(.1,seconds-(time.monotonic()-started)))
            if code!=0:raise RuntimeError('Phase supervisor exited '+str(code))
    finally:
        for process in processes:
            if process.poll() is None:
                os.killpg(process.pid,signal.SIGTERM)
                try:process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid,signal.SIGKILL);process.wait(timeout=5)
        for stream in streams:stream.close()
        signal.signal(signal.SIGTERM,previous)


def check_training(path,preflight=False):
    result=json.loads((path/'summary.json').read_bytes())
    if (not all(math.isfinite(result[k]) for k in ('parameter_delta_l2','cuda_peak_allocated')) or
            not result['reload_tensors_exact'] or not result['reload_logits_exact'] or
            result['parameter_delta_l2']<=0 or result['evaluation_responses_forwarded']!=0 or
            result['cuda_peak_allocated']>36*1024**3):
        raise ValueError('CUDA training/reload/memory preflight failed')
    if preflight:
        if result['updates']!=1:raise ValueError('Exactly one real preflight update required')
    elif result['updates']<50 or result['attempted_train_tasks']!=50:
        raise ValueError('Larger SFT arm did not cover its full50 TRAIN population')
    checkpoint=path/'policy_optimizer.pt'
    if file_sha(checkpoint)!=result['checkpoint_sha256']:
        raise ValueError('Saved checkpoint hash mismatch')
    return result


def saved_arm(path,prompt_bytes,data,tokenizer):
    paths=[path/('base-shard'+str(i)) for i in range(4)]
    shards=[(json.loads((p/'config.json').read_bytes()),read_rows(p/'generations.jsonl'),
             json.loads((p/'summary.json').read_bytes())) for p in paths]
    merged,identity=merge_shards(prompt_bytes,data,shards)
    if len(merged)!=119 or any(r['status']!='generated' for r in merged.values()):
        raise ValueError('Resume requires complete119 BASE; no generation retries')
    for task in validate_export(data):
        validate_tokenization(tokenizer,task,merged[task['id']])
    return identity


def validate_resume(source,output,config,prompt_bytes,data,base_files,tokenizer,runtime):
    """Read-only recovery of completed BASE, never an optimizer-state resume."""
    source=source.resolve();output=output.resolve()
    if source==output or source in output.parents or output in source.parents:
        raise ValueError('Resume output must be isolated from the original run')
    if (source/'training').exists() or (source/'summary.json').exists():
        raise ValueError('Resume is only for a cycle stopped before full training')
    old=json.loads((source/'config.json').read_bytes())
    pre=json.loads((source/'preflight/config.json').read_bytes())
    for key in ('train_input_sha256','prompts_sha256','model_path','seed','train_evidence'):
        if old.get(key)!=config[key]:raise ValueError('Resume cycle provenance mismatch: '+key)
    expected=dict(input_sha256=config['train_input_sha256'],model_path=config['model_path'],
        model_files=base_files,dtype_profile=PROFILE,seed=config['seed'],lr=1e-5,
        requested_updates=1,seconds=180,max_tokens=8192,evidence=config['train_evidence'])
    for key,value in expected.items():
        if pre.get(key)!=value:raise ValueError('Resume preflight provenance mismatch: '+key)
    for key,value in runtime.items():
        if pre.get(key)!=value:raise ValueError('Resume runtime changed: '+key)
    implementations=pre.get('implementation_sha256',{})
    if not implementations or any(file_sha(ROOT/name)!=sha for name,sha in implementations.items()):
        raise ValueError('Resume requires the exact preflight training implementation')
    result=check_training(source/'preflight',preflight=True)
    identity=saved_arm(source,prompt_bytes,data,tokenizer)
    if identity['arm']!='base' or identity['checkpoint_sha256'] is not None or identity['model_files']!=base_files:
        raise ValueError('Resume BASE does not match fresh training parent')
    files=['config.json','preflight/config.json','preflight/summary.json']
    files += [f'base-shard{i}/{name}' for i in range(4)
              for name in ('config.json','generations.jsonl','summary.json')]
    return dict(source=str(source),source_files_sha256={name:file_sha(source/name) for name in files},
                preflight=result,base_identity=identity,generated=119,
                optimizer_resume=False,preflight_checkpoint_used_for_training=False)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('train-input','prompts','model-path','output'):
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--resume-cycle',type=Path,help='Read-only prior cycle with complete BASE and verified preflight')
    a=p.parse_args();packet=json.loads(a.train_input.read_bytes());validate_packet(packet)
    prompt_bytes=a.prompts.read_bytes();data=json.loads(prompt_bytes);validate_export(data)
    if BUDGET['seconds']!=1200:raise ValueError('Paired phases must fit this one-hour job contract')
    if a.resume_cycle:
        source=a.resume_cycle.resolve();output=a.output.resolve()
        if source==output or source in output.parents or output in source.parents:
            raise ValueError('Resume output must be isolated from the original run')
    a.output.mkdir(parents=True,exist_ok=False);started=time.monotonic()
    config=dict(hypothesis='Verified human proof-leaf SFT on Llama8B transfers to full119 free proof generation',
        training='fresh-base final-layer float32 SFT;100 requested shuffled updates; at least50 actual/all50 tasks required',
        measurement='Paired identical full119 prompts,greedy512,batch2,fourGPUshards; local strict30s TLAPS after collection',
        budgets=dict(preflight_seconds=180,base_seconds=1200,train_seconds=600,child_seconds=1200,total_supervisor_seconds=3300),
        stop='Any failed preflight or incomplete BASE stops before full training; no silent retry or model fallback',
        train_input_sha256=file_sha(a.train_input),prompts_sha256=file_sha(a.prompts),
        model_path=str(a.model_path),train_evidence=packet['evidence'],seed=20260923,
        preflight_checkpoint='Discarded diagnostic parent; full SFT initializes afresh from cached base',
        proof_success_claim=False)
    if a.resume_cycle:
        config['budgets']=dict(preflight_seconds=0,base_seconds=0,train_seconds=600,
                              child_seconds=1200,total_supervisor_seconds=2100)
        config['resume_cycle']=str(a.resume_cycle.resolve())
    dump(a.output/'config.json',config)
    progress=[]
    def record(phase,result):
        progress.append(dict(phase=phase,elapsed_seconds=time.monotonic()-started,result=result))
        dump(a.output/'progress.json',progress);print(json.dumps(progress[-1]),flush=True)
    def training(name,steps,seconds):
        output=a.output/name
        command=[sys.executable,str(ROOT/'tools/proof_cuda_train.py'),'train',
            '--input',str(a.train_input),'--expected-input-sha256',config['train_input_sha256'],
            '--model-path',str(a.model_path),'--output',str(output),'--seed','20260923',
            '--steps',str(steps),'--seconds',str(seconds)]
        run_processes([command],[a.output/(name+'.log')],seconds+20)
        result=check_training(output,preflight=steps==1);record(name,result)
        return output/'policy_optimizer.pt'
    def inference(name,checkpoint=None):
        commands=[];paths=[]
        for index in range(4):
            output=a.output/(name+'-shard'+str(index));paths.append(output)
            command=[sys.executable,str(ROOT/'tools/proof_cuda_eval.py'),'generate',
                '--prompts',str(a.prompts),'--model-path',str(a.model_path),
                '--output',str(output),'--shard-index',str(index)]
            if checkpoint:command+=['--checkpoint',str(checkpoint)]
            commands.append(command)
        run_processes(commands,[a.output/(name+'-shard'+str(i)+'.log') for i in range(4)],1260)
        shards=[(json.loads((path/'config.json').read_bytes()),read_rows(path/'generations.jsonl'),
                 json.loads((path/'summary.json').read_bytes())) for path in paths]
        merged,identity=merge_shards(prompt_bytes,data,shards)
        result=dict(generated=sum(r['status']=='generated' for r in merged.values()),requested=119,identity=identity)
        record(name,result)
        if result['generated']!=119:raise ValueError('Incomplete full119 generation arm; no automatic retry')
    try:
        if a.resume_cycle:
            import torch
            import transformers
            tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
            runtime=dict(torch_version=torch.__version__,transformers_version=transformers.__version__,
                         hardware=torch.cuda.get_device_name(0))
            recovery=validate_resume(a.resume_cycle,a.output,config,prompt_bytes,data,
                                     model_files(a.model_path),tokenizer,runtime)
            dump(a.output/'resume.json',recovery);record('validated_saved_base_and_preflight',recovery)
        else:
            training('preflight',1,180)
            inference('base')
        checkpoint=training('training',100,600)
        inference('child',checkpoint)
        dump(a.output/'summary.json',dict(status='generation_cycle_complete',elapsed_seconds=time.monotonic()-started,
             verification_pending=True,proof_success_claim=False))
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=repr(exc),elapsed_seconds=time.monotonic()-started,
             completed_phases=[r['phase'] for r in progress],proof_success_claim=False))
        raise


if __name__=='__main__':main()
