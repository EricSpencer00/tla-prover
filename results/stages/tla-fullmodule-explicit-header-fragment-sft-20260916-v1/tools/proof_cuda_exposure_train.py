#!/usr/bin/env python3
"""Isolated sixteen-epoch whole-proof SFT profile; historical100 cap unchanged."""
import argparse
from collections import Counter
import json
import math
import os
from pathlib import Path
import random
import signal
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_train import (ALGORITHM,PROFILE,sha,file_sha,dump,encode_row,model_files,
    load_policy,select_final_layer,autocast,release_unused_cache,save_reload)
from tools.proof_broader_packet import validate_training_packet,TRAIN_IDS
from tools.proof_cuda_eval import digest,read_rows

STEPS=512
SEED=20260928
SECONDS=600
RESERVE=90
CACHE_POLICY='release_unused_after_each_optimizer_step'
MEMORY_LIMIT=36*1024**3
INPUT_SHA='5adb8315e8d9563fbf42a40fa5055d4e4b3b7f3e3c6e4ec7fe889b05ca030860'
MODEL_FILES_SHA='be21cca8df80e80b27b11aa238d8d77192e3c0e47a096224d1292559190a4cf9'
SOURCES=('tools/proof_cuda_exposure_train.py','tools/proof_cuda_train.py','tools/proof_sequence_train.py',
    'tools/proof_candidate_rank.py','tools/proof_repair_pilot.py','tools/proof_whole_packet.py',
    'tools/proof_broader_packet.py','tools/proof_cuda_eval.py')


def schedule(count,steps,seed):
    if count!=32 or steps!=STEPS:
        raise ValueError('Exposure profile requires exactly32 tasks and512 updates')
    rng=random.Random(seed);indices=[]
    for _ in range(16):
        epoch=list(range(count));rng.shuffle(epoch);indices.extend(epoch)
    return indices


def validate_args(args):
    if (args.steps!=STEPS or args.seed!=SEED or args.seconds!=SECONDS or args.max_tokens!=8192 or
            args.lr!=1e-5 or args.expected_input_sha256!=INPUT_SHA):
        raise ValueError('Exact frozen32,512-update,600-second exposure profile required')
    output=args.output.resolve()
    for path in (args.input,args.model_path):
        path=path.resolve()
        if output==path or output in path.parents or path in output.parents:
            raise ValueError('Output must be isolated from immutable inputs')


def memory_guard(allocated,reserved):
    if any(type(v) not in (int,float) or not math.isfinite(v) or v<=0 for v in (allocated,reserved)):
        raise ValueError('Invalid allocated/reserved memory measurement')
    if max(allocated,reserved)>MEMORY_LIMIT:
        raise ValueError('36GiB allocated/reserved memory headroom exceeded')


def train_steps(net,selected,encoded,rows,steps,seed,lr,seconds,device,emit,clear_cache=True):
    """Same response-only AdamW math, independently bounded sixteen-epoch schedule."""
    import torch
    if not math.isfinite(lr) or lr<=0 or not 0<seconds<=SECONDS:
        raise ValueError('Positive finite learning rate and bounded worker remainder required')
    indices=schedule(len(encoded),steps,seed)
    if len(rows)!=32 or any(p.dtype!=torch.float32 or not p.requires_grad for p in selected.values()):
        raise ValueError('32 rows and enabled float32 parameters required')
    optimizer=torch.optim.AdamW(selected.values(),lr=lr,weight_decay=0,foreach=False)
    started=time.monotonic();metrics=[];net.eval()
    for step,index in enumerate(indices):
        if time.monotonic()-started>=seconds:break
        e=encoded[index];ids=torch.tensor([e['input_ids']],device=device)
        labels=torch.tensor([e['labels']],device=device)
        optimizer.zero_grad(set_to_none=True)
        with autocast(device):loss=net(input_ids=ids,labels=labels,use_cache=False).loss
        if not torch.isfinite(loss):raise RuntimeError('Nonfinite loss')
        loss.backward()
        norm=torch.nn.utils.clip_grad_norm_(selected.values(),1.,error_if_nonfinite=True)
        optimizer.step()
        if any(not torch.isfinite(p).all() for p in selected.values()):raise RuntimeError('Nonfinite parameter')
        release_unused_cache(device,clear_cache)
        row=dict(step=step+1,task=rows[index]['id'],loss=float(loss.detach()),gradient_norm=float(norm),
                 response_tokens=e['response_tokens'],elapsed_s=time.monotonic()-started)
        metrics.append(row);emit(row)
        if device=='cuda':memory_guard(torch.cuda.max_memory_allocated(),torch.cuda.max_memory_reserved())
    return optimizer,metrics,indices


def train(args):
    validate_args(args)
    os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
    raw=args.input.read_bytes()
    if sha(raw)!=INPUT_SHA:raise ValueError('Exact frozen TRAIN packet bytes required')
    packet=json.loads(raw);rows=validate_training_packet(packet)
    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 required; no CPU/model fallback')
    started=time.monotonic();random.seed(args.seed);torch.manual_seed(args.seed);torch.cuda.manual_seed_all(args.seed)
    torch.backends.cuda.matmul.allow_tf32=False
    tokenizer=transformers.AutoTokenizer.from_pretrained(args.model_path,local_files_only=True)
    encoded=[encode_row(tokenizer,row,args.max_tokens) for row in rows]
    hashes=model_files(args.model_path)
    if digest(hashes)!=MODEL_FILES_SHA:raise ValueError('Exact immutable Llama8B model files required')
    sources={name:file_sha(ROOT/name) for name in SOURCES}
    args.output.mkdir(parents=True,exist_ok=False);(args.output/'train.json').write_bytes(raw)
    config=dict(algorithm=ALGORITHM,dtype_profile=PROFILE,input_sha256=sha(raw),model_path=str(args.model_path),
        model_files=hashes,seed=args.seed,lr=args.lr,requested_updates=STEPS,seconds=SECONDS,max_tokens=8192,
        train_ids=[r['id'] for r in rows],task_schedule=[rows[i]['id'] for i in schedule(32,STEPS,args.seed)],
        hypothesis='Sixteen whole-proof exposures improve transfer over the same32 tasks at100updates',
        stop='Exactly512 updates or600s total worker deadline;90s checkpoint reserve;36GiB allocated/reserved guard',
        measurement='SFT mechanics only; externally verified matched proof evaluations remain required',
        torch_version=torch.__version__,transformers_version=transformers.__version__,hardware=torch.cuda.get_device_name(),
        evidence=packet['evidence'],implementation_sha256=sources,cuda_cache_policy=CACHE_POLICY,
        initialization='fresh immutable base and fresh AdamW; no checkpoint resume',training_epochs=16)
    dump(args.output/'config.json',config)
    dump(args.output/'encodings.json',[dict(id=r['id'],**e) for r,e in zip(rows,encoded)])
    torch.cuda.reset_peak_memory_stats();net=load_policy(args.model_path);selected=select_final_layer(net,train=True)
    initial={name:p.detach().cpu().clone() for name,p in selected.items()}
    config.update(trainable_names=list(selected),trainable_dtypes={n:str(p.dtype) for n,p in selected.items()},
        trainable_parameters=sum(p.numel() for p in selected.values()),all_parameter_dtypes=sorted({str(p.dtype) for p in net.parameters()}))
    dump(args.output/'config.json',config)
    remaining=max(.000001,SECONDS-(time.monotonic()-started)-RESERVE)
    with (args.output/'steps.jsonl').open('x') as ledger:
        def emit(row):
            ledger.write(json.dumps(row)+'\n');ledger.flush();print(json.dumps(row),flush=True)
        optimizer,metrics,_=train_steps(net,selected,encoded,rows,STEPS,SEED,args.lr,remaining,'cuda',emit)
    checkpoint=args.output/'policy_optimizer.pt'
    result=save_reload(net,selected,optimizer,initial,config,metrics,encoded[0]['input_ids'],checkpoint,'cuda')
    summary=dict(**result,algorithm=ALGORITHM,updates=len(metrics),requested_updates=STEPS,
        train_tasks=32,attempted_train_tasks=len({r['task'] for r in metrics}),
        family_coverage=sorted({r['source_family'] for r in rows if r['id'] in {m['task'] for m in metrics}}),
        elapsed_s=time.monotonic()-started,cuda_peak_allocated=torch.cuda.max_memory_allocated(),
        cuda_peak_reserved=torch.cuda.max_memory_reserved(),evaluation_responses_forwarded=0,
        checkpoint=str(checkpoint),stop_reason='step_budget' if len(metrics)==STEPS else 'time_budget',
        task_update_counts=dict(Counter(r['task'] for r in metrics)))
    dump(args.output/'summary.json',summary)
    memory_guard(summary['cuda_peak_allocated'],summary['cuda_peak_reserved'])
    if sources!={name:file_sha(ROOT/name) for name in SOURCES}:raise ValueError('Training source changed during execution')
    return summary


def validate_training(path,frozen):
    config=json.loads((path/'config.json').read_bytes());summary=json.loads((path/'summary.json').read_bytes())
    expected=dict(model_files=frozen['model_files'],input_sha256=frozen['train_input_sha256'],
        train_ids=frozen['train_ids'],evidence=frozen['train_evidence'],dtype_profile=PROFILE,algorithm=ALGORITHM,
        requested_updates=STEPS,seconds=SECONDS,seed=SEED,lr=1e-5,max_tokens=8192,cuda_cache_policy=CACHE_POLICY,
        implementation_sha256={n:frozen['implementation_sha256'][n] for n in SOURCES},training_epochs=16,
        initialization='fresh immutable base and fresh AdamW; no checkpoint resume',
        task_schedule=[TRAIN_IDS[i] for i in schedule(32,STEPS,SEED)])
    if frozen['train_ids']!=TRAIN_IDS or frozen['train_input_sha256']!=INPUT_SHA or digest(frozen['model_files'])!=MODEL_FILES_SHA:
        raise ValueError('Exact frozen input/model population required')
    for key,value in expected.items():
        if config.get(key)!=value:raise ValueError('Training identity mismatch: '+key)
    for key,value in dict(reload_tensors_exact=True,reload_logits_exact=True,evaluation_responses_forwarded=0,
            train_tasks=32,attempted_train_tasks=32,updates=STEPS,requested_updates=STEPS,stop_reason='step_budget',
            task_update_counts={i:16 for i in TRAIN_IDS},algorithm=ALGORITHM).items():
        if summary.get(key)!=value:raise ValueError('Incomplete training/reload: '+key)
    if not isinstance(summary['parameter_delta_l2'],(float,int)) or not math.isfinite(summary['parameter_delta_l2']) or summary['parameter_delta_l2']<=0:
        raise ValueError('No finite positive parameter change')
    memory_guard(summary['cuda_peak_allocated'],summary['cuda_peak_reserved'])
    for key in ('torch_version','transformers_version'):
        if config.get(key)!=frozen['admissions']['base'][key]:raise ValueError('Training runtime changed')
    if (config.get('trainable_parameters')!=218112000 or len(config.get('trainable_names',[]))!=9 or
            set(config.get('trainable_dtypes',{}))!=set(config['trainable_names']) or
            set(config['trainable_dtypes'].values())!={'torch.float32'} or
            config.get('all_parameter_dtypes')!=['torch.bfloat16','torch.float32']):
        raise ValueError('Exact float32 final-layer parameter profile required')
    steps=read_rows(path/'steps.jsonl')
    if (len(steps)!=STEPS or [r['step'] for r in steps]!=list(range(1,STEPS+1)) or
            [r['task'] for r in steps]!=expected['task_schedule'] or
            Counter(r['task'] for r in steps)!={i:16 for i in TRAIN_IDS} or
            any(not math.isfinite(r[k]) for r in steps for k in ('loss','gradient_norm'))):
        raise ValueError('Actual512-step optimizer ledger incomplete/unhealthy')
    if file_sha(path/'policy_optimizer.pt')!=summary['checkpoint_sha256']:raise ValueError('Checkpoint bytes changed')
    return summary


def supervise(args,argv):
    validate_args(args)
    if args.output.exists():raise ValueError('Output must be new')
    process=subprocess.Popen([sys.executable,str(Path(__file__).resolve()),'_worker',*argv],start_new_session=True)
    def stop():
        try:os.killpg(process.pid,signal.SIGTERM)
        except ProcessLookupError:pass
        try:process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid,signal.SIGKILL);process.wait(timeout=5)
    previous=signal.getsignal(signal.SIGTERM)
    def terminated(signum,frame):raise SystemExit(128+signum)
    signal.signal(signal.SIGTERM,terminated)
    try:return process.wait(timeout=SECONDS)
    except subprocess.TimeoutExpired:
        stop()
        if args.output.exists():dump(args.output/'timeout.json',dict(status='supervisor_timeout',seconds=SECONDS,
            certified=False,checkpoint_reload_unverified=True))
        return 124
    except BaseException:
        stop();raise
    finally:signal.signal(signal.SIGTERM,previous)


def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='mode',required=True)
    p=sub.add_parser('train',aliases=['_worker'])
    for name in ('input','model-path','output'):p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--expected-input-sha256',required=True);p.add_argument('--seed',type=int,required=True)
    p.add_argument('--steps',type=int,default=STEPS);p.add_argument('--seconds',type=int,default=SECONDS)
    p.add_argument('--max-tokens',type=int,default=8192);p.add_argument('--lr',type=float,default=1e-5)
    args=parser.parse_args()
    if args.mode=='train':return supervise(args,sys.argv[2:])
    print(json.dumps(train(args)))


if __name__=='__main__':raise SystemExit(main() or 0)
