#!/usr/bin/env python3
"""Frozen14 prospective whole-proof EVAL. No training, repair, or population substitution."""
import argparse
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_cuda_eval import sha,digest,dump,decode_reply,trim_output,read_rows
from tools.proof_cuda_train import file_sha

BUDGET=dict(max_new_tokens=3072,max_tokens=8192,batch_size=1,seconds=1200,
    batch_seconds=180,seed=20260928,do_sample=False,num_beams=1,num_return_sequences=1,
    profile='frozen bf16 base with float32 final transformer layer; bf16 autocast')
MODEL_FILES_SHA='be21cca8df80e80b27b11aa238d8d77192e3c0e47a096224d1292559190a4cf9'
VERSIONS=dict(torch_version='2.11.0+cu128',transformers_version='5.6.2')
EOS_IDS=[128001,128008,128009]
CHECKPOINT_SHA='769115a0722f947efd1247bd66b6764ab82ba531671eaefab9e27be219d7aefa'
IMPLEMENTATION=('tools/proof_cuda_fresh_eval.py','tools/proof_fresh_packet.py',
    'tools/proof_cuda_eval.py','tools/proof_cuda_train.py','tools/proof_sequence_train.py',
    'tools/proof_candidate_rank.py','tools/proof_repair_pilot.py','tools/proof_whole_packet.py')


def validate_packet(raw,expected):
    from tools.proof_fresh_packet import validate_export
    if not isinstance(expected,str) or not re.fullmatch('[0-9a-f]{64}',expected) or sha(raw)!=expected:
        raise ValueError('Explicit expected fresh packet SHA mismatch')
    tasks=validate_export(json.loads(raw))
    if len(tasks)!=14 or any(t['split']!='fresh_evaluation' for t in tasks):
        raise ValueError('Full14 fresh evaluation only')
    return tasks


def checkpoint_identity(path,expected):
    if path is None:
        if expected is not None:raise ValueError('BASE cannot declare checkpoint')
        return None
    if expected!=CHECKPOINT_SHA or file_sha(path)!=expected:
        raise ValueError('Only pinned exposure checkpoint allowed')
    return expected


def runtime_versions():
    import torch,transformers
    return dict(torch_version=torch.__version__,transformers_version=transformers.__version__)


def source_identity():
    return {n:file_sha(ROOT/n) for n in IMPLEMENTATION}


def input_evidence(row):
    return {k:row[k] for k in ('id','input_tokens','input_token_ids_sha256','rendered_prompt_sha256')}


def encode_prompt(tokenizer,task):
    from tools.proof_cuda_eval import encode_prompt as encode
    row=encode(tokenizer,task)
    row.update(split=task['split'],status='ready' if row['input_tokens']+3072<=8192 else 'context_overflow')
    return row


def output_fields(tokens,eos_ids,reply):
    if (not tokens or len(tokens)>3072 or any(type(i) is not int or i<0 for i in tokens)
            or trim_output(tokens,eos_ids)!=tokens):raise ValueError('Invalid output tokens/EOS')
    eos=tokens[-1] in eos_ids;cap=len(tokens)==3072
    reason='eos' if eos else 'token_limit' if cap else 'time_limit'
    return dict(status='generation_time_limit' if reason=='time_limit' else 'generated',
        finish_reason=reason,eos_reached=eos,hit_token_limit=cap,token_ids=tokens,
        token_ids_sha256=digest(tokens),output_tokens=len(tokens),raw_reply=reply,raw_reply_sha256=sha(reply.encode()))


def admit(a):
    import transformers
    from tools.proof_cuda_train import model_files,PROFILE
    raw=a.prompts.read_bytes();tasks=validate_packet(raw,a.expected_input_sha256)
    checkpoint=checkpoint_identity(a.checkpoint,a.expected_checkpoint_sha256)
    files=model_files(a.model_path)
    if digest(files)!=MODEL_FILES_SHA or runtime_versions()!=VERSIONS or PROFILE!=BUDGET['profile']:
        raise ValueError('Pinned model/runtime required')
    if json.loads((a.model_path/'generation_config.json').read_bytes())['eos_token_id']!=EOS_IDS:
        raise ValueError('Pinned model EOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encoded=[encode_prompt(tokenizer,t) for t in tasks]
    if any(e['status']!='ready' for e in encoded):raise ValueError('Full context/output budget required')
    return dict(**BUDGET,**VERSIONS,prompts_sha256=sha(raw),model_files=files,
        model_files_sha256=digest(files),eos_token_ids=EOS_IDS,checkpoint_sha256=checkpoint,
        arm='base' if checkpoint is None else 'checkpoint',restore_exact=False,
        requested_task_ids=[t['id'] for t in tasks],input_evidence=list(map(input_evidence,encoded)),
        implementation_sha256=source_identity())


def validate_run(raw,expected,expected_checkpoint,config,rows,summary):
    tasks=validate_packet(raw,expected)
    if expected_checkpoint not in (None,CHECKPOINT_SHA):raise ValueError('Unsupported checkpoint')
    if (any(config.get(k)!=v for k,v in {**BUDGET,**VERSIONS}.items()) or
        config.get('eos_token_ids')!=EOS_IDS or config.get('model_files_sha256')!=MODEL_FILES_SHA or
        digest(config.get('model_files',{}))!=MODEL_FILES_SHA or
        config.get('checkpoint_sha256')!=expected_checkpoint or
        config.get('arm')!=('base' if expected_checkpoint is None else 'checkpoint') or
        config.get('restore_exact') is not True or config.get('prompts_sha256')!=expected or
        config.get('requested_task_ids')!=[t['id'] for t in tasks]):
        raise ValueError('Run model/budget/input identity mismatch')
    hashes=config.get('implementation_sha256',{})
    if set(hashes)!=set(IMPLEMENTATION) or any(not re.fullmatch('[0-9a-f]{64}',v) for v in hashes.values()):
        raise ValueError('Runtime source hashes required')
    if config.get('implementation_after_sha256') not in (None,hashes):raise ValueError('Generation source drift')
    evidence=config.get('input_evidence',[])
    if [e.get('id') for e in evidence]!=[t['id'] for t in tasks]:raise ValueError('Full input evidence required')
    for e in evidence:
        if (set(e)!={'id','input_tokens','input_token_ids_sha256','rendered_prompt_sha256'} or
            type(e['input_tokens']) is not int or not 0<e['input_tokens']<=5120 or
            any(not isinstance(e[k],str) or not re.fullmatch('[0-9a-f]{64}',e[k])
                for k in ('input_token_ids_sha256','rendered_prompt_sha256'))):raise ValueError('Invalid input evidence')
    if (len(rows)>14 or [r['id'] for r in rows]!=[t['id'] for t in tasks[:len(rows)]] or
        summary.get('requested_tasks')!=14 or summary.get('completed_rows')!=len(rows) or
        summary.get('unattempted_task_ids')!=[t['id'] for t in tasks[len(rows):]] or
        summary.get('termination') not in {'complete','phase_timeout','batch_timeout','worker_error'} or
        (len(rows)==14)!=(summary['termination']=='complete')):
        raise ValueError('Full denominator/order/termination mismatch')
    if summary['termination']=='complete' and config.get('implementation_after_sha256')!=hashes:
        raise ValueError('Complete generation requires after identity')
    for task,row,ev in zip(tasks,rows,evidence):
        ids=row.get('input_token_ids')
        if (row.get('split')!='fresh_evaluation' or row.get('prompt_sha256')!=task['prompt_sha256'] or
            not isinstance(ids,list) or not ids or any(type(i) is not int or i<0 for i in ids) or
            len(ids)!=row.get('input_tokens') or digest(ids)!=row.get('input_token_ids_sha256') or
            sha(row['rendered_prompt'].encode())!=row.get('rendered_prompt_sha256') or input_evidence(row)!=ev):
            raise ValueError('Input bytes/tokens mismatch')
        if row.get('status') not in {'generated','generation_time_limit'}:raise ValueError('Unadmitted row status')
        fields=output_fields(row['token_ids'],set(EOS_IDS),row['raw_reply'])
        if any(row.get(k)!=v for k,v in fields.items()):raise ValueError('Output/finish accounting mismatch')
    return tasks


def worker(a):
    import torch,transformers
    from tools.proof_cuda_train import load_policy,restore_policy,model_files
    os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
    config=json.loads((a.output/'config.json').read_bytes())
    tasks=validate_packet(a.prompts.read_bytes(),config['prompts_sha256'])
    if (source_identity()!=config['implementation_sha256'] or runtime_versions()!=VERSIONS or
        model_files(a.model_path)!=config['model_files']):raise ValueError('Frozen runtime drift')
    checkpoint_identity(a.checkpoint,config['checkpoint_sha256'])
    torch.set_num_threads(4);torch.manual_seed(BUDGET['seed']);torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats();net=load_policy(a.model_path,device='cuda')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    if a.checkpoint:
        saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
        selected=restore_policy(net,saved,config['model_files'])
        if not all(torch.equal(p.detach().cpu(),saved['trainable_state'][n]) for n,p in selected.items()):
            raise ValueError('Exact checkpoint restore failed')
        del saved
    if net.generation_config.eos_token_id!=EOS_IDS:raise ValueError('Model EOS changed')
    config['restore_exact']=True;dump(a.output/'config.json',config)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if type(pad) is not int:raise ValueError('Scalar pad required')
    with (a.output/'generations.jsonl').open('x') as stream:
        for task,ev in zip(tasks,config['input_evidence']):
            row=encode_prompt(tokenizer,task)
            if row['status']!='ready' or input_evidence(row)!=ev:raise ValueError('Prompt reconstruction changed')
            inputs=torch.tensor([row['input_token_ids']],device='cuda')
            dump(a.output/'batch.json',dict(active=True,started=time.time(),id=task['id']))
            with torch.inference_mode(),torch.autocast('cuda',dtype=torch.bfloat16):
                output=net.generate(input_ids=inputs,attention_mask=torch.ones_like(inputs),
                    do_sample=False,num_beams=1,num_return_sequences=1,max_new_tokens=3072,max_time=180,pad_token_id=pad)
            torch.cuda.synchronize();dump(a.output/'batch.json',dict(active=False))
            ids=trim_output(output[0,inputs.shape[1]:].tolist(),set(EOS_IDS))
            row.update(output_fields(ids,set(EOS_IDS),decode_reply(tokenizer,ids)))
            stream.write(json.dumps(row)+'\n');stream.flush()
    config['implementation_after_sha256']=source_identity()
    if config['implementation_after_sha256']!=config['implementation_sha256']:raise ValueError('Generation runtime drift')
    dump(a.output/'config.json',config)
    dump(a.output/'runtime.json',dict(parameter_updates=0,gpu=torch.cuda.get_device_name(),
        cuda_peak_allocated_bytes=torch.cuda.max_memory_allocated(),cuda_peak_reserved_bytes=torch.cuda.max_memory_reserved()))


def generate(a):
    started=time.monotonic();config=admit(a)
    tasks=validate_packet(a.prompts.read_bytes(),a.expected_input_sha256)
    dump(a.output/'config.json',config)
    command=[sys.executable,str(Path(__file__).resolve()),'_worker','--prompts',str(a.prompts),
        '--model-path',str(a.model_path),'--output',str(a.output)]
    if a.checkpoint:command+=['--checkpoint',str(a.checkpoint)]
    termination=None
    with (a.output/'console.log').open('x') as log:
        process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        previous=signal.getsignal(signal.SIGTERM)
        def terminated(signum,frame):raise SystemExit(128+signum)
        signal.signal(signal.SIGTERM,terminated)
        try:
            while process.poll() is None:
                if time.monotonic()-started>=1200:termination='phase_timeout'
                if (a.output/'batch.json').exists():
                    batch=json.loads((a.output/'batch.json').read_bytes())
                    if batch.get('active') and time.time()-batch['started']>=180:termination='batch_timeout'
                if termination:break
                time.sleep(.25)
        finally:
            if process.poll() is None:os.killpg(process.pid,signal.SIGKILL);process.wait()
            signal.signal(signal.SIGTERM,previous)
    rows=read_rows(a.output/'generations.jsonl')
    termination=termination or ('complete' if process.returncode==0 and len(rows)==14 else 'worker_error')
    dump(a.output/'summary.json',dict(requested_tasks=14,completed_rows=len(rows),termination=termination,
        returncode=process.returncode,unattempted_task_ids=[t['id'] for t in tasks[len(rows):]],
        elapsed_seconds=time.monotonic()-started,training_authorized=False))


def verify(a):
    import transformers
    from tools.proof_fresh_packet import local_load_tasks
    from tools.proof_hierarchical_packet import runtime_identity
    from tools.proof_cuda_eval import validate_tokenization
    from harness.proof_gen import extract_proof_block
    from harness.proof_full_fragment_check import certify_fragment
    raw=a.prompts.read_bytes()
    packet,tasks=local_load_tasks(a.manifest,a.expected_manifest_sha256)
    if raw!=(json.dumps(packet,indent=2)+'\n').encode():raise ValueError('Local controlled export differs')
    config=json.loads((a.generations/'config.json').read_bytes())
    if source_identity()!=config.get('implementation_sha256'):
        raise ValueError('Generation implementation differs from verifier reconstruction')
    rows=read_rows(a.generations/'generations.jsonl')
    exported=validate_run(raw,a.expected_input_sha256,a.expected_checkpoint_sha256,config,rows,
        json.loads((a.generations/'summary.json').read_bytes()))
    expected={n:h for n,h in config['model_files'].items() if n.endswith('.json') or n in {'tokenizer.model','chat_template.jinja'}}
    actual={p.name:file_sha(p) for p in a.tokenizer_path.iterdir() if p.is_file() and
        (p.suffix=='.json' or p.name in {'tokenizer.model','chat_template.jinja'})}
    if expected!=actual:raise ValueError('Exact tokenizer files required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    for task,row in zip(exported,rows):
        validate_tokenization(tokenizer,task,row)
        if decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:raise ValueError('Exact output byte reconstruction failed')
    def local_identity():
        paths={ROOT/n for n in IMPLEMENTATION}
        paths.update([Path(__file__),a.manifest,a.prompts])
        paths.update(a.tokenizer_path/n for n in expected)
        paths.update(a.generations/n for n in ('config.json','generations.jsonl','summary.json'))
        paths.update(ROOT/n for n in ('harness/proof_full_fragment_check.py','harness/proof_fragment_check.py',
                                      'harness/proof_gen.py','harness/runner.py'))
        for t in tasks:paths.update(map(Path,[t['source_path'],*t['dependencies']]))
        return {str(p):file_sha(p) for p in sorted(paths)}
    sources=local_identity();before=runtime_identity();results=[];complete=False
    dump(a.output/'verifier_before.json',before)
    generated={r['id']:r for r in rows}
    families={family:{t['id'] for t in tasks if t['source_family']==family}
              for family in sorted({t['source_family'] for t in tasks})}
    def save():
        dump(a.output/'summary.json',dict(requested_tasks=14,split='fresh_evaluation',
            method='Prospective whole-target proof generation; greedy pass@1, no repairs',
            training_authorized=False,verification_complete=complete,timeout_per_module=30,
            identity=config,source_identity=sources,certified_tasks=sum(r['certified'] for r in results) if complete else 0,
            provisional_certified_tasks=sum(r['certified'] for r in results),
            per_family={family:dict(requested_tasks=len(ids),
                generated_tasks=sum(r['id'] in ids and r['status']=='generated' for r in rows),
                certified_tasks=sum(r['id'] in ids and r['certified'] for r in results) if complete else 0)
                for family,ids in families.items()},
            status_counts={s:sum(r['status']==s for r in results) for s in sorted({r['status'] for r in results})},
            unmeasured_tasks=sum(r['status'] in {'generation_unattempted','generation_time_limit','infrastructure_error',
                'timeout','error','unrecognized_output'} for r in results),
            accounted_tasks=len(results)))
    save()
    with (a.output/'rows.jsonl').open('x') as stream:
        for task in tasks:
            if local_identity()!=sources:raise ValueError('Local verifier/source drift')
            row=generated.get(task['id']);result=dict(id=task['id'],split='fresh_evaluation',certified=False,status='generation_unattempted')
            if row:
                result['status']=row['status']
                if row['status']=='generated':
                    fragment=extract_proof_block(row['raw_reply'])
                    result.update(fragment=fragment,raw_reply_sha256=row['raw_reply_sha256'],status='no_proof_fragment')
                    if fragment is not None:
                        result.update(certify_fragment(task['prefix'],fragment,task['suffix'],theorem_name=task['theorem_name'],
                            dependencies=tuple(map(Path,task['dependencies'])),work_root=a.output/'checks'/task['id'],timeout=30))
            results.append(result);stream.write(json.dumps(result)+'\n');stream.flush();save()
            if local_identity()!=sources:raise ValueError('Local verifier/source drift')
    after=runtime_identity();dump(a.output/'verifier_after.json',after)
    if before!=after:raise ValueError('Verifier library/tool identity changed')
    complete=True;save()


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=['generate','verify','_worker'])
    for name in ('prompts','model-path','checkpoint','tokenizer-path','generations','manifest','output'):
        p.add_argument('--'+name,type=Path,required=name=='output')
    for name in ('expected-input-sha256','expected-checkpoint-sha256','expected-manifest-sha256'):p.add_argument('--'+name)
    a=p.parse_args()
    needed={'generate':['prompts','model_path','expected_input_sha256'],
            '_worker':['prompts','model_path'],'verify':['prompts','manifest','expected_manifest_sha256',
            'generations','tokenizer_path','expected_input_sha256']}[a.mode]
    if any(getattr(a,n) is None for n in needed):p.error('Missing required mode arguments')
    a.output=a.output.resolve()
    if a.mode!='_worker':a.output.mkdir(parents=True,exist_ok=False)
    globals()[a.mode.removeprefix('_')](a)


if __name__=='__main__':main()
