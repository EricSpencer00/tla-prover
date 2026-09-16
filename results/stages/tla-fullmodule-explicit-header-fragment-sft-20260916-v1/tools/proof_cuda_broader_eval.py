#!/usr/bin/env python3
"""32 whole-target TRAIN proofs +4 unchanged CRDT DEV; developmental free generation."""
import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_cuda_eval import sha, digest, dump, decode_reply, trim_output, read_rows

from tools.proof_broader_packet import MANIFEST_SHA256, SOURCE_MANIFEST_SHA256, export_tasks, validate_export
from tools.proof_cuda_train import file_sha
import re

BUDGET = dict(max_new_tokens=3072, max_tokens=8192, batch_size=1, seconds=1200,
              batch_seconds=180, seed=20260928, do_sample=False, num_beams=1,
              num_return_sequences=1, profile='frozen bf16 base with float32 final transformer layer; bf16 autocast')
IMPLEMENTATION = ('tools/proof_cuda_broader_eval.py', 'tools/proof_broader_packet.py', 'tools/proof_whole_packet.py',
                  'tools/proof_cuda_eval.py', 'tools/proof_cuda_train.py',
                  'tools/proof_sequence_train.py', 'tools/proof_repair_pilot.py',
                  'tools/proof_candidate_rank.py')


MODEL_FILES_SHA='be21cca8df80e80b27b11aa238d8d77192e3c0e47a096224d1292559190a4cf9'
FIRST_VERSIONS=dict(torch_version='2.11.0+cu128',transformers_version='5.6.2')
EOS_IDS=[128001,128008,128009]


def runtime_versions():
    import torch
    import transformers
    return dict(torch_version=torch.__version__,transformers_version=transformers.__version__)


def input_evidence(row):
    return {k:row[k] for k in ('id','input_tokens','input_token_ids_sha256','rendered_prompt_sha256')}


def admit(prompts,expected_input_sha256,model_path,checkpoint=None):
    """Actual CPU-only read-only admission. Caller freezes returned checkpoint hash."""
    from tools.proof_cuda_train import model_files, PROFILE
    import transformers
    prompts=Path(prompts);model_path=Path(model_path)
    raw=prompts.read_bytes();tasks=validate_export(json.loads(raw))
    if not re.fullmatch('[0-9a-f]{64}',expected_input_sha256 or '') or sha(raw)!=expected_input_sha256:
        raise ValueError('Expected broader packet hash mismatch')
    files=model_files(model_path)
    if digest(files)!=MODEL_FILES_SHA or PROFILE!=BUDGET['profile']:
        raise ValueError('Pinned model/profile mismatch')
    versions=runtime_versions()
    if versions!=FIRST_VERSIONS:raise ValueError('Pinned runtime versions required')
    eos=json.loads((model_path/'generation_config.json').read_bytes())['eos_token_id']
    if eos!=EOS_IDS:raise ValueError('Pinned model EOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(model_path,local_files_only=True)
    inputs=[]
    for task in tasks:
        encoded=encode_prompt(tokenizer,task)
        if encoded['status']!='ready':raise ValueError('Full prompt and output context budget required')
        inputs.append(input_evidence(encoded))
    return dict(**BUDGET,prompts_sha256=sha(raw),model_files=files,
        model_files_sha256=digest(files),requested_task_ids=[t['id'] for t in tasks],restore_exact=False,
        checkpoint_sha256=file_sha(Path(checkpoint)) if checkpoint else None,eos_token_ids=EOS_IDS,**versions,
        arm='checkpoint' if checkpoint else 'base',input_evidence=inputs,
        implementation_sha256={n:sha((ROOT/n).read_bytes()) for n in IMPLEMENTATION})


def encode_prompt(tokenizer, task):
    from tools.proof_cuda_eval import encode_prompt as inference_encoder
    row = inference_encoder(tokenizer, task)
    row.update(split=task['split'], status='context_overflow' if row['input_tokens']+3072>8192 else 'ready')
    return row


def output_fields(tokens, eos_ids, reply):
    """max_time is not EOS: short unfinished replies remain unmeasured."""
    if not tokens or len(tokens)>BUDGET['max_new_tokens']:
        raise ValueError('invalid output length')
    if trim_output(tokens,eos_ids)!=tokens:
        raise ValueError('tokens after first EOS')
    eos = tokens[-1] in eos_ids
    cap = len(tokens)==BUDGET['max_new_tokens']
    reason = 'eos' if eos else 'token_limit' if cap else 'time_limit'
    return dict(status='generation_time_limit' if reason=='time_limit' else 'generated',
                finish_reason=reason, eos_reached=eos, hit_token_limit=cap,
                token_ids=tokens,token_ids_sha256=digest(tokens),output_tokens=len(tokens),
                raw_reply=reply,raw_reply_sha256=sha(reply.encode()))


def validate_run(raw, config, rows, summary):
    tasks = validate_export(json.loads(raw))
    if (any(config.get(k)!=v for k,v in FIRST_VERSIONS.items())
            or config.get('eos_token_ids')!=EOS_IDS or config.get('model_files_sha256')!=MODEL_FILES_SHA):
        raise ValueError('Pinned model/libraries/EOS mismatch')
    if any(not isinstance(v,str) or not re.fullmatch('[0-9a-f]{64}',v)
           for v in config.get('implementation_sha256',{}).values()):
        raise ValueError('Invalid runtime hash')
    if config.get('checkpoint_sha256') is not None and not re.fullmatch('[0-9a-f]{64}',config['checkpoint_sha256']):
        raise ValueError('Invalid checkpoint hash')
    evidence=config.get('input_evidence',[])
    if [e.get('id') for e in evidence]!=[t['id'] for t in tasks]:
        raise ValueError('Full input evidence required')
    for e in evidence:
        if (set(e)!={'id','input_tokens','input_token_ids_sha256','rendered_prompt_sha256'}
                or type(e['input_tokens']) is not int or not 0<e['input_tokens']<=5120
                or any(not isinstance(e[k],str) or not re.fullmatch('[0-9a-f]{64}',e[k])
                       for k in ('input_token_ids_sha256','rendered_prompt_sha256'))):
            raise ValueError('Invalid frozen input evidence')
    if summary.get('requested_tasks')!=36:
        raise ValueError('Full denominator required')
    if any(config.get(k)!=v for k,v in BUDGET.items()):
        raise ValueError('frozen budget/profile mismatch')
    if (config.get('prompts_sha256') != sha(raw) or not config.get('model_files')
            or config.get('model_files_sha256') != digest(config['model_files'])
            or config.get('requested_task_ids') != [t['id'] for t in tasks]
            or config.get('restore_exact') is not True
            or set(config.get('implementation_sha256',{})) != set(IMPLEMENTATION)):
        raise ValueError('run provenance mismatch')
    if config.get('arm') not in {'base','checkpoint'} or (config['arm']=='base') != (config.get('checkpoint_sha256') is None):
        raise ValueError('checkpoint arm mismatch')
    if [r['id'] for r in rows] != [t['id'] for t in tasks[:len(rows)]]:
        raise ValueError('reordered/duplicate/interior missing rows')
    if summary.get('unattempted_task_ids') != [t['id'] for t in tasks[len(rows):]]:
        raise ValueError('unattempted suffix mismatch')
    if summary.get('termination') not in {'complete','phase_timeout','batch_timeout','worker_error'}:
        raise ValueError('undeclared termination')
    if (len(rows)==36) != (summary['termination']=='complete'):
        raise ValueError('completion accounting mismatch')
    eos=config.get('eos_token_ids')
    if not isinstance(eos,list) or not eos or any(type(i) is not int or i<0 for i in eos):
        raise ValueError('EOS identity required')
    for task,row in zip(tasks,rows):
        if input_evidence(row)!=evidence[tasks.index(task)]:raise ValueError('Frozen input evidence mismatch')
        ids=row.get('input_token_ids')
        if (row.get('split')!=task['split'] or row.get('prompt_sha256')!=task['prompt_sha256']
                or not isinstance(ids,list) or not ids or any(type(i) is not int or i<0 for i in ids)
                or row.get('input_tokens')!=len(ids) or row.get('input_token_ids_sha256')!=digest(ids)
                or sha(row['rendered_prompt'].encode())!=row.get('rendered_prompt_sha256')):
            raise ValueError('input provenance mismatch')
        if row.get('status')=='context_overflow':
            if len(ids)+3072<=8192 or 'token_ids' in row:
                raise ValueError('invalid context overflow')
        elif row.get('status') in {'generated','generation_time_limit'}:
            tokens=row.get('token_ids')
            if (len(ids)+3072>8192 or not isinstance(tokens,list) or not tokens or len(tokens)>3072
                    or any(type(i) is not int or i<0 for i in tokens)
                    or row.get('output_tokens')!=len(tokens) or row.get('token_ids_sha256')!=digest(tokens)
                    or row.get('hit_token_limit') is not (len(tokens)==3072)
                    or sha(row['raw_reply'].encode())!=row.get('raw_reply_sha256')):
                raise ValueError('output provenance mismatch')
            expected=output_fields(tokens, set(config['eos_token_ids']), row['raw_reply'])
            if any(row.get(k)!=v for k,v in expected.items()):
                raise ValueError('termination/token provenance mismatch')
        else:
            raise ValueError('unsupported row status')
    return tasks


def worker(a):
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, restore_policy, model_files, PROFILE
    os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
    config=json.loads((a.output/'config.json').read_bytes())
    if sha(a.prompts.read_bytes())!=config['prompts_sha256']:
        raise ValueError('prompts changed after freeze')
    for name,expected in config['implementation_sha256'].items():
        if sha((ROOT/name).read_bytes())!=expected: raise ValueError('runtime source changed')
    if PROFILE!=BUDGET['profile'] or model_files(a.model_path)!=config['model_files']:
        raise ValueError('model/profile mismatch')
    if runtime_versions()!=FIRST_VERSIONS:raise ValueError('Runtime libraries changed')
    if (file_sha(a.checkpoint) if a.checkpoint else None)!=config['checkpoint_sha256']:
        raise ValueError('Checkpoint changed after admission')
    torch.set_num_threads(4);torch.manual_seed(BUDGET['seed'])
    torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats()
    net=load_policy(a.model_path,device='cuda')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    if a.checkpoint:
        if file_sha(a.checkpoint)!=config['checkpoint_sha256']: raise ValueError('checkpoint changed')
        saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
        selected=restore_policy(net,saved,config['model_files'])
        if not all(torch.equal(p.detach().cpu(),saved['trainable_state'][n]) for n,p in selected.items()):
            raise ValueError('checkpoint exact restore failed')
        del saved
    config.update(restore_exact=True,torch_version=torch.__version__,transformers_version=transformers.__version__)
    dump(a.output/'config.json',config)
    eos=net.generation_config.eos_token_id
    eos=set(eos if isinstance(eos,list) else [eos])
    if not eos or any(type(i) is not int or i < 0 for i in eos): raise ValueError('valid EOS IDs required')
    if sorted(eos)!=config['eos_token_ids']:raise ValueError('Model EOS changed')
    config['eos_token_ids']=sorted(eos)
    dump(a.output/'config.json',config)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if not isinstance(pad,int): raise ValueError('scalar pad required')
    len_completed=0
    with (a.output/'generations.jsonl').open('x') as stream:
        for task in validate_export(json.loads(a.prompts.read_bytes())):
            row=encode_prompt(tokenizer,task)
            if input_evidence(row)!=config['input_evidence'][len_completed]:raise ValueError('Input reconstruction changed')
            len_completed+=1
            if row['status']=='ready':
                inputs=torch.tensor([row['input_token_ids']],device='cuda')
                dump(a.output/'batch.json',dict(active=True,started=time.time(),id=task['id']))
                with torch.inference_mode(),torch.autocast('cuda',dtype=torch.bfloat16):
                    output=net.generate(input_ids=inputs,attention_mask=torch.ones_like(inputs),
                        do_sample=False,num_beams=1,num_return_sequences=1,max_new_tokens=3072,max_time=180,pad_token_id=pad)
                torch.cuda.synchronize()
                dump(a.output/'batch.json',dict(active=False))
                ids=trim_output(output[0,inputs.shape[1]:].tolist(),eos)
                reply=decode_reply(tokenizer,ids)
                row.update(output_fields(ids, eos, reply))
            stream.write(json.dumps(row)+'\n');stream.flush()
            dump(a.output/'runtime.json',dict(cuda_peak_allocated_bytes=torch.cuda.max_memory_allocated(),
                cuda_peak_reserved_bytes=torch.cuda.max_memory_reserved(),gpu=torch.cuda.get_device_name(),parameter_updates=0))


def generate(a):
    started=time.monotonic()
    config=admit(a.prompts,a.expected_input_sha256,a.model_path,a.checkpoint)
    tasks=validate_export(json.loads(a.prompts.read_bytes()))
    dump(a.output/'config.json',config)
    command=[sys.executable,str(Path(__file__).resolve()),'_worker','--prompts',str(a.prompts),
             '--model-path',str(a.model_path),'--output',str(a.output)]
    if a.checkpoint:command+=['--checkpoint',str(a.checkpoint)]
    termination=None
    with (a.output/'console.log').open('w') as log:
        process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        previous=signal.getsignal(signal.SIGTERM)
        def terminated(signum,frame): raise SystemExit(128+signum)
        signal.signal(signal.SIGTERM,terminated)
        try:
            while process.poll() is None:
                if time.monotonic()-started>=BUDGET['seconds']: termination='phase_timeout'
                if (a.output/'batch.json').exists():
                    batch=json.loads((a.output/'batch.json').read_bytes())
                    if batch.get('active') and time.time()-batch['started']>=180: termination='batch_timeout'
                if termination: break
                time.sleep(.25)
        finally:
            if process.poll() is None: os.killpg(process.pid,signal.SIGKILL);process.wait()
            signal.signal(signal.SIGTERM,previous)
    rows=read_rows(a.output/'generations.jsonl')
    termination=termination or ('complete' if process.returncode==0 and len(rows)==36 else 'worker_error')
    dump(a.output/'summary.json',dict(termination=termination,returncode=process.returncode,requested_tasks=36,
        completed_rows=len(rows),generated_tasks=sum(r['status']=='generated' for r in rows),
        per_split={s:dict(requested_tasks=n,completed_rows=sum(r['split']==s for r in rows),
            generated_tasks=sum(r['split']==s and r['status']=='generated' for r in rows))
            for s,n in [('train',32),('development',4)]},
        unattempted_task_ids=[t['id'] for t in tasks[len(rows):]],elapsed_seconds=time.monotonic()-started))


def verify(a):
    from tools.proof_hierarchical_packet import runtime_identity
    from harness.proof_gen import extract_proof_block
    from harness.proof_fragment_check import certify_fragment as repair_certify
    from harness.proof_full_fragment_check import certify_fragment as whole_certify
    from tools.proof_cuda_eval import validate_tokenization
    import transformers
    raw=a.prompts.read_bytes();packet,tasks=export_tasks()
    if raw!=(json.dumps(packet,indent=2)+'\n').encode(): raise ValueError('export differs from exact local manifest')
    config=json.loads((a.generations/'config.json').read_bytes())
    rows=read_rows(a.generations/'generations.jsonl')
    validate_run(raw,config,rows,json.loads((a.generations/'summary.json').read_bytes()))
    expected={n:h for n,h in config['model_files'].items() if n.endswith('.json') or n in {'tokenizer.model','chat_template.jinja'}}
    actual={p.name:sha(p.read_bytes()) for p in a.tokenizer_path.iterdir() if p.is_file()
            and (p.suffix=='.json' or p.name in {'tokenizer.model','chat_template.jinja'})}
    if actual!=expected: raise ValueError('exact tokenizer artifact set/hash required')
    model_eos=json.loads((a.tokenizer_path/'generation_config.json').read_bytes())['eos_token_id']
    model_eos=model_eos if isinstance(model_eos,list) else [model_eos]
    if config['eos_token_ids']!=sorted(set(model_eos)):
        raise ValueError('EOS differs from frozen model generation config')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    for task,row in zip(packet['tasks'],rows):
        validate_tokenization(tokenizer,task,row)
        if row['status']=='generation_time_limit' and decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
            raise ValueError('time-limited output decode mismatch')
    generated={r['id']:r for r in rows};results=[]
    verification_complete=False
    populations={'original6':[t['id'] for t in tasks[:6]],
                 'new26':[t['id'] for t in tasks[6:32]],'development':[t['id'] for t in tasks[32:]]}
    def source_identity():
        paths={ROOT/n for n in IMPLEMENTATION}
        for task in tasks:
            paths.add(Path(task['source_path']))
            paths.update(Path(p) for p in task['dependencies'])
        return {str(p):file_sha(p) for p in sorted(paths)}
    frozen_sources=source_identity()
    verifier_before=runtime_identity()
    dump(a.output/'verifier_before.json',verifier_before)
    def save():
        dump(a.output/'summary.json',dict(manifest_sha256=MANIFEST_SHA256,identity=config,
            method='whole-target TRAIN construction and unchanged DEV repair; greedy pass@1; reused development, not generalization',
            timeout_per_module=30,requested_tasks=36,verification_complete=verification_complete,
            source_identity=frozen_sources,
            per_population={name:dict(requested_tasks=len(ids),
                generated_tasks=sum(r['id'] in ids and r['status']=='generated' for r in rows),
                certified_tasks=sum(r['id'] in ids and r['certified'] for r in results))
                for name,ids in populations.items()},
            status_counts={status:sum(r['status']==status for r in results)
                           for status in sorted({r['status'] for r in results})},
            per_split={s:dict(requested_tasks=n,generated_tasks=sum(r['split']==s and r['status']=='generated' for r in rows),
                certified_tasks=sum(r['split']==s and r['certified'] for r in results),
                checked_tasks=sum(r['split']==s and 'returncode' in r for r in results)) for s,n in [('train',32),('development',4)]}))
    def invalidate(reason):
        for result in results:
            result.update(certified=False,status='verification_identity_changed')
        save()
        dump(a.output/'failure.json',dict(reason=reason,verification_complete=False))
        raise ValueError(reason)
    save()
    with (a.output/'rows.jsonl').open('x') as stream:
        for task in tasks:
            if source_identity()!=frozen_sources:invalidate('Verification source/runtime drift')
            row=generated.get(task['id'])
            result=dict(id=task['id'],split=task['split'],certified=False,status='generation_unattempted')
            if row:
                result['status']=row['status']
                if row['status']=='generated':
                    fragment=extract_proof_block(row['raw_reply'])
                    result.update(fragment=fragment,raw_reply_sha256=row['raw_reply_sha256'],status='no_proof_fragment')
                    if fragment is not None:
                        certify_fragment = whole_certify if task['split']=='train' else repair_certify
                        result['fragment_contract']='full-proof-fragment-v1' if task['split']=='train' else 'legacy-repair'
                        result.update(certify_fragment(task['prefix'],fragment,task['suffix'],theorem_name=task['theorem_name'],
                            dependencies=tuple(Path(p) for p in task['dependencies']),work_root=a.output/'checks'/task['id'],timeout=30))
            if source_identity()!=frozen_sources:invalidate('Verification source/runtime drift')
            results.append(result);stream.write(json.dumps(result)+'\n');stream.flush();save()
    verifier_after=runtime_identity()
    dump(a.output/'verifier_after.json',verifier_after)
    if verifier_after!=verifier_before:
        invalidate('Verifier runtime/library identity changed')
    verification_complete=True
    save()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--expected-input-sha256')
    p.add_argument('mode',choices=['prepare','generate','verify','_worker'])
    for name in ('manifest','prompts','model-path','checkpoint','tokenizer-path','generations','output'):
        p.add_argument('--'+name,type=Path,required=name=='output')
    a=p.parse_args()
    required={'prepare':[],'generate':['prompts','model_path','expected_input_sha256'],'_worker':['prompts','model_path'],
              'verify':['prompts','generations','tokenizer_path']}[a.mode]
    if any(getattr(a,n) is None for n in required):p.error('missing required mode argument')
    a.output=a.output.resolve()
    if a.mode!='_worker':a.output.mkdir(parents=True,exist_ok=False)
    if a.mode=='prepare':dump(a.output/'prompts.json',export_tasks()[0])
    else:globals()[a.mode.removeprefix('_')](a)


if __name__=='__main__':main()
