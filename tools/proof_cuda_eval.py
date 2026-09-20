#!/usr/bin/env python3
"""Full119 free proof generation, sharded CUDA inference and strict local checks."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'
BUDGET = dict(max_new_tokens=512, max_tokens=8192, batch_size=2,
              seconds=1200, batch_seconds=90, shard_count=4, do_sample=False,
              num_beams=1, num_return_sequences=1,
              padding_side='left', seed=20260922, profile=PROFILE)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(value):
    return sha(json.dumps(value, sort_keys=True, separators=(',', ':')).encode())


def dump(path, data):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def export_tasks(manifest):
    from tools.proof_official_rank import freeze_tasks
    tasks = freeze_tasks(manifest)
    return dict(schema=1, split='official_test', requested_tasks=119,
        manifest_sha256=sha(manifest.read_bytes()), reference_fragments_exported=False,
        candidates_exported=False,
        tasks=[{k:t[k] for k in ('id', 'prompt', 'prompt_sha256')} for t in tasks],
        sources=[{k:t[k] for k in ('id', 'source_sha256', 'category', 'theorem_name')} for t in tasks]), tasks


def validate_export(data):
    if (set(data) != {'schema', 'split', 'requested_tasks', 'manifest_sha256',
            'reference_fragments_exported', 'candidates_exported', 'tasks', 'sources'}
            or data['schema'] != 1 or data['split'] != 'official_test'
            or data['requested_tasks'] != 119 or data['reference_fragments_exported'] is not False
            or data['candidates_exported'] is not False):
        raise ValueError('official prompt export contract mismatch')
    rows = data['tasks']
    if len(rows) != 119 or len({t['id'] for t in rows}) != 119:
        raise ValueError('full119 unique population required')
    for t in rows:
        if (set(t) != {'id','prompt','prompt_sha256'} or not isinstance(t['prompt'], str)
                or t['prompt_sha256'] != sha(t['prompt'].encode())):
            raise ValueError('prompt fields/hash mismatch')
    if [t['id'] for t in rows] != [s['id'] for s in data['sources']]:
        raise ValueError('source population mismatch')
    for source in data['sources']:
        if set(source) != {'id','source_sha256','category','theorem_name'}:
            raise ValueError('unexpected source metadata')
    return rows


def shard_tasks(tasks, index, count=4):
    if count != 4 or not 0 <= index < count:
        raise ValueError('exactly four strided shards required')
    return tasks[index::count]


def encode_prompt(tokenizer, task):
    rendered = tokenizer.apply_chat_template([dict(role='user', content=task['prompt'])],
                                             tokenize=False, add_generation_prompt=True)
    ids = tokenizer(rendered, add_special_tokens=False, truncation=False)['input_ids']
    if not ids or any(type(x) is not int or x < 0 for x in ids):
        raise ValueError('invalid input token IDs')
    return dict(id=task['id'], prompt_sha256=task['prompt_sha256'],
                rendered_prompt=rendered, rendered_prompt_sha256=sha(rendered.encode()),
                input_token_ids=ids, input_token_ids_sha256=digest(ids), input_tokens=len(ids),
                status='context_overflow' if len(ids)+512 > 8192 else 'ready')


def left_pad(rows, pad_id):
    width = max(len(r['input_token_ids']) for r in rows)
    return dict(input_ids=[[pad_id]*(width-r['input_tokens'])+r['input_token_ids'] for r in rows],
                attention_mask=[[0]*(width-r['input_tokens'])+[1]*r['input_tokens'] for r in rows])


def trim_output(ids, eos_ids):
    for i, token in enumerate(ids):
        if token in eos_ids:
            return ids[:i+1]
    return ids


def decode_reply(tokenizer, ids):
    """Preserve the saved transformers-5.6 decoder contract across versions.

    Newer BPE backends silently skip configured whitespace cleanup. Decode
    without cleanup, then apply the tokenizer's configured legacy cleanup
    explicitly, matching the immutable BASE replies rather than changing them.
    """
    text = tokenizer.decode(ids, skip_special_tokens=True,
                            clean_up_tokenization_spaces=False)
    return (tokenizer.clean_up_tokenization(text)
            if getattr(tokenizer, 'clean_up_tokenization_spaces', False)
            else text)


def validate_tokenization(tokenizer, task, row):
    encoded=encode_prompt(tokenizer,task)
    for key in ('rendered_prompt','rendered_prompt_sha256','input_token_ids','input_token_ids_sha256','input_tokens'):
        if encoded[key]!=row[key]:
            raise ValueError('tokenizer reconstruction mismatch: '+key)
    if row['status']=='generated' and decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
        raise ValueError('output decode differs from recorded raw reply')


def read_rows(path):
    if not path.exists():
        return []
    # A killed writer may leave a final incomplete line; never salvage that row.
    raw = path.read_bytes()
    return [json.loads(line) for line in raw.splitlines(keepends=True) if line.endswith(b'\n')]


def model_files(path):
    from tools.proof_cuda_train import model_files as trainer_model_files
    return trainer_model_files(path)


def validate_shard(prompt_bytes, data, config, rows, summary):
    tasks = validate_export(data)
    for key, value in BUDGET.items():
        if config.get(key) != value:
            raise ValueError('budget/profile mismatch: '+key)
    expected = shard_tasks(tasks, config['shard_index'])
    if (config.get('prompts_sha256') != sha(prompt_bytes)
            or config.get('requested_task_ids') != [t['id'] for t in expected]
            or config.get('model_files_sha256') != digest(config.get('model_files'))
            or not config.get('model_files') or config.get('restore_exact') is not True):
        raise ValueError('shard provenance/restore mismatch')
    if config.get('arm') not in {'base','checkpoint'} or (config['arm']=='base') != (config.get('checkpoint_sha256') is None):
        raise ValueError('arm/checkpoint mismatch')
    if [r['id'] for r in rows] != [t['id'] for t in expected[:len(rows)]]:
        raise ValueError('duplicate, reordered or missing interior task')
    if summary.get('unattempted_task_ids') != [t['id'] for t in expected[len(rows):]]:
        raise ValueError('only declared suffix may be unattempted')
    if summary.get('termination') not in {'complete','phase_timeout','batch_timeout','worker_error'}:
        raise ValueError('missing declared termination')
    if (len(rows)==len(expected)) != (summary['termination']=='complete'):
        raise ValueError('completion accounting mismatch')
    for row, task in zip(rows, expected):
        if row.get('prompt_sha256') != task['prompt_sha256']:
            raise ValueError('prompt provenance mismatch')
        rendered = row.get('rendered_prompt')
        # Llama's real chat template trims the outer message whitespace. This
        # presence check permits only that boundary operation; local verification
        # still reconstructs the complete rendered prompt AND every input token.
        if not isinstance(rendered,str) or sha(rendered.encode()) != row.get('rendered_prompt_sha256') or task['prompt'].strip() not in rendered:
            raise ValueError('rendered prompt mismatch')
        ids = row.get('input_token_ids')
        if (not isinstance(ids,list) or not ids or any(type(x) is not int or x<0 for x in ids)
                or row.get('input_tokens') != len(ids) or row.get('input_token_ids_sha256') != digest(ids)):
            raise ValueError('input token provenance mismatch')
        if row.get('status') == 'context_overflow':
            if len(ids)+512 <= 8192 or 'token_ids' in row:
                raise ValueError('invalid overflow accounting')
        elif row.get('status') == 'generated':
            tokens = row.get('token_ids')
            if (len(ids)+512 > 8192 or not isinstance(tokens,list) or not tokens
                    or any(type(x) is not int or x<0 for x in tokens) or len(tokens)>512
                    or row.get('output_tokens') != len(tokens) or row.get('token_ids_sha256') != digest(tokens)
                    or row.get('hit_token_limit') is not (len(tokens)==512)
                    or sha(row['raw_reply'].encode()) != row.get('raw_reply_sha256')):
                raise ValueError('output budget/provenance mismatch')
        else:
            raise ValueError('unsupported generation status')


def merge_shards(prompt_bytes, data, shards):
    if len(shards)!=4 or sorted(s[0]['shard_index'] for s in shards)!=list(range(4)):
        raise ValueError('four distinct shards required')
    merged, common = {}, None
    for config, rows, summary in shards:
        validate_shard(prompt_bytes, data, config, rows, summary)
        identity = {k:config[k] for k in ('prompts_sha256','model_files','model_files_sha256',
                    'checkpoint_sha256','arm','profile','implementation_sha256')}
        if common is not None and common != identity:
            raise ValueError('shards have different model/checkpoint/implementation provenance')
        common = identity
        for row in rows:
            if row['id'] in merged:
                raise ValueError('duplicate merged ID')
            merged[row['id']] = row
    return merged, common


def worker(a):
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, restore_policy, PROFILE as trainer_profile
    config = json.loads((a.output/'config.json').read_bytes())
    if sha(a.prompts.read_bytes())!=config['prompts_sha256']:
        raise ValueError('exported prompts changed after config freeze')
    for path,expected in config['implementation_sha256'].items():
        if sha((ROOT/path).read_bytes())!=expected:
            raise ValueError('implementation changed after freeze')
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    torch.set_num_threads(4)
    torch.manual_seed(BUDGET['seed'])
    torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats()
    if trainer_profile != PROFILE or model_files(a.model_path)!=config['model_files']:
        raise ValueError('loader profile/base identity changed')
    net = load_policy(a.model_path, device='cuda')
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    if a.checkpoint:
        if sha(a.checkpoint.read_bytes())!=config['checkpoint_sha256']:
            raise ValueError('checkpoint changed')
        saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
        selected=restore_policy(net,saved,config['model_files'])
        if not all(torch.equal(p.detach().cpu(),saved['trainable_state'][name]) for name,p in selected.items()):
            raise ValueError('checkpoint exact tensor restore failed')
        del saved
    config.update(restore_exact=True, torch_version=torch.__version__,transformers_version=transformers.__version__)
    dump(a.output/'config.json', config)
    dump(a.output/'runtime.json',dict(cuda_peak_allocated_bytes=torch.cuda.max_memory_allocated(),
         cuda_peak_reserved_bytes=torch.cuda.max_memory_reserved(),gpu=torch.cuda.get_device_name(),
         torch_version=torch.__version__,transformers_version=transformers.__version__,parameter_updates=0))
    tokenizer.padding_side = 'left'
    pad_id = tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if not isinstance(pad_id,int):
        raise ValueError('scalar pad token required')
    eos = net.generation_config.eos_token_id
    eos = set(eos if isinstance(eos,list) else [eos])
    tasks = shard_tasks(validate_export(json.loads(a.prompts.read_bytes())),a.shard_index)
    with (a.output/'generations.jsonl').open('x') as stream:
        for offset in range(0,len(tasks),2):
            encoded = [encode_prompt(tokenizer,t) for t in tasks[offset:offset+2]]
            ready = [r for r in encoded if r['status']=='ready']
            if ready:
                inputs = {k:torch.tensor(v,device='cuda') for k,v in left_pad(ready,pad_id).items()}
                dump(a.output/'batch.json',dict(active=True,started=time.time(),ids=[r['id'] for r in ready]))
                with torch.inference_mode(), torch.autocast('cuda',dtype=torch.bfloat16):
                    outputs = net.generate(**inputs,do_sample=False,num_beams=1,num_return_sequences=1,
                                           max_new_tokens=512,max_time=90,pad_token_id=pad_id)
                torch.cuda.synchronize()
                dump(a.output/'batch.json',dict(active=False))
                for row,output in zip(ready,outputs):
                    ids = trim_output(output[inputs['input_ids'].shape[1]:].tolist(),eos)
                    reply = decode_reply(tokenizer,ids)
                    row.update(status='generated',token_ids=ids,token_ids_sha256=digest(ids),
                        output_tokens=len(ids),hit_token_limit=len(ids)==512,
                        raw_reply=reply,raw_reply_sha256=sha(reply.encode()))
            for row in encoded:
                stream.write(json.dumps(row)+'\n');stream.flush()
            dump(a.output/'runtime.json',dict(cuda_peak_allocated_bytes=torch.cuda.max_memory_allocated(),
                 cuda_peak_reserved_bytes=torch.cuda.max_memory_reserved(),gpu=torch.cuda.get_device_name(),
                 torch_version=torch.__version__,parameter_updates=0))


def generate(a):
    data = json.loads(a.prompts.read_bytes())
    tasks = shard_tasks(validate_export(data),a.shard_index)
    files = model_files(a.model_path)
    config = dict(**BUDGET,shard_index=a.shard_index,requested_task_ids=[t['id'] for t in tasks],
        prompts_sha256=sha(a.prompts.read_bytes()),model_files=files,model_files_sha256=digest(files),
        checkpoint_sha256=sha(a.checkpoint.read_bytes()) if a.checkpoint else None,
        arm='checkpoint' if a.checkpoint else 'base',restore_exact=False,
        implementation_sha256={name:sha((ROOT/name).read_bytes()) for name in
            ('tools/proof_cuda_eval.py','tools/proof_cuda_train.py','tools/proof_sequence_train.py')})
    dump(a.output/'config.json',config)
    command = [sys.executable,str(Path(__file__).resolve()),'_worker','--prompts',str(a.prompts),
               '--model-path',str(a.model_path),'--output',str(a.output),'--shard-index',str(a.shard_index)]
    if a.checkpoint:command.extend(['--checkpoint',str(a.checkpoint)])
    started=time.monotonic();termination=None
    with (a.output/'console.log').open('w') as log:
        process=subprocess.Popen(command,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
        previous=signal.getsignal(signal.SIGTERM)
        def terminated(signum,frame):
            raise SystemExit(128+signum)
        signal.signal(signal.SIGTERM,terminated)
        try:
            while process.poll() is None:
                if time.monotonic()-started >=BUDGET['seconds']:
                    termination='phase_timeout'
                batch_path=a.output/'batch.json'
                if batch_path.exists():
                    batch=json.loads(batch_path.read_bytes())
                    if batch.get('active') and time.time()-batch['started']>=90:
                        termination='batch_timeout'
                if termination:
                    os.killpg(process.pid,signal.SIGKILL);process.wait();break
                time.sleep(.25)
        finally:
            if process.poll() is None:
                os.killpg(process.pid,signal.SIGKILL);process.wait()
            signal.signal(signal.SIGTERM,previous)
    rows=read_rows(a.output/'generations.jsonl')
    termination=termination or ('complete' if process.returncode==0 and len(rows)==len(tasks) else 'worker_error')
    runtime=json.loads((a.output/'runtime.json').read_bytes()) if (a.output/'runtime.json').exists() else {}
    dump(a.output/'summary.json',dict(termination=termination,returncode=process.returncode,
        requested_tasks=len(tasks),unattempted_task_ids=[t['id'] for t in tasks[len(rows):]],
        elapsed_seconds=time.monotonic()-started,**runtime))


def verify(a):
    from harness.proof_gen import extract_proof_block
    from harness.proof_fragment_check import certify_fragment
    prompt_bytes=a.prompts.read_bytes(); data=json.loads(prompt_bytes)
    actual,tasks=export_tasks(a.manifest)
    if data!=actual:raise ValueError('prompts do not reconstruct from exact official manifest')
    shards=[]
    for path in a.shards:
        shards.append((json.loads((path/'config.json').read_bytes()),read_rows(path/'generations.jsonl'),
                       json.loads((path/'summary.json').read_bytes())))
    generated,identity=merge_shards(prompt_bytes,data,shards)
    import transformers
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    for path in a.tokenizer_path.iterdir():
        if path.is_file() and (path.suffix=='.json' or path.name in {'tokenizer.model','chat_template.jinja'}):
            if identity['model_files'].get(path.name)!=sha(path.read_bytes()):
                raise ValueError('local tokenizer artifact differs from inference base')
    for task in data['tasks']:
        if task['id'] in generated:validate_tokenization(tokenizer,task,generated[task['id']])
    statuses={t['id']:'generation_unattempted' for t in tasks}; results=[]
    def save():
        dump(a.output/'summary.json',dict(requested_tasks=119,generated_tasks=sum(r['status']=='generated' for r in generated.values()),
            certified_tasks=sum(r['certified'] for r in results),checked_tasks=sum('returncode' in r for r in results),
            task_statuses=statuses,identity=identity,manifest_sha256=sha(a.manifest.read_bytes()),
            method='free whole-target proof generation; greedy pass@1; not candidate ranking',
            timeout_per_module=30,verification_seconds_budget=3600))
    started=time.monotonic();save()
    with (a.output/'rows.jsonl').open('x') as stream:
        for task in tasks:
            row=generated.get(task['id'])
            if not row:continue
            if row['status']!='generated':statuses[task['id']]=row['status'];save();continue
            if time.monotonic()-started>3570:
                statuses[task['id']]='verification_unattempted_budget';save();continue
            proof=extract_proof_block(row['raw_reply'])
            fragment='\n'+proof if proof is not None else None
            result=dict(id=task['id'],certified=False,status='no_proof_fragment',fragment=fragment,
                        raw_reply_sha256=row['raw_reply_sha256'])
            if fragment is not None:
                result.update(certify_fragment(task['prefix'],fragment,task['suffix'],theorem_name=task['theorem_name'],
                    work_root=a.output/'checks'/task['id'],timeout=30))
            results.append(result);statuses[task['id']]=result['status']
            stream.write(json.dumps(result)+'\n');stream.flush();save()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['prepare','generate','verify','_worker'])
    for name in ('manifest','prompts','model-path','checkpoint','tokenizer-path','output'):
        p.add_argument('--'+name,type=Path,required=name=='output')
    p.add_argument('--shards',type=Path,nargs=4)
    p.add_argument('--shard-index',type=int,default=0)
    p.add_argument('--shard-count',type=int,default=4)
    a=p.parse_args()
    required={'prepare':['manifest'],'generate':['prompts','model_path'],'_worker':['prompts','model_path'],
              'verify':['manifest','prompts','shards','tokenizer_path']}[a.mode]
    if any(getattr(a,k) is None for k in required):p.error('missing required mode argument')
    shard_tasks([],a.shard_index,a.shard_count)
    a.output=a.output.resolve()
    if a.mode!='_worker':a.output.mkdir(parents=True,exist_ok=False)
    if a.mode=='prepare':
        export,_=export_tasks(a.manifest);validate_export(export);dump(a.output/'prompts.json',export)
    elif a.mode=='_worker':worker(a)
    else:globals()[a.mode](a)


if __name__=='__main__':main()
