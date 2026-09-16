#!/usr/bin/env python3
"""One feedback repair on four frozen DEV failures; three separate immutable policies."""
import argparse
import json
import os
import re
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_cuda_eval import sha, digest, dump, decode_reply, trim_output, read_rows

from tools.proof_whole_packet import MANIFEST_SHA256, DEV_IDS, TOKENIZER_HASHES
from tools.proof_cuda_train import file_sha


BUDGET = dict(max_new_tokens=3072, max_tokens=8192, batch_size=1, seconds=600,
              batch_seconds=180, seed=20260927, do_sample=False, num_beams=1,
              num_return_sequences=1, profile='frozen bf16 base with float32 final transformer layer; bf16 autocast')
IMPLEMENTATION = ('tools/proof_cuda_feedback_eval.py', 'tools/proof_whole_packet.py',
                  'tools/proof_cuda_whole_eval.py',
                  'tools/proof_cuda_eval.py', 'tools/proof_cuda_train.py',
                  'tools/proof_sequence_train.py', 'tools/proof_repair_pilot.py',
                  'tools/proof_candidate_rank.py')

RUNS=ROOT/'results/runs'
ORIGINAL_PROMPTS=RUNS/'proof-whole-train-prepared-20260905-v1/prompts.json'
ORIGINAL_PROMPTS_SHA='34b7bf16b13d8476e524f825627de473516edfa7b23886b4a1b2f3832ac7e90d'
TOKENIZER=RUNS/'proof-cuda-tokenizer-20260905-v2'
MODEL_FILES_SHA='be21cca8df80e80b27b11aa238d8d77192e3c0e47a096224d1292559190a4cf9'
FIRST_VERSIONS=dict(torch_version='2.11.0+cu128',transformers_version='5.6.2')
EOS_IDS=[128001,128008,128009]
CHECKPOINTS=dict(base=None,parent='6d6c42def8283d50229862874c9b1ab7c2355a499159c0ae37b43c1bd18d7ca2',
 child='b2ff2b9ed7d9a5e6c8f9b82b11f56a91a17f110ecbc57ad5d3d1e64c29179c21')
FIRST_HASHES={
 'base':dict(config='06eb4edb5b2b92c13c4316e9ff867cb6a90f6462e4107eb413fb79d0c97ef969',
  summary='69938f696568f2fb9a7db46745b0ce9171e52518c04acb5dc3b50517d18acc35',
  generations='13b4c476094973adb3ba43a2d7fa4f5a26979bdcafac47c8745e7a65f1447dc6',
  verdicts='71d4f48d345d91f4c666f496642db7321d6475b4092d3ff35e2f8af3817f6597'),
 'parent':dict(config='0e9c1568a15f18ced7051a37a7c6b6e49a063f25b036f79f800d7e5748a9ecce',
  summary='6c363631d510d351fa82a051837fb5e808aac71ffc7fe945b69110be64c8517b',
  generations='3938a59a4068c38a1c75661ba89142d82f33c38a03d824638382f2820bd0d248',
  verdicts='f5354623b96ffdbf31a4c030a1c6f6ba3637bdc2b0ff1c10e66754265fdf457e'),
 'child':dict(config='44cdb280bde513ce46923d0a05536afd05bd5fcd971b40eeeeff2716248dc6e3',
  summary='fdc84154261305850e482559dfee76b5ebda863c7b1a6f5f884e8c8d3c2a5c5c',
  generations='2c9b28c723a6ed467705c0a69f0ce2d2d5326126e0516511fc73742d7dc2d38e',
  verdicts='367be343ee363f84c60974d28d147082467285bdc6f3527b2a7bd313f444e19f')}


def checked(path, expected):
    raw=path.read_bytes()
    if sha(raw)!=expected:raise ValueError('Pinned original artifact changed: '+str(path))
    return raw


def load_tokenizer(path):
    import transformers
    actual={p.name:file_sha(p) for p in path.iterdir() if p.is_file()}
    if actual!=TOKENIZER_HASHES:raise ValueError('Exact pinned tokenizer metadata required')
    return transformers.AutoTokenizer.from_pretrained(path,local_files_only=True)


def diagnostic_prefix(tokenizer,text):
    encoded=tokenizer(text,add_special_tokens=False,truncation=False,return_offsets_mapping=True)
    if len(encoded['input_ids'])<=512:return text
    end=encoded['offset_mapping'][511][1]
    while len(tokenizer(text[:end],add_special_tokens=False,truncation=False)['input_ids'])>512:end-=1
    return text[:end]


def feedback_prompt(original,reply,diagnostic):
    return (original+'\n\n=== PREVIOUS MODEL REPLY (verbatim; rejected) ===\n'+reply+
     '\n=== END PREVIOUS MODEL REPLY ===\n=== VERIFIER FEEDBACK (raw prefix; at most 512 tokens) ===\n'+diagnostic+
     '\n=== END VERIFIER FEEDBACK ===\nRepair the previous proof using this feedback. Return only a replacement for the same <PROOF_HOLE>. Keep every theorem statement, definition, dependency, assumption and surrounding proof unchanged. Do not add axioms, declarations, OMITTED, or change the task. This is one repair attempt.\n')


def failure_diagnostic(row):
    if row.get('certified') is not False or row.get('timed_out',False) is not False:
        raise ValueError('Only measured first-attempt failures are admitted')
    if row['status']=='contract_reject' and row.get('reason'):
        return row['reason']
    if row['status']=='verifier_reject' and row.get('returncode') in (3,10) and row.get('output'):
        from harness.proof_fragment_check import classify_result
        if classify_result(row['returncode'],row['output'],False)[0]!='verifier_reject':
            raise ValueError('Unknown/infra diagnostic must remain unmeasured')
        text=row['output']
        if row['returncode']==3 and not any(marker in text for marker in
                ('Failure("Proof.Parser")','Failure("Module.Parser.parse_file")')):
            raise ValueError('Only evidenced parser diagnostics are admitted')
        if row['returncode']==10 and ("[ERROR]: Could not prove or check:" not in text
                or re.search(r'\[ERROR\]: [1-9][0-9]*/[1-9][0-9]* obligations? failed\.',text) is None):
            raise ValueError('Only evidenced obligation failures are admitted')
        return row['output']
    raise ValueError('Positive, timeout, unattempted or unknown first outcome is not this experiment')


def export_tasks(arm,tokenizer_path=TOKENIZER):
    """Only prompt exports, generated replies and pinned verdicts; no oracle proof source."""
    if arm not in FIRST_HASHES:raise ValueError('Unknown frozen arm')
    from tools.proof_cuda_whole_eval import validate_run as validate_first
    from tools.proof_cuda_eval import validate_tokenization
    raw=checked(ORIGINAL_PROMPTS,ORIGINAL_PROMPTS_SHA); original=json.loads(raw)
    path=RUNS/('proof-cuda-whole-cycle-20260905-v2/whole' if arm=='child' else
               'proof-cuda-whole-cycle-20260905-v1/'+arm)
    hashes=FIRST_HASHES[arm]
    config=json.loads(checked(path/'config.json',hashes['config']))
    summary=json.loads(checked(path/'summary.json',hashes['summary']))
    rows=[json.loads(line) for line in checked(path/'generations.jsonl',hashes['generations']).splitlines()]
    validate_first(raw,config,rows,summary)
    verdicts=[json.loads(line) for line in checked(RUNS/('proof-cuda-whole-'+arm+'-verified-20260905-v1/rows.jsonl'),hashes['verdicts']).splitlines()]
    verdicts={r['id']:r for r in verdicts if r['split']=='development'}
    generated={r['id']:r for r in rows if r['split']=='development'}
    if list(generated)!=DEV_IDS or list(verdicts)!=DEV_IDS:
        raise ValueError('All four unchanged development tasks required')
    tokenizer=load_tokenizer(tokenizer_path); tasks=[]; evidence=[]
    for original_task in original['tasks']:
        if original_task['split']!='development':continue
        key=original_task['id']; g=generated[key]; v=verdicts[key]
        if g['status']!='generated' or v['raw_reply_sha256']!=g['raw_reply_sha256']:
            raise ValueError('Measured reply/verdict binding required')
        validate_tokenization(tokenizer,original_task,g)
        diagnostic=failure_diagnostic(v); prefix=diagnostic_prefix(tokenizer,diagnostic)
        prompt=feedback_prompt(original_task['prompt'],g['raw_reply'],prefix)
        task=dict(id=key,split='development',prompt=prompt,prompt_sha256=sha(prompt.encode()))
        encoded=encode_prompt(tokenizer,task)
        if encoded['status']!='ready':raise ValueError('Complete source and previous reply exceed context; no truncation permitted')
        tasks.append(task)
        evidence.append(dict(id=key,first_status=v['status'],previous_reply_sha256=g['raw_reply_sha256'],
            diagnostic_sha256=sha(diagnostic.encode()),diagnostic_prefix_sha256=sha(prefix.encode()),
            diagnostic_tokens=len(tokenizer(prefix,add_special_tokens=False,truncation=False)['input_ids']),
            diagnostic_truncated=prefix!=diagnostic,input_tokens=encoded['input_tokens'],
            input_token_ids_sha256=encoded['input_token_ids_sha256']))
    packet=dict(schema=1,kind='one_feedback_repair_frozen4dev',arm=arm,
        original_prompts_sha256=ORIGINAL_PROMPTS_SHA,manifest_sha256=MANIFEST_SHA256,
        first_artifacts_sha256=hashes,checkpoint_sha256=config['checkpoint_sha256'],model_files=config['model_files'],
        first_runtime_versions={k:config[k] for k in FIRST_VERSIONS},eos_token_ids=config['eos_token_ids'],
        requested_tasks=4,prior_attempts_per_task=1,new_attempts_per_task=1,diagnostic_token_cap=512,
        reference_fragments_exported=False,candidates_exported=False,tasks=tasks,evidence=evidence)
    validate_export(packet)
    return packet


def validate_export(packet):
    expected={'schema','kind','arm','original_prompts_sha256','manifest_sha256','first_artifacts_sha256',
        'checkpoint_sha256','model_files','first_runtime_versions','eos_token_ids','requested_tasks',
        'prior_attempts_per_task','new_attempts_per_task','diagnostic_token_cap','reference_fragments_exported',
        'candidates_exported','tasks','evidence'}
    arm=packet.get('arm')
    if (set(packet)!=expected or arm not in FIRST_HASHES or packet['schema']!=1
        or packet['kind']!='one_feedback_repair_frozen4dev' or packet['requested_tasks']!=4
        or packet['prior_attempts_per_task']!=1 or packet['new_attempts_per_task']!=1
        or packet['diagnostic_token_cap']!=512 or packet['reference_fragments_exported'] is not False
        or packet['candidates_exported'] is not False or packet['manifest_sha256']!=MANIFEST_SHA256
        or packet['original_prompts_sha256']!=ORIGINAL_PROMPTS_SHA
        or packet['first_artifacts_sha256']!=FIRST_HASHES[arm] or packet['checkpoint_sha256']!=CHECKPOINTS[arm]
        or digest(packet['model_files'])!=MODEL_FILES_SHA or packet['first_runtime_versions']!=FIRST_VERSIONS
        or packet['eos_token_ids']!=EOS_IDS):
        raise ValueError('Frozen feedback provenance/budget/arm mismatch')
    tasks=packet['tasks']
    if [t['id'] for t in tasks]!=DEV_IDS or [e['id'] for e in packet['evidence']]!=DEV_IDS:
        raise ValueError('Exact ordered four development IDs required')
    for task,e in zip(tasks,packet['evidence']):
        if set(e)!={'id','first_status','previous_reply_sha256','diagnostic_sha256','diagnostic_prefix_sha256',
                    'diagnostic_tokens','diagnostic_truncated','input_tokens','input_token_ids_sha256'}:
            raise ValueError('Only reference-free feedback evidence is allowed')
        if any(not isinstance(e[k],str) or re.fullmatch(r'[0-9a-f]{64}',e[k]) is None
               for k in ('previous_reply_sha256','diagnostic_sha256','diagnostic_prefix_sha256','input_token_ids_sha256')):
            raise ValueError('Feedback evidence SHA-256 must be lowercase hexadecimal')
        if (set(task)!={'id','split','prompt','prompt_sha256'} or task['split']!='development'
                or not isinstance(task['prompt'],str) or sha(task['prompt'].encode())!=task['prompt_sha256']
                or not 0<e['input_tokens']<=5120 or not 0<e['diagnostic_tokens']<=512
                or e['first_status'] not in {'contract_reject','verifier_reject'}):
            raise ValueError('Feedback prompt/evidence mismatch')
    return tasks

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
    packet=json.loads(raw)
    tasks = validate_export(packet)
    if config.get('experiment_arm')!=packet['arm'] or config.get('checkpoint_sha256')!=packet['checkpoint_sha256'] or config.get('model_files')!=packet['model_files']:
        raise ValueError('Feedback arm/model/checkpoint mismatch')
    if any(config.get(k)!=v for k,v in FIRST_VERSIONS.items()):
        raise ValueError('Generation libraries differ from first attempt')
    if config.get('eos_token_ids')!=EOS_IDS:
        raise ValueError('EOS differs from first attempt')
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
    if (len(rows)==4) != (summary['termination']=='complete'):
        raise ValueError('completion accounting mismatch')
    eos=config.get('eos_token_ids')
    if not isinstance(eos,list) or not eos or any(type(i) is not int or i<0 for i in eos):
        raise ValueError('EOS identity required')
    for task,row in zip(tasks,rows):
        ids=row.get('input_token_ids')
        evidence=next(e for e in packet['evidence'] if e['id']==task['id'])
        if (row.get('split')!=task['split'] or row.get('prompt_sha256')!=task['prompt_sha256']
                or not isinstance(ids,list) or not ids or any(type(i) is not int or i<0 for i in ids)
                or row.get('input_tokens')!=len(ids) or row.get('input_token_ids_sha256')!=digest(ids)
                or row.get('input_tokens')!=evidence['input_tokens']
                or row.get('input_token_ids_sha256')!=evidence['input_token_ids_sha256']
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
    packet=json.loads(a.prompts.read_bytes());validate_export(packet)
    if config['checkpoint_sha256']!=packet['checkpoint_sha256'] or config['model_files']!=packet['model_files']:
        raise ValueError('Worker first-attempt identity changed')
    if (file_sha(a.checkpoint) if a.checkpoint else None)!=packet['checkpoint_sha256']:
        raise ValueError('Checkpoint changed before GPU load')
    if torch.__version__!=FIRST_VERSIONS['torch_version'] or transformers.__version__!=FIRST_VERSIONS['transformers_version']:
        raise ValueError('Exact first-attempt runtime versions required')
    torch.set_num_threads(4);torch.manual_seed(BUDGET['seed'])
    torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats()
    net=load_policy(a.model_path,device='cuda')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    if a.checkpoint:
        if sha(a.checkpoint.read_bytes())!=config['checkpoint_sha256']: raise ValueError('checkpoint changed')
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
    config['eos_token_ids']=sorted(eos)
    dump(a.output/'config.json',config)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if not isinstance(pad,int): raise ValueError('scalar pad required')
    with (a.output/'generations.jsonl').open('x') as stream:
        for task in validate_export(json.loads(a.prompts.read_bytes())):
            row=encode_prompt(tokenizer,task)
            evidence=next(e for e in packet['evidence'] if e['id']==task['id'])
            if row['input_tokens']!=evidence['input_tokens'] or row['input_token_ids_sha256']!=evidence['input_token_ids_sha256']:
                raise ValueError('Runtime tokenizer differs from frozen feedback token evidence')
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


def runtime_versions():
    import torch
    import transformers
    return dict(torch_version=torch.__version__,transformers_version=transformers.__version__)


def admit(prompts,expected_input_sha256,model_path,checkpoint=None):
    """Full production CPU-only read-only admission; no output creation or CUDA."""
    from tools.proof_cuda_train import model_files
    import transformers
    raw=prompts.read_bytes();packet=json.loads(raw);tasks=validate_export(packet)
    if sha(raw)!=expected_input_sha256: raise ValueError('Expected feedback packet hash mismatch')
    files=model_files(model_path)
    checkpoint_sha=file_sha(checkpoint) if checkpoint else None
    if files!=packet['model_files'] or checkpoint_sha!=packet['checkpoint_sha256']:
        raise ValueError('Feedback must use exact first-attempt model and checkpoint')
    versions=runtime_versions()
    if versions!=FIRST_VERSIONS:raise ValueError('Exact first-attempt runtime versions required')
    generation=json.loads((model_path/'generation_config.json').read_bytes())
    eos=generation['eos_token_id'];eos=eos if isinstance(eos,list) else [eos]
    if sorted(set(eos))!=EOS_IDS:raise ValueError('Exact first-attempt EOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(model_path,local_files_only=True)
    for task,evidence in zip(tasks,packet['evidence']):
        encoded=encode_prompt(tokenizer,task)
        if (encoded['status']!='ready' or encoded['input_tokens']!=evidence['input_tokens']
                or encoded['input_token_ids_sha256']!=evidence['input_token_ids_sha256']):
            raise ValueError('Frozen feedback token reconstruction or full context budget changed')
    return dict(**BUDGET,prompts_sha256=sha(raw),model_files=files,experiment_arm=packet['arm'],
        model_files_sha256=digest(files),requested_task_ids=[t['id'] for t in tasks],restore_exact=False,
        checkpoint_sha256=checkpoint_sha,eos_token_ids=EOS_IDS,**versions,
        arm='checkpoint' if checkpoint else 'base',
        implementation_sha256={n:sha((ROOT/n).read_bytes()) for n in IMPLEMENTATION})


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
                if time.monotonic()-started>=600: termination='phase_timeout'
                if (a.output/'batch.json').exists():
                    batch=json.loads((a.output/'batch.json').read_bytes())
                    if batch.get('active') and time.time()-batch['started']>=180: termination='batch_timeout'
                if termination: break
                time.sleep(.25)
        finally:
            if process.poll() is None: os.killpg(process.pid,signal.SIGKILL);process.wait()
            signal.signal(signal.SIGTERM,previous)
    rows=read_rows(a.output/'generations.jsonl')
    termination=termination or ('complete' if process.returncode==0 and len(rows)==4 else 'worker_error')
    dump(a.output/'summary.json',dict(termination=termination,returncode=process.returncode,requested_tasks=4,
        unattempted_task_ids=[t['id'] for t in tasks[len(rows):]],elapsed_seconds=time.monotonic()-started))


def verify(a):
    from harness.proof_gen import extract_proof_block
    from harness.proof_fragment_check import certify_fragment
    from tools.proof_cuda_eval import validate_tokenization
    raw=a.prompts.read_bytes();packet=json.loads(raw);validate_export(packet)
    if export_tasks(packet['arm'],a.tokenizer_path)!=packet:
        raise ValueError('Feedback packet differs from exact first outputs and raw diagnostics')
    config=json.loads((a.generations/'config.json').read_bytes())
    rows=read_rows(a.generations/'generations.jsonl')
    validate_run(raw,config,rows,json.loads((a.generations/'summary.json').read_bytes()))
    tokenizer=load_tokenizer(a.tokenizer_path)
    for task,row in zip(packet['tasks'],rows):
        validate_tokenization(tokenizer,task,row)
        if row['status']=='generation_time_limit' and decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
            raise ValueError('Time-limited reply reconstruction changed')
    # Manifest hash binds immutable holes. Never export or use its reference fragments.
    manifest=json.loads(checked(a.manifest,MANIFEST_SHA256))
    fields=('id','split','prefix','suffix','theorem_name','dependencies','dependency_sha256','source_path','source_sha256')
    tasks=[{k:t[k] for k in fields} for t in manifest['tasks'] if t['split']=='development']
    if [t['id'] for t in tasks]!=DEV_IDS:raise ValueError('Frozen DEV scaffold population changed')
    for task in tasks:
        if file_sha(Path(task['source_path']))!=task['source_sha256']:
            raise ValueError('Immutable source bytes changed')
        if set(task['dependencies'])!=set(task['dependency_sha256']):raise ValueError('Dependency inventory changed')
        for name,h in task['dependency_sha256'].items():
            if file_sha(Path(name))!=h:raise ValueError('Dependency source bytes changed')
    generated={r['id']:r for r in rows};results=[]
    def save():
        successes=sum(r['certified'] for r in results)
        dump(a.output/'summary.json',dict(identity=config,arm=packet['arm'],requested_tasks=4,
            method='One adaptive feedback repair after one greedy initial attempt; reused DEV, not held-out generalization',
            first_attempt_certified_tasks=0,repair_certified_tasks=successes,adaptive_pass_at_2_certified_tasks=successes,
            repair_success_rate=successes/4,adaptive_pass_at_2_rate=successes/4,
            prior_attempts=4,requested_new_attempts=4,total_requested_attempts=8,
            generated_repair_tasks=sum(r['status']=='generated' for r in rows),timeout_per_module=30,
            first_artifacts_sha256=packet['first_artifacts_sha256'],
            status_counts={s:sum(r['status']==s for r in results) for s in sorted({r['status'] for r in results})},
            manifest_sha256=MANIFEST_SHA256,training_executed=False,parameter_updates=0))
    save()
    with (a.output/'rows.jsonl').open('x') as stream:
        for task in tasks:
            row=generated.get(task['id'])
            result=dict(id=task['id'],split='development',arm=packet['arm'],attempt=2,
                        certified=False,status='generation_unattempted')
            if row:
                result['status']=row['status']
                if row['status']=='generated':
                    fragment=extract_proof_block(row['raw_reply'])
                    result.update(fragment=fragment,raw_reply_sha256=row['raw_reply_sha256'],status='no_proof_fragment')
                    if fragment is not None:
                        result.update(certify_fragment(task['prefix'],fragment,task['suffix'],
                            theorem_name=task['theorem_name'],dependencies=tuple(Path(p) for p in task['dependencies']),
                            work_root=a.output/'checks'/task['id'],timeout=30))
            results.append(result);stream.write(json.dumps(result)+'\n');stream.flush();save()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['prepare','generate','verify','_worker'])
    p.add_argument('--arm',choices=list(CHECKPOINTS))
    p.add_argument('--expected-input-sha256')
    for name in ('manifest','prompts','model-path','checkpoint','generations','output'):
        p.add_argument('--'+name,type=Path,required=name=='output')
    p.add_argument('--tokenizer-path',type=Path,default=TOKENIZER)
    a=p.parse_args()
    required={'prepare':['arm'],'generate':['prompts','model_path','expected_input_sha256'],
              '_worker':['prompts','model_path'],'verify':['manifest','prompts','generations']}[a.mode]
    if any(getattr(a,n) is None for n in required):p.error('Missing required mode argument')
    a.output=a.output.resolve()
    if a.mode!='_worker':a.output.mkdir(parents=True,exist_ok=False)
    if a.mode=='prepare':
        packet=export_tasks(a.arm,a.tokenizer_path)
        dump(a.output/'prompts.json',packet)
        dump(a.output/'summary.json',dict(arm=a.arm,requested_tasks=4,
            prompts_sha256=file_sha(a.output/'prompts.json'),reference_fragments_exported=False,
            input_tokens={e['id']:e['input_tokens'] for e in packet['evidence']},training_executed=False))
    else:globals()[a.mode.removeprefix('_')](a)


if __name__=='__main__':main()
