"""Matched greedy 40-target retention: original36 then new TRAIN4, no training."""
import argparse
import json
import math
import os
from pathlib import Path
import re
import sys
import time

CPU_ENV={n:'4' for n in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}
os.environ.update(CPU_ENV)
os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_cuda_broader_eval as common
from tools import proof_broader_packet as broader,proof_sumsequence_packet as extra
from tools.proof_cuda_eval import digest,sha,dump
from tools.proof_cuda_train import file_sha
from harness.proof_owned_process import run_owned,as_runner_tuple

PARENT_SHA='f41f4a147b0fbc4cbd62ba87403d76516b4cd9da96fcc577979b033fa96b1a91'
BUDGET=dict(requested_tasks=40,original_train=32,original_development=4,new_train=4,
    max_new_tokens=3072,max_context=8192,do_sample=False,num_beams=1,num_return_sequences=1,
    seed=20260930,phase_seconds=1000,item_seconds=180,cpu_threads=4,memory_bytes=36*1024**3,
    post_admission_reserve_seconds=30)
SOURCES=tuple(dict.fromkeys(('tools/proof_sumsequence_repair_eval.py','tools/proof_sumsequence_packet.py',
    'harness/proof_owned_process.py')+common.IMPLEMENTATION))


def compose(broader_raw,sumsequence_raw):
    original=broader.validate_export(json.loads(broader_raw));new=extra.validate_export(json.loads(sumsequence_raw))
    return dict(schema=1,kind='original36_then_sumsequence4_retention',
        original_packet_bytes=broader_raw.decode(),new_packet_bytes=sumsequence_raw.decode(),
        original_sha256=sha(broader_raw),new_sha256=sha(sumsequence_raw),tasks=original+new,
        reference_answers_exported=False,counts=dict(original_train=32,original_development=4,new_train=4))


def validate_export(packet):
    if not isinstance(packet,dict) or set(packet)!={'schema','kind','original_packet_bytes','new_packet_bytes',
        'original_sha256','new_sha256','tasks','reference_answers_exported','counts'}:
        raise ValueError('Exact portable40 packet fields required')
    expected=compose(packet['original_packet_bytes'].encode(),packet['new_packet_bytes'].encode())
    if packet!=expected or len(packet['tasks'])!=40 or len({t['id'] for t in packet['tasks']})!=40:
        raise ValueError('Exact unchanged original36 followed by new TRAIN4 required')
    return packet['tasks']


def checkpoint_role(role,expected):
    if role not in ('parent','child') or not re.fullmatch('[0-9a-f]{64}',expected or ''):
        raise ValueError('Explicit role and exact checkpoint SHA required')
    if (role=='parent')!=(expected==PARENT_SHA):raise ValueError('Parent hash pinned; child must be distinct')


def sources():return {name:file_sha(ROOT/name) for name in SOURCES}


def admit(a):
    os.environ.update(CPU_ENV)
    import torch,transformers
    from tools.proof_cuda_train import model_files,PROFILE
    torch.set_num_threads(4);checkpoint_role(a.role,a.expected_checkpoint_sha256)
    raw=a.prompts.read_bytes();tasks=validate_export(json.loads(raw))
    if sha(raw)!=a.expected_input_sha256 or file_sha(a.checkpoint)!=a.expected_checkpoint_sha256:
        raise ValueError('Frozen prompt/checkpoint bytes required')
    files=model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS or PROFILE!=common.BUDGET['profile']:
        raise ValueError('Exact model, runtime and profile required')
    if json.loads((a.model_path/'generation_config.json').read_bytes())['eos_token_id']!=common.EOS_IDS:
        raise ValueError('Exact model EOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encoded=[common.encode_prompt(tokenizer,t) for t in tasks]
    if any(e['status']!='ready' for e in encoded):raise ValueError('Full untruncated context required')
    return dict(schema=1,budget=BUDGET,role=a.role,prompts_sha256=sha(raw),
        checkpoint_sha256=a.expected_checkpoint_sha256,model_files=files,
        model_files_sha256=digest(files),versions=common.runtime_versions(),profile=PROFILE,
        eos_token_ids=common.EOS_IDS,input_evidence=encoded,implementation_sha256=sources(),
        cpu_environment=CPU_ENV,optimizer_updates=0,training_linkage_verified=False,
        scope='Matched retention diagnosis: original TRAIN32/DEV4 and separate new TRAIN4; not unseen proof gain')


def output_fields(tokens,reply,*,late=False):
    if not isinstance(tokens,list) or len(tokens)>3072 or any(type(t) is not int or t<0 for t in tokens):
        raise ValueError('Exact bounded output token IDs required')
    if common.trim_output(tokens,set(common.EOS_IDS))!=tokens:raise ValueError('No token after first EOS')
    eos=bool(tokens and tokens[-1] in common.EOS_IDS);cap=len(tokens)==3072
    finish='time_limit' if late or not tokens else 'eos' if eos else 'token_limit' if cap else 'time_limit'
    return dict(token_ids=tokens,token_ids_sha256=digest(tokens),output_tokens=len(tokens),
        raw_reply=reply,raw_reply_sha256=sha(reply.encode()),finish_reason=finish,eos_reached=eos,
        hit_token_limit=cap,deadline_exceeded=bool(late),
        status='generation_time_limit' if finish=='time_limit' else 'generated')


def validate_rows(admission,rows,*,complete=False):
    if admission['budget']!=BUDGET or len(admission['input_evidence'])!=40:
        raise ValueError('Frozen40 evaluation budget required')
    checkpoint_role(admission['role'],admission['checkpoint_sha256'])
    if len(rows)>40 or complete and len(rows)!=40:raise ValueError('Full40 accounting required')
    for frozen,row in zip(admission['input_evidence'],rows):
        if any(row.get(k)!=v for k,v in frozen.items() if k!='status'):
            raise ValueError('Exact ordered prompt/input identity required')
        if row.get('status') in ('unattempted','worker_error'):
            if set(row)!=set(frozen)|{'reason'} or not isinstance(row['reason'],str) or not row['reason']:
                raise ValueError('Explicit unmeasured row required')
        else:
            expected=output_fields(row['token_ids'],row['raw_reply'],late=row['deadline_exceeded'])
            if set(row)!=set(frozen)|set(expected) or any(row.get(k)!=v for k,v in expected.items()):
                raise ValueError('Exact output/completion evidence required')


def memory_guard(allocated,reserved):
    if any(type(v) not in (int,float) or not math.isfinite(v) or not 0<=v<=BUDGET['memory_bytes'] for v in (allocated,reserved)):
        raise ValueError('36GiB allocated/reserved ceiling exceeded')


def worker(a):
    os.environ.update(CPU_ENV)
    import torch,transformers
    from tools.proof_cuda_train import load_policy,restore_policy
    admission=json.loads(a.admission.read_bytes())
    if admit(a)!=admission:raise ValueError('Worker full admission changed')
    torch.manual_seed(BUDGET['seed']);torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats();net=load_policy(a.model_path,device='cuda')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    selected=restore_policy(net,saved,admission['model_files'])
    if any(not torch.equal(p.detach().cpu(),saved['trainable_state'][n]) for n,p in selected.items()):
        raise ValueError('Exact checkpoint restore failed')
    initial={n:p.detach().cpu().clone() for n,p in selected.items()};del saved
    if any(p.requires_grad for p in net.parameters()) or net.generation_config.eos_token_id!=common.EOS_IDS:
        raise ValueError('Frozen inference parameters/EOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if type(pad) is not int:raise ValueError('Scalar pad token required')
    tasks=validate_export(json.loads(a.prompts.read_bytes()))
    with (a.output/'generations.jsonl').open('x') as stream:
        for task,frozen in zip(tasks,admission['input_evidence']):
            row=common.encode_prompt(tokenizer,task)
            if row!=frozen:raise ValueError('Exact input reconstruction drift')
            started=time.monotonic();inputs=torch.tensor([row['input_token_ids']],device='cuda')
            with torch.inference_mode(),torch.autocast('cuda',dtype=torch.bfloat16):
                generated=net.generate(input_ids=inputs,attention_mask=torch.ones_like(inputs),
                    do_sample=False,num_beams=1,num_return_sequences=1,max_new_tokens=3072,max_time=180,pad_token_id=pad)
            torch.cuda.synchronize()
            tokens=common.trim_output(generated[0,inputs.shape[1]:].tolist(),set(common.EOS_IDS))
            row.update(output_fields(tokens,common.decode_reply(tokenizer,tokens),late=time.monotonic()-started>180))
            stream.write(json.dumps(row)+'\n');stream.flush()
            runtime=dict(allocated=torch.cuda.max_memory_allocated(),reserved=torch.cuda.max_memory_reserved(),
                optimizer_updates=0,restore_exact=True,weights_unchanged=False,
                device=torch.cuda.get_device_name(),cpu_threads=torch.get_num_threads())
            dump(a.output/'runtime.json',runtime);memory_guard(runtime['allocated'],runtime['reserved'])
    if any(not torch.equal(p.detach().cpu(),initial[n]) for n,p in selected.items()):
        raise ValueError('Frozen inference weights changed')
    if admit(a)!=admission:raise ValueError('Post-generation full admission changed')
    runtime['weights_unchanged']=True;dump(a.output/'runtime.json',runtime)


def _generate(a):
    started=time.monotonic()
    admission=json.loads(a.admission.read_bytes())
    if admit(a)!=admission:raise ValueError('Full frozen pre-worker admission mismatch')
    for source in (a.prompts,a.checkpoint,a.admission,a.model_path):
        source=source.resolve();output=a.output.resolve()
        if source==output or output in source.parents or source in output.parents:
            raise ValueError('Isolated output required')
    a.output.mkdir(parents=True,exist_ok=False);a._created_output=True
    dump(a.output/'admission.json',admission)
    unknown=[dict(frozen,status='unattempted',reason='worker_pending') for frozen in admission['input_evidence']]
    validate_rows(admission,unknown,complete=True)
    dump(a.output/'accounting.json',unknown)
    dump(a.output/'summary.json',dict(complete=False,status='worker_pending',requested_tasks=40,
        accounted_tasks=40,unknown_tasks=40,unattempted_ids=[r['id'] for r in unknown],
        optimizer_updates=0,proof_verification_pending=True))
    command=[sys.executable,str(Path(__file__).resolve()),'worker','--role',a.role,
        '--expected-input-sha256',a.expected_input_sha256,'--expected-checkpoint-sha256',a.expected_checkpoint_sha256]
    for name in ('prompts','model_path','checkpoint'):command+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
    command+=['--admission',str((a.output/'admission.json').resolve()),'--output',str(a.output.resolve())]
    remaining=1000-(time.monotonic()-started)-BUDGET['post_admission_reserve_seconds']
    if remaining<=0:raise TimeoutError('Admission exhausted phase before worker reserve')
    process=run_owned(command,ROOT,remaining);dump(a.output/'process.json',process)
    if json.loads((a.output/'process.json').read_bytes())!=process or process['command']!=command or Path(process['cwd']).resolve()!=ROOT:
        raise ValueError('Exact owned process ledger required')
    rc,out,elapsed,timeout=as_runner_tuple(process)
    path=a.output/'generations.jsonl'
    rows=[json.loads(line) for line in path.read_bytes().splitlines()] if path.exists() else []
    validate_rows(admission,rows)
    accounted=rows+[dict(frozen,status='unattempted',reason='owned_worker_stopped_before_this_task')
                    for frozen in admission['input_evidence'][len(rows):]]
    validate_rows(admission,accounted,complete=True);dump(a.output/'accounting.json',accounted)
    provenance=(admit(a)==admission and json.loads(a.admission.read_bytes())==admission and
        json.loads((a.output/'admission.json').read_bytes())==admission)
    runtime=json.loads((a.output/'runtime.json').read_bytes()) if (a.output/'runtime.json').exists() else {}
    memory_ok=False
    try:memory_guard(runtime.get('allocated'),runtime.get('reserved'));memory_ok=True
    except ValueError:pass
    phase_seconds=time.monotonic()-started
    complete=rc==0 and not timeout and phase_seconds<=1000 and len(rows)==40 and provenance and memory_ok and runtime.get('weights_unchanged') is True and runtime.get('restore_exact') is True
    summary=dict(complete=complete,requested_tasks=40,accounted_tasks=40,generated_rows=len(rows),
        eos_complete=sum(r.get('finish_reason')=='eos' for r in rows),
        unattempted_ids=[r['id'] for r in accounted if r['status']=='unattempted'],
        populations=dict(original_train=32,original_development=4,new_train=4),
        checkpoint_sha256=a.expected_checkpoint_sha256,role=a.role,training_linkage_verified=False,
        full_admission_stable=provenance,memory_guard_passed=memory_ok,
        accounting_sha256=file_sha(a.output/'accounting.json'),process_sha256=file_sha(a.output/'process.json'),
        returncode=rc,timed_out=timeout,optimizer_updates=0,proof_verification_pending=True)
    summary.update(phase_seconds=phase_seconds,worker_timeout_seconds=remaining)
    dump(a.output/'summary.json',summary)
    if not complete:raise RuntimeError('Incomplete evaluation; exact40 accounting preserved')
    return summary


def generate(a):
    a._created_output=False
    try:return _generate(a)
    except BaseException as exc:
        if a._created_output:
            dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
            summary=json.loads((a.output/'summary.json').read_bytes())
            if summary.get('status')=='worker_pending':
                admission=json.loads((a.output/'admission.json').read_bytes())
                unknown=[dict(frozen,status='unattempted',reason='unverified_execution_or_ledger_failure')
                         for frozen in admission['input_evidence']]
                dump(a.output/'accounting.json',unknown)
                summary.update(status='unmeasured_execution_or_ledger_error',unknown_tasks=40,
                    unattempted_ids=[r['id'] for r in unknown],accounting_sha256=file_sha(a.output/'accounting.json'))
                dump(a.output/'summary.json',summary)
        raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('compose','admit','generate','worker'))
    for name in ('broader','sumsequence','prompts','model-path','checkpoint','admission','output'):
        parser.add_argument('--'+name,type=Path,required=name=='output')
    parser.add_argument('--role',choices=('parent','child'))
    parser.add_argument('--expected-input-sha256');parser.add_argument('--expected-checkpoint-sha256')
    a=parser.parse_args()
    if a.mode=='compose':dump(a.output,compose(a.broader.read_bytes(),a.sumsequence.read_bytes()))
    elif a.mode=='admit':dump(a.output,admit(a))
    else:globals()[a.mode](a)


if __name__=='__main__':main()
