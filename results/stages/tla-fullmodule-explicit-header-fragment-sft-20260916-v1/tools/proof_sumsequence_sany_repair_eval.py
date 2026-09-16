"""Two selected full-context greedy repair attempts; not original40 pass@1."""
import argparse
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_proof_rl_eval as base
from tools import proof_sumsequence_sany_repair_packet as repair
from tools.proof_cuda_eval import encode_prompt as full_encoder
from harness.proof_owned_process import run_owned

load=base.load;dump=base.dump;file_sha=base.file_sha;digest=base.digest;train=base.train;common=base.common
PACKET_SHA='9bf035b22be90997769396a9ec94918e7cc6bd00e003baceecd374fe99b12d77'
POLICY_SHA=repair.POLICY_SHA;IDS=repair.IDS
BUDGET=dict(requested_tasks=2,attempts_per_task=1,original_denominator=40,max_context=9216,
    max_new_tokens=3072,maximum_input_tokens=6144,do_sample=False,num_beams=1,num_return_sequences=1,
    seed=20261005,seconds=1200,item_seconds=180,memory_bytes=36*1024**3,cpu_threads=4,
    minimum_post_admission_seconds=30,admission_reserve_multiplier=1.25,truncation=False,optimizer_updates=0)
INPUTS=('packet','model_path','checkpoint','training_inputs','training_output')
SOURCES=tuple(sorted(set(base.SOURCES)|set(repair.SOURCES)|{
    'tools/proof_sumsequence_sany_repair_eval.py','tools/proof_sumsequence_sany_repair_eval.pbs',
    'tools/proof_breadth26_manifest.py','tools/proof_breadth_manifest.py','tools/proof_dev_manifest.py',
    'tools/proof_fact_search.py','tools/proof_family_manifest.py','tools/proof_official_extension.py',
    'tools/proof_original18.py','tools/proof_premise_search.py','tools/proof_source_scope.py'}))


def sources():return {name:file_sha(ROOT/name) for name in SOURCES}


def packet(path):
    if file_sha(path)!=PACKET_SHA:raise ValueError('Exact immutable two-task diagnostic packet required')
    value=load(path)
    if (value['policy_sha256']!=POLICY_SHA or value['budget']!=repair.BUDGET or value['original_denominator']!=40 or
        value['diagnostic_tasks']!=2 or [r['id'] for r in value['tasks']]!=list(IDS) or
        value['reference_answers_exported'] is not False or value['gate_claim'] is not False):
        raise ValueError('Original selected repair provenance must remain unchanged')
    for name,pin in value['source_sha256'].items():
        if file_sha(ROOT/name)!=pin:raise ValueError('Original packet source audit changed')
    return value


def encode(tokenizer,row):
    task={k:row[k] for k in ('id','split','prompt','prompt_sha256')}
    actual=full_encoder(tokenizer,task)
    # Only readiness changes under the NEW9216 contract, never bytes or tokens.
    original=row['encoding']
    if any(actual[k]!=original[k] for k in actual if k!='status'):
        raise ValueError('Full original repair prompt/token reconstruction changed')
    actual.update(split='train',status='ready' if actual['input_tokens']+3072<=9216 else 'context_overflow')
    if actual['status']!='ready':raise ValueError('Complete repair context exceeds NEW9216; no truncation')
    return actual


def admit(a):
    base.os.environ.update(base.CPU_ENV)
    before=sources();value=packet(a.packet)
    # Calls the real target-host training and CPU checkpoint/optimizer validators.
    receipt=base.training_receipt(a)
    if receipt['child_sha256']!=POLICY_SHA or file_sha(a.checkpoint)!=POLICY_SHA:
        raise ValueError('Actual current1bb6 policy required; no update/resume')
    import torch,transformers
    torch.set_num_threads(4)
    if {n:base.os.environ.get(n) for n in base.CPU_ENV}!=base.CPU_ENV:raise ValueError('CPU4 before numerical imports required')
    files=train.model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS:
        raise ValueError('Exact frozen model and target runtime required')
    config=load(a.model_path/'config.json')
    if type(config.get('max_position_embeddings')) is not int or config['max_position_embeddings']<9216:
        raise ValueError('Actual original model must support NEW9216 without config changes')
    if load(a.model_path/'generation_config.json')['eos_token_id']!=common.EOS_IDS:raise ValueError('Original actual EOS required')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    checkpoint_config=base.stochastic.checkpoint_state(saved,files);del saved
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encodings=[encode(tokenizer,row) for row in value['tasks']]
    if sources()!=before or file_sha(a.checkpoint)!=POLICY_SHA or file_sha(a.packet)!=PACKET_SHA:
        raise ValueError('Source/checkpoint/packet changed during full admission')
    return dict(schema=1,kind='selected2_full_context_repair_diagnostic',budget=BUDGET,packet_sha256=PACKET_SHA,
        checkpoint_sha256=POLICY_SHA,checkpoint_config_sha256=checkpoint_config,training_receipt=receipt,
        model_files=files,model_files_sha256=digest(files),versions=common.runtime_versions(),profile=train.PROFILE,
        model_max_position_embeddings=config['max_position_embeddings'],eos_token_ids=common.EOS_IDS,
        encodings=encodings,original_encoding_sha256=[digest(row['encoding']) for row in value['tasks']],
        original_packet_budget=value['budget'],original_packet_executable_tasks=value['executable_tasks'],
        source_sha256=before,cpu_environment=base.CPU_ENV,optimizer_updates=0,
        original_denominator=40,repair_attempts=2,original_pass_at1_unchanged=True,
        verification_pending=True,generalization_claim=False,gate_claim=False,
        context_change='Explicit new9216 context budget; original8192 packet/overflow evidence unchanged; full prompts verbatim')


def validate_rows(frozen,rows,tokenizer=None):
    if frozen['budget']!=BUDGET or len(rows)!=2 or [r['id'] for r in frozen['encodings']]!=list(IDS):
        raise ValueError('Exact two-task newcontext accounting required')
    for expected,row in zip(frozen['encodings'],rows):
        if any(row.get(k)!=v for k,v in expected.items() if k!='status'):raise ValueError('Exact ordered full input identity required')
        if row.get('status')=='unattempted':
            if row!=base.unknown(expected,row.get('reason')) or not isinstance(row.get('reason'),str) or not row['reason']:
                raise ValueError('Explicit unattempted row required')
        else:
            fields=base.greedy.output_fields(row['token_ids'],row['raw_reply'],late=row['deadline_exceeded'])
            if row!=dict(expected,**fields):raise ValueError('Exact output tokens/actualEOS/limit evidence required')
            if tokenizer is not None and common.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Actual exact reply decoder reconstruction required')


def accounting(rows):
    return dict(requested_tasks=2,accounted_tasks=len(rows),generated_rows=sum(r['status']!='unattempted' for r in rows),
        eos_complete=sum(r.get('finish_reason')=='eos' for r in rows),unknown_generations=sum(r.get('finish_reason')!='eos' for r in rows),
        unattempted_ids=[r['id'] for r in rows if r['status']=='unattempted'],original_denominator=40)


def reserve(seconds):return max(30.,1.25*seconds)


def save_rng(output,label):
    import torch
    path=output/('rng_'+label+'.pt')
    torch.save(dict(seed=BUDGET['seed'],cpu=torch.get_rng_state(),cuda=torch.cuda.get_rng_state()),path)
    return file_sha(path)


def worker(a):
    started=time.monotonic();frozen=load(a.admission)
    if not 30<a.worker_seconds<=1200:raise ValueError('Bounded owned worker required')
    if admit(a)!=frozen:raise ValueError('Actual full saved admission changed before model load')
    pre=time.monotonic()-started;post=reserve(pre)
    if a.worker_seconds-pre-post<=0:raise TimeoutError('No model load after exhausted admission budget')
    import torch,transformers
    torch.manual_seed(BUDGET['seed']);torch.cuda.manual_seed(BUDGET['seed'])
    torch.backends.cuda.matmul.allow_tf32=False;torch.cuda.reset_peak_memory_stats()
    net=train.load_policy(a.model_path,device='cuda');base.record_memory(a.output,'after_model_load')
    if net.config.max_position_embeddings!=frozen['model_max_position_embeddings']:
        raise ValueError('Loaded model context configuration changed')
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    if base.stochastic.checkpoint_state(saved,frozen['model_files'])!=frozen['checkpoint_config_sha256']:raise ValueError('Exact checkpoint config required')
    selected=train.restore_policy(net,saved,frozen['model_files'])
    initial={n:v.clone() for n,v in saved['trainable_state'].items()};del saved
    base.stochastic.assert_unchanged(selected,initial);base.record_memory(a.output,'after_checkpoint_restore')
    if any(p.requires_grad for p in net.parameters()) or net.generation_config.eos_token_id!=common.EOS_IDS:
        raise ValueError('Entire model frozen and originalEOS required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if type(pad) is not int:raise ValueError('Scalar padding token required')
    value=packet(a.packet);rows=[base.unknown(e) for e in frozen['encodings']];base.persist(a.output,rows)
    rng=dict(before=save_rng(a.output,'before'))
    with (a.output/'events.jsonl').open('x') as stream:
        for index,task in enumerate(value['tasks']):
            remaining=a.worker_seconds-(time.monotonic()-started)-post
            if remaining<=0:break
            row=encode(tokenizer,task)
            if row!=frozen['encodings'][index]:raise ValueError('Actual full input encoding changed')
            inputs=torch.tensor([row['input_token_ids']],device='cuda');item=time.monotonic();limit=min(180,remaining)
            with torch.inference_mode(),train.autocast('cuda'):
                output=net.generate(input_ids=inputs,attention_mask=torch.ones_like(inputs),do_sample=False,
                    num_beams=1,num_return_sequences=1,max_new_tokens=3072,max_time=limit,pad_token_id=pad)
            torch.cuda.synchronize()
            tokens=common.trim_output(output[0,inputs.shape[1]:].tolist(),set(common.EOS_IDS))
            row.update(base.greedy.output_fields(tokens,common.decode_reply(tokenizer,tokens),late=time.monotonic()-item>limit))
            rows[index]=row;base.persist(a.output,rows);stream.write(json.dumps(row)+'\n');stream.flush()
            base.record_memory(a.output,'after_sample_'+str(index))
    base.stochastic.assert_unchanged(selected,initial);validate_rows(frozen,rows,tokenizer)
    rng['after']=save_rng(a.output,'after');stable=admit(a)==frozen
    memory=base.record_memory(a.output,'after_final_admission');elapsed=time.monotonic()-started;counts=accounting(rows)
    summary=dict(complete=stable and counts['generated_rows']==2 and elapsed<=a.worker_seconds,**counts,
        checkpoint_sha256=POLICY_SHA,weights_unchanged=True,restore_exact=True,full_admission_stable=stable,
        elapsed_seconds=elapsed,pre_admission_seconds=pre,post_admission_reserve_seconds=post,
        memory=memory,rng_sha256=rng,accounting_sha256=file_sha(a.output/'accounting.json'),
        optimizer_updates=0,verification_pending=True,original_pass_at1_unchanged=True,gate_claim=False)
    dump(a.output/'worker_summary.json',summary)
    if not summary['complete']:raise RuntimeError('Incomplete selected repair attempts; no scores')


def validate_worker(frozen,rows,summary,output):
    validate_rows(frozen,rows)
    if (any(summary.get(k)!=v for k,v in accounting(rows).items()) or summary.get('generated_rows')!=2 or
        any(summary.get(k) is not True for k in ('complete','weights_unchanged','restore_exact','full_admission_stable','verification_pending','original_pass_at1_unchanged')) or
        summary.get('checkpoint_sha256')!=POLICY_SHA or summary.get('optimizer_updates')!=0 or summary.get('gate_claim') is not False or
        summary.get('accounting_sha256')!=file_sha(output/'accounting.json') or
        not 0<summary.get('elapsed_seconds',float('inf'))<=1200 or
        not 0<=summary.get('pre_admission_seconds',float('inf'))<1200 or
        summary.get('post_admission_reserve_seconds')!=reserve(summary['pre_admission_seconds'])):
        raise ValueError('Exact complete actual two-task worker evidence required')
    raw=(output/'events.jsonl').read_bytes()
    if not raw.endswith(b'\n') or [json.loads(line) for line in raw.splitlines()]!=rows:raise ValueError('Exact complete two raw events required')
    memory=load(output/'memory_events.json')
    if [r['phase'] for r in memory]!=['after_model_load','after_checkpoint_restore','after_sample_0','after_sample_1','after_final_admission']:
        raise ValueError('Complete ordered raw memory phases required')
    for row in memory:
        base.greedy.memory_guard(row['allocated'],row['reserved'])
        if not 0<row['allocated']<=row['reserved']:raise ValueError('Actual memory evidence required')
    if summary['memory']!=load(output/'memory.json') or summary['memory']!={k:memory[-1][k] for k in ('allocated','reserved')}:
        raise ValueError('Final raw memory differs from worker summary')
    import torch
    for label in ('before','after'):
        path=output/('rng_'+label+'.pt')
        if summary['rng_sha256'][label]!=file_sha(path):raise ValueError('Actual RNG evidence hash changed')
        rng=torch.load(path,map_location='cpu',weights_only=True)
        if set(rng)!=set(('seed','cpu','cuda')) or rng['seed']!=BUDGET['seed']:raise ValueError('Exact seeded RNG snapshots required')
        if any(rng[k].dtype!=torch.uint8 or rng[k].ndim!=1 or not rng[k].numel() for k in ('cpu','cuda')):
            raise ValueError('Actual CPU/CUDA byte RNG states required')


def command_args(a):
    result=[]
    for name in INPUTS:result+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
    return result


def generate(a):
    started=time.monotonic();a.output=a.output.resolve()
    for name in (*INPUTS,'admission'):
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Isolated immutable inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'summary.json',dict(complete=False,requested_tasks=2,accounted_tasks=2,original_denominator=40,
        unknown_generations=2,unattempted_ids=list(IDS),optimizer_updates=0,verification_pending=True))
    try:
        frozen=load(a.admission)
        if admit(a)!=frozen:raise ValueError('Full production admission changed')
        dump(a.output/'admission.json',frozen);base.persist(a.output,[base.unknown(e) for e in frozen['encodings']])
        pre=time.monotonic()-started;post=reserve(pre);remaining=1200-pre-post
        if remaining<=30:raise TimeoutError('No worker budget after actual admission/reserve')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']+command_args(a)+[
            '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);dump(a.output/'process.json',process)
        base.historical.process_ok(process,command,ROOT,remaining)
        rows=load(a.output/'accounting.json');summary=load(a.output/'worker_summary.json');validate_worker(frozen,rows,summary,a.output)
        if summary['elapsed_seconds']>remaining:raise ValueError('Actual worker exceeded remaining deadline')
        if admit(a)!=frozen or load(a.admission)!=frozen or load(a.output/'admission.json')!=frozen:
            raise ValueError('Full final source/checkpoint/runtime/input admission changed')
        elapsed=time.monotonic()-started
        if elapsed>1200:raise TimeoutError('Total bounded diagnostic deadline exceeded')
        summary.update(total_seconds=elapsed,process_sha256=file_sha(a.output/'process.json'),admission_sha256=file_sha(a.admission),
            supervisor_pre_admission_seconds=pre,supervisor_post_admission_reserve_seconds=post,worker_timeout_seconds=remaining)
        dump(a.output/'summary.json',summary);return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
        dump(a.output/'summary.json',dict(complete=False,requested_tasks=2,accounted_tasks=2,original_denominator=40,
            unknown_generations=2,requested_ids=list(IDS),unattempted_ids=None,accounting_unverified=True,
            optimizer_updates=0,verification_pending=True,total_seconds=time.monotonic()-started));raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','generate','worker'))
    for name in INPUTS:p.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--admission',type=Path);p.add_argument('--worker-seconds',type=float)
    a=p.parse_args()
    if a.mode=='admit':
        value=admit(a)
        with a.output.open('x') as stream:json.dump(value,stream,indent=2);stream.write('\n')
    elif a.admission is None:p.error('Saved full target CPU admission required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
