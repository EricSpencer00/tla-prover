"""Paired TRAIN20 autoregressive syntax probe; no holdout, generalization, or proof claim."""
import argparse
import json
import math
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_learning_eval as lineage
from tools import proof_fullmodule_train_probe_packet as packet
from harness.proof_owned_process import run_owned
base=lineage.base;train=lineage.train;common=lineage.common;learning=lineage.learning
load=lineage.load;dump=lineage.dump;digest=lineage.digest;file_sha=lineage.file_sha
PARENT_SHA=lineage.PARENT_SHA
ARMS=('parent','child')
BUDGET=dict(requested_per_arm=20,requested_total=40,attempts_per_task=1,max_new_tokens=16384,
    do_sample=False,num_beams=1,num_return_sequences=1,item_seconds=45,seconds=3420,
    seed=20261010,memory_bytes=36*1024**3,cpu_threads=4,truncation=False,
    minimum_post_admission_seconds=120,admission_reserve_multiplier=1.25,arm_restore_reserve_seconds=60,
    official_gate2_replication=False,optimizer_updates=0,train_only=True)
PATHS=lineage.PATHS
HASH_ARGS=lineage.HASH_ARGS
SOURCES=tuple(sorted(set(lineage.SOURCES)|set(packet.SOURCES)|{
    'tools/proof_fullmodule_train_probe_eval.py','tools/proof_fullmodule_train_probe_eval.pbs'}))

# Frozen pure instrumentation/receipt helpers. Never call the TRAIN packet/admission path.
reserve=lineage.reserve;finite=lineage.finite;audit_process=lineage.audit_process
encode=lineage.encode;training_args=lineage.training_args;training_receipt=lineage.training_receipt
output_fields=lineage.output_fields;unknown=lineage.unknown
memory=lineage.memory;preflight=lineage.preflight;restore=lineage.restore


def sources():
    return {name:file_sha(ROOT/name) for name in sorted(set(SOURCES)|set(lineage.sources()))}


def packet_rows(a):
    if file_sha(a.packet)!=a.expected_packet_sha256:raise ValueError('Exact frozen TRAIN20 prompt packet required')
    rows=packet.validate_export(load(a.packet))
    if (len(rows)!=20 or len({r['id'] for r in rows})!=20 or any(r['split']!='train' for r in rows)
        or a.expected_input_sha256!=packet.INPUT_SHA or a.expected_child_sha256!=packet.POLICIES['child']):
        raise ValueError('Exact TRAIN20 membership and actual338 policy/input bindings required')
    return rows


def environment(value):
    import os
    expected=value['prompt_environment']
    if any(os.environ.get(n,'1' if n=='GEN_EVAL_CONCURRENCY' else '0')!=v for n,v in expected.items()):
        raise ValueError('Frozen original TRAIN prompt environment required')
    if packet.training.audit.framing.framing.GEN_EVAL_CONCURRENCY!=1:raise ValueError('Imported generation concurrency changed')
    return dict(expected)


def paired_admit(a):
    started=time.monotonic();before=sources();rows=packet_rows(a)
    prompt_environment=environment(load(a.packet))
    args=training_args(a)
    admitted=learning.admit(args)
    if admitted!=load(a.training_admission):raise ValueError('Authentic actual338-SFT admission required')
    receipt=training_receipt(a,admitted)
    import torch,transformers
    torch.set_num_threads(4)
    files=train.model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS:
        raise ValueError('Exact frozen base model/runtime required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encodings=[encode(tokenizer,row) for row in rows]
    for row,encoding in zip(rows,encodings):
        if any(row.get(k)!=v for k,v in encoding.items() if k!='status'):
            raise ValueError('Actual full prompt/render/token bytes differ from TRAIN packet')
    config=load(a.model_path/'config.json');context=max(e['input_tokens'] for e in encodings)+16384
    if config['max_position_embeddings']!=131072 or context>131072:
        raise ValueError('Original actual128k capability and complete requested contexts required')
    if load(a.model_path/'generation_config.json')['eos_token_id']!=common.EOS_IDS:
        raise ValueError('Original actual EOS configuration required')
    policies={}
    for arm,path,pin in (('parent',a.parent_checkpoint,PARENT_SHA),('child',a.checkpoint,a.expected_child_sha256)):
        if file_sha(path)!=pin:raise ValueError('Exact matched frozen checkpoint required')
        saved=torch.load(path,map_location='cpu',weights_only=False)
        cfg=base.stochastic.checkpoint_state(saved,files)
        policies[arm]=dict(checkpoint_sha256=pin,checkpoint_config_sha256=cfg)
        del saved
    if sources()!=before or file_sha(a.packet)!=a.expected_packet_sha256:
        raise ValueError('Source or TRAIN packet changed during admission')
    return dict(schema=1,kind='train20_fullmodule_paired45_sany_diagnostic',budget=BUDGET,
        task_ids=[r['id'] for r in rows],tasks=rows,encodings=encodings,packet_sha256=a.expected_packet_sha256,
        policies=policies,phase_order=list(ARMS),declared_context=context,model_max_position_embeddings=131072,
        model_files=files,model_files_sha256=digest(files),versions=common.runtime_versions(),profile=train.PROFILE,
        eos_token_ids=common.EOS_IDS,source_sha256=before,cpu_environment=base.CPU_ENV,
        prompt_environment=prompt_environment,
        training_receipt=receipt,training_admission_sha256=file_sha(a.training_admission),
        training_input_sha256=a.expected_input_sha256,expected_child_sha256=a.expected_child_sha256,
        optimizer_updates=0,verification_pending=True,training_authorized=False,train_only=True,
        official_gate2_replication=False,tlc_claim=False,gate_claim=False,
        holdout_claim=False,generalization_claim=False,proof_claim=False,
        scope='Fixed TRAIN20 greedy1 system diagnostic only; no holdout, generalization, TLC, proof or G2 claim')


admit=paired_admit


def initial_rows(frozen):return [unknown(e,arm) for arm in ARMS for e in frozen['encodings']]


def validate_rows(frozen,rows,tokenizer=None):
    if frozen['budget']!=BUDGET or len(rows)!=40 or len(frozen['encodings'])!=20:
        raise ValueError('Exact all40 paired accounting required')
    for expected,row in zip(initial_rows(frozen),rows):
        fixed={k:v for k,v in expected.items() if k not in ('status','reason')}
        if any(row.get(k)!=v for k,v in fixed.items()):raise ValueError('Exact ordered paired input binding required')
        if row.get('status')=='unattempted':
            if row!=dict(fixed,status='unattempted',reason=row.get('reason')) or not isinstance(row.get('reason'),str) or not row['reason']:
                raise ValueError('Explicit unattempted unknown required')
        else:
            actual=dict(fixed,**output_fields(row['token_ids'],row['raw_reply'],late=row['deadline_exceeded']))
            if row!=actual:raise ValueError('Exact actual EOS/cap/time accounting required')
            if tokenizer is not None and common.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Exact raw decoder reconstruction required')


def accounting(rows):
    return {arm:dict(requested=20,accounted=sum(r['arm']==arm for r in rows),
        generated=sum(r['arm']==arm and r['status']!='unattempted' for r in rows),
        eos=sum(r['arm']==arm and r.get('finish_reason')=='eos' for r in rows),
        unknown=sum(r['arm']==arm and r.get('finish_reason')!='eos' for r in rows)) for arm in ARMS}


def save_rng(output,arm,label):
    import torch
    path=output/(arm+'_rng_'+label+'.pt')
    torch.save(dict(seed=BUDGET['seed'],cpu=torch.get_rng_state(),cuda=torch.cuda.get_rng_state()),path)
    return file_sha(path)


def _worker(a):
    started=time.monotonic();frozen=load(a.admission);finite(a.worker_seconds,3420)
    if paired_admit(a)!=frozen:raise ValueError('Full actual paired admission changed')
    pre=time.monotonic()-started;post=reserve(pre)
    import torch,transformers
    torch.set_num_threads(4);torch.backends.cuda.matmul.allow_tf32=False;torch.cuda.reset_peak_memory_stats()
    net=train.load_policy(a.model_path,device='cuda');memory(a.output,'after_model_load')
    if net.config.max_position_embeddings!=131072 or net.generation_config.eos_token_id!=common.EOS_IDS:
        raise ValueError('Unmodified actual model context/EOS required')
    for arm in ARMS:
        selected,initial=restore(net,a,frozen,arm);memory(a.output,arm+'_preflight_restore')
        preflight(net,frozen,a.output,arm);base.stochastic.assert_unchanged(selected,initial)
        del selected,initial
    overhead=time.monotonic()-started
    if a.worker_seconds-overhead-post<1800+BUDGET['arm_restore_reserve_seconds']:
        raise TimeoutError('Measured overhead leaves insufficient fixed40×45s plus post/restore reserve; no samples')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    pad=tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if type(pad) is not int:raise ValueError('Scalar original pad required')
    rows=initial_rows(frozen);dump(a.output/'accounting.json',rows);rng={};timing=[]
    with (a.output/'events.jsonl').open('x') as stream:
        for arm_index,arm in enumerate(ARMS):
            selected,initial=restore(net,a,frozen,arm);memory(a.output,arm+'_generation_restore')
            # Synthetic probes cannot consume the actual sampling RNG stream.
            torch.manual_seed(BUDGET['seed']);torch.cuda.manual_seed(BUDGET['seed'])
            rng[arm]={'before':save_rng(a.output,arm,'before')}
            for index,task in enumerate(frozen['tasks']):
                if a.worker_seconds-(time.monotonic()-started)-post<45:
                    raise TimeoutError('Fixed sampletime unavailable; never shorten an arm')
                row=dict(encode(tokenizer,task),arm=arm)
                if {k:v for k,v in row.items() if k!='arm'}!=frozen['encodings'][index]:raise ValueError('Actual input token drift')
                ids=torch.tensor([row['input_token_ids']],device='cuda');item=time.monotonic()
                with torch.inference_mode(),train.autocast('cuda'):
                    result=net.generate(input_ids=ids,attention_mask=torch.ones_like(ids),do_sample=False,num_beams=1,
                        num_return_sequences=1,max_new_tokens=16384,max_time=45,pad_token_id=pad)
                torch.cuda.synchronize();elapsed=time.monotonic()-item
                tokens=common.trim_output(result[0,ids.shape[1]:].tolist(),set(common.EOS_IDS))
                row.update(output_fields(tokens,common.decode_reply(tokenizer,tokens),late=elapsed>45))
                rows[arm_index*20+index]=row;dump(a.output/'accounting.json',rows)
                stream.write(json.dumps(row)+'\n');stream.flush()
                timing.append(dict(arm=arm,id=task['id'],limit_seconds=45,actual_seconds=elapsed));dump(a.output/'timing.json',timing)
                memory(a.output,arm+'_sample_'+str(index));del result,ids
            base.stochastic.assert_unchanged(selected,initial);rng[arm]['after']=save_rng(a.output,arm,'after')
            del selected,initial
    validate_rows(frozen,rows,tokenizer);stable=paired_admit(a)==frozen
    final_memory=memory(a.output,'after_final_admission');elapsed=time.monotonic()-started
    summary=dict(complete=stable and elapsed<=a.worker_seconds,counts=accounting(rows),elapsed_seconds=elapsed,
        pre_admission_seconds=pre,post_admission_reserve_seconds=post,measured_presampling_seconds=overhead,
        worker_seconds=a.worker_seconds,
        memory=final_memory,rng_sha256=rng,weights_unchanged=True,restore_exact=True,full_admission_stable=stable,
        optimizer_updates=0,verification_pending=True,train_only=True,gate_claim=False,
        policies=frozen['policies'],accounting_sha256=file_sha(a.output/'accounting.json'))
    dump(a.output/'worker_summary.json',summary)
    if not summary['complete']:raise RuntimeError('Incomplete bounded paired40; no admitted samples')


def worker(a):
    try:return _worker(a)
    except BaseException as exc:
        try:
            import torch
            if torch.cuda.is_available():memory(a.output,'worker_failure')
        except Exception:pass  # Retain raw peak before guard, never mask original failure.
        dump(a.output/'worker_failure.json',dict(error=type(exc).__name__+': '+str(exc),
            requested=40,complete=False,optimizer_updates=0,train_only=True))
        raise


def validate_worker(frozen,output,tokenizer=None):
    import torch
    rows=load(output/'accounting.json');validate_rows(frozen,rows,tokenizer);summary=load(output/'worker_summary.json')
    if (summary['counts']!=accounting(rows) or any(r['status']=='unattempted' for r in rows) or
        any(summary.get(k) is not True for k in ('complete','weights_unchanged','restore_exact','full_admission_stable','verification_pending','train_only')) or
        summary['optimizer_updates']!=0 or summary['gate_claim'] is not False or summary['policies']!=frozen['policies'] or
        summary['accounting_sha256']!=file_sha(output/'accounting.json')):raise ValueError('Complete actual paired40 worker evidence required')
    finite(summary['elapsed_seconds'],3420);finite(summary['pre_admission_seconds'],3420)
    finite(summary['worker_seconds'],3420);finite(summary['elapsed_seconds'],summary['worker_seconds'])
    finite(summary['measured_presampling_seconds'],summary['worker_seconds'])
    if (summary['measured_presampling_seconds']<summary['pre_admission_seconds'] or
        summary['worker_seconds']-summary['measured_presampling_seconds']-summary['post_admission_reserve_seconds']<1860):
        raise ValueError('Measured overhead must leave every fixed40×45s plus restore reserve')
    if summary['post_admission_reserve_seconds']!=reserve(summary['pre_admission_seconds']):raise ValueError('Measured final admission reserve required')
    raw=(output/'events.jsonl').read_bytes()
    if not raw.endswith(b'\n') or [json.loads(s) for s in raw.splitlines()]!=rows:raise ValueError('Exact all40 raw event binding required')
    timing=load(output/'timing.json')
    if [(r['arm'],r['id']) for r in timing]!=[(r['arm'],r['id']) for r in rows]:raise ValueError('All40 timing keys required')
    for record,row in zip(timing,rows):
        finite(record['actual_seconds'],3420)
        if record['limit_seconds']!=45 or row['deadline_exceeded']!=(record['actual_seconds']>45):raise ValueError('Actual fixed45s request timing required')
    records=[json.loads(s) for s in (output/'memory.jsonl').read_text().splitlines()]
    phases=['after_model_load']+[arm+'_preflight_'+phase for arm in ARMS for phase in ('restore','prefill','decode')]
    phases += [phase for arm in ARMS for phase in [arm+'_generation_restore']+[arm+'_sample_'+str(i) for i in range(20)]]+['after_final_admission']
    if [r['phase'] for r in records]!=phases:raise ValueError('Exact complete raw memory phases required')
    for record in records:base.greedy.memory_guard(record['allocated'],record['reserved'])
    if summary['memory']!=records[-1]:raise ValueError('Final memory binding differs')
    for arm in ARMS:
        report=load(output/(arm+'_preflight.json'));length=frozen['declared_context']
        expected=dict(arm=arm,synthetic=True,model_result=False,context=length,prefill_tokens=length-1,decode_tokens=1,
            use_cache=True,logits_to_keep=1,token_id=1,logits_finite=True,device='cuda',test_only=False,
            prefill_memory=next(r for r in records if r['phase']==arm+'_preflight_prefill'),
            decode_memory=next(r for r in records if r['phase']==arm+'_preflight_decode'))
        if report!=expected:raise ValueError('Actual full declared-context synthetic probe required')
        for label in ('before','after'):
            path=output/(arm+'_rng_'+label+'.pt')
            if file_sha(path)!=summary['rng_sha256'][arm][label]:raise ValueError('Actual RNG bytes changed')
            rng=torch.load(path,map_location='cpu',weights_only=True)
            if set(rng)!=set(('seed','cpu','cuda')) or rng['seed']!=BUDGET['seed'] or any(rng[k].dtype!=torch.uint8 or rng[k].ndim!=1 or not rng[k].numel() for k in ('cpu','cuda')):
                raise ValueError('Actual arm RNG byte snapshots required')
    before=[torch.load(output/(arm+'_rng_before.pt'),map_location='cpu',weights_only=True) for arm in ARMS]
    if any(not torch.equal(before[0][k],before[1][k]) for k in ('cpu','cuda')):raise ValueError('Matched RNG reset after instrumentation required')
    return rows


def command_args(a):
    result=[]
    for name in PATHS:result+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
    for name in HASH_ARGS:result+=['--'+name.replace('_','-'),getattr(a,name)]
    return result


def validate_output(a,frozen):
    rows=validate_worker(frozen,a.output);worker=load(a.output/'worker_summary.json');summary=load(a.output/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];finite(pre,3420)
    post=reserve(pre);seconds=3420-pre-post
    if (summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds or
        worker['worker_seconds']!=seconds):raise ValueError('Exact actual shared supervisor/worker budget required')
    process=load(a.output/'process.json');root=Path(process['cwd']).resolve()
    if file_sha(root/'tools/proof_fullmodule_train_probe_eval.py')!=file_sha(Path(__file__)):
        raise ValueError('Actual evaluator source differs')
    command=[sys.executable,str(root/'tools/proof_fullmodule_train_probe_eval.py'),'worker']+command_args(a)+[
        '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(seconds)]
    audit_process(process,command,root,seconds)
    extras={'total_seconds','supervisor_pre_admission_seconds','supervisor_post_admission_reserve_seconds',
            'worker_timeout_seconds','process_sha256','admission_sha256'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker or
        summary['process_sha256']!=file_sha(a.output/'process.json') or summary['admission_sha256']!=file_sha(a.admission) or
        load(a.output/'admission.json')!=frozen):raise ValueError('Exact complete supervisor receipt required')
    finite(summary['total_seconds'],3420)
    return rows


def run(a):
    started=time.monotonic();a.output=a.output.resolve()
    for name in (*PATHS,'admission'):
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    frozen=load(a.admission);rows=initial_rows(frozen);dump(a.output/'accounting.json',rows)
    dump(a.output/'summary.json',dict(complete=False,counts=accounting(rows),optimizer_updates=0,train_only=True))
    try:
        if paired_admit(a)!=frozen:raise ValueError('Authentic complete prelaunch paired admission changed')
        dump(a.output/'admission.json',frozen)
        pre=time.monotonic()-started;post=reserve(pre);seconds=3420-pre-post
        if seconds<1800+120+60:raise TimeoutError('Insufficient fixed all40 sample budget after measured admission')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']+command_args(a)+[
            '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(seconds)]
        process=run_owned(command,ROOT,seconds);dump(a.output/'process.json',process)
        audit_process(process,command,ROOT,seconds)
        validate_worker(frozen,a.output)
        if paired_admit(a)!=frozen or load(a.admission)!=frozen:raise ValueError('Full final paired admission drift')
        elapsed=time.monotonic()-started;finite(elapsed,3420)
        summary=load(a.output/'worker_summary.json');finite(summary['elapsed_seconds'],seconds)
        summary.update(total_seconds=elapsed,supervisor_pre_admission_seconds=pre,supervisor_post_admission_reserve_seconds=post,
            worker_timeout_seconds=seconds,process_sha256=file_sha(a.output/'process.json'),admission_sha256=file_sha(a.admission))
        dump(a.output/'summary.json',summary);validate_output(a,frozen);return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
        dump(a.output/'summary.json',dict(complete=False,requested=40,accounting_unverified=True,optimizer_updates=0,
            train_only=True,gate_claim=False,total_seconds=time.monotonic()-started));raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','run','worker'))
    for name in PATHS:p.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    for name in HASH_ARGS:p.add_argument('--'+name.replace('_','-'),required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--admission',type=Path);p.add_argument('--worker-seconds',type=float)
    a=p.parse_args()
    if a.mode=='admit':
        with a.output.open('x') as stream:json.dump(paired_admit(a),stream,indent=2);stream.write('\n')
    elif a.admission is None:p.error('Saved actual full target admission required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
