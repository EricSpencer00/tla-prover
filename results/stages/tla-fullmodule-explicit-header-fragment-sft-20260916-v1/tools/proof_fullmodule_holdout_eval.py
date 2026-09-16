"""Paired protected30 full-module SANY diagnosis; not an official Gate2 replication."""
import argparse
import json
import math
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
# The frozen trainer sets CPU4 before any numerical imports.
from tools import proof_sany_repair_learning_eval as prior
from harness.proof_owned_process import run_owned,as_runner_tuple
base=prior.base;train=prior.train;common=prior.common;learning=prior.learning
load=prior.load;dump=prior.dump;digest=prior.digest;file_sha=prior.file_sha
PARENT_SHA='1bb603f605ddc0307631b0db4bda3fdfa109b5e0493f4508db05334deff87ee2'
CHILD_SHA='88660d5a17eab6ae23adf109e5619db0feb986254e8b46460899a528781cdde3'
TRAIN_SHA='d370761500e0f828f536d74fffd7d9785df34215ffa61c09490bccbcfe6544d7'
ARMS=('parent','child')
BUDGET=dict(requested_per_arm=30,requested_total=60,attempts_per_task=1,max_new_tokens=16384,
    do_sample=False,num_beams=1,num_return_sequences=1,item_seconds=30,seconds=3000,
    seed=20261007,memory_bytes=36*1024**3,cpu_threads=4,truncation=False,
    minimum_post_admission_seconds=120,admission_reserve_multiplier=1.25,arm_restore_reserve_seconds=60,
    official_gate2_replication=False,optimizer_updates=0)
PATHS=('packet','model_path','parent_checkpoint','checkpoint','training_input','training_admission','training_output')
SOURCES=tuple(sorted(set(prior.SOURCES)|{'tools/proof_fullmodule_holdout_eval.py',
    'tools/proof_fullmodule_holdout_eval.pbs','tools/proof_fullmodule_holdout_packet.py'}))


def sources():
    from tools import proof_fullmodule_holdout_packet as packet
    names=set(SOURCES)|set(packet.SOURCES)
    return {name:file_sha(ROOT/name) for name in sorted(names)}


def reserve(seconds):return max(120.,1.25*seconds)


def finite(value,limit,zero=False):
    if type(value) not in (int,float) or not math.isfinite(value) or not (0<=value<=limit if zero else 0<value<=limit):
        raise ValueError('Finite bounded actual duration required')


def packet_rows(a):
    from tools import proof_fullmodule_holdout_packet as packet
    if file_sha(a.packet)!=a.expected_packet_sha256:raise ValueError('Exact frozen protected30 prompt packet required')
    rows=packet.validate_packet(load(a.packet))
    if len(rows)!=30 or len({r['id'] for r in rows})!=30:raise ValueError('All30 distinct protected tasks required')
    return rows


def encode(tokenizer,row):
    encoded=common.encode_prompt(tokenizer,row)
    return dict(encoded,status='ready')  # New full-context contract only; original bytes/tokens unchanged.


def paired_admit(a):
    started=time.monotonic();before=sources();rows=packet_rows(a)
    from tools import proof_fullmodule_holdout_packet as packet
    prompt_environment=packet.environment()
    args=SimpleNamespace(input=a.training_input,model_path=a.model_path,checkpoint=a.parent_checkpoint,
        expected_input_sha256=TRAIN_SHA,output=a.training_output,admission=a.training_admission)
    admitted=learning.admit(args)
    if admitted!=load(a.training_admission):raise ValueError('Authentic actual84-SFT admission required')
    receipt_args=SimpleNamespace(training_input=a.training_input,model_path=a.model_path,parent_checkpoint=a.parent_checkpoint,
        expected_input_sha256=TRAIN_SHA,training_output=a.training_output,training_admission=a.training_admission,checkpoint=a.checkpoint)
    receipt=prior.training_receipt(receipt_args,dict(training_admission=admitted))
    if receipt['parent_sha256']!=PARENT_SHA or receipt['child_sha256']!=CHILD_SHA or receipt['optimizer_updates']!=84:
        raise ValueError('Actual immutable1bb6→88660d5 ancestry required')
    import torch,transformers
    torch.set_num_threads(4)
    files=train.model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS:
        raise ValueError('Exact frozen base model/runtime required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encodings=[encode(tokenizer,row) for row in rows]
    for row,encoding in zip(rows,encodings):
        if any(row.get(k)!=v for k,v in encoding.items() if k!='status'):
            raise ValueError('Actual full prompt/render/token bytes differ from protected packet')
    config=load(a.model_path/'config.json');context=max(e['input_tokens'] for e in encodings)+16384
    if config['max_position_embeddings']!=131072 or context>131072:
        raise ValueError('Original actual128k capability and complete requested contexts required')
    if load(a.model_path/'generation_config.json')['eos_token_id']!=common.EOS_IDS:
        raise ValueError('Original actual EOS configuration required')
    policies={}
    for arm,path,pin in (('parent',a.parent_checkpoint,PARENT_SHA),('child',a.checkpoint,CHILD_SHA)):
        if file_sha(path)!=pin:raise ValueError('Exact matched frozen checkpoint required')
        saved=torch.load(path,map_location='cpu',weights_only=False)
        cfg=base.stochastic.checkpoint_state(saved,files)
        policies[arm]=dict(checkpoint_sha256=pin,checkpoint_config_sha256=cfg)
        del saved
    if sources()!=before or file_sha(a.packet)!=a.expected_packet_sha256:
        raise ValueError('Source or protected packet changed during admission')
    return dict(schema=1,kind='protected30_fullmodule_paired_sany_diagnostic',budget=BUDGET,
        task_ids=[r['id'] for r in rows],tasks=rows,encodings=encodings,packet_sha256=a.expected_packet_sha256,
        policies=policies,phase_order=list(ARMS),declared_context=context,model_max_position_embeddings=131072,
        model_files=files,model_files_sha256=digest(files),versions=common.runtime_versions(),profile=train.PROFILE,
        eos_token_ids=common.EOS_IDS,source_sha256=before,cpu_environment=base.CPU_ENV,
        prompt_environment=prompt_environment,
        training_receipt=receipt,training_admission_sha256=file_sha(a.training_admission),
        optimizer_updates=0,verification_pending=True,training_authorized=False,protected_outputs_never_train=True,
        official_gate2_replication=False,tlc_claim=False,gate_claim=False,
        scope='Paired greedy1 at fixed30s/item and16384 token ceiling; SANY diagnosis only, not TLC/pass32/G2 completion')


admit=paired_admit


def output_fields(tokens,reply,*,late=False):
    if (not isinstance(tokens,list) or len(tokens)>16384 or any(type(t) is not int or not 0<=t<128256 for t in tokens) or
        common.trim_output(tokens,set(common.EOS_IDS))!=tokens):raise ValueError('Exact bounded output token evidence required')
    eos=bool(tokens and tokens[-1] in common.EOS_IDS);cap=len(tokens)==16384
    # Completed EOS takes precedence over max_time's after-call wall-clock overrun.
    finish='eos' if eos else 'token_limit' if cap else 'time_limit'
    return dict(token_ids=tokens,token_ids_sha256=digest(tokens),output_tokens=len(tokens),raw_reply=reply,
        raw_reply_sha256=train.sha(reply.encode()),finish_reason=finish,eos_reached=eos,hit_token_limit=cap,
        deadline_exceeded=bool(late),status='generation_time_limit' if finish=='time_limit' else 'generated')


def unknown(encoding,arm,reason='worker_pending'):
    return dict(encoding,arm=arm,status='unattempted',reason=reason)


def initial_rows(frozen):return [unknown(e,arm) for arm in ARMS for e in frozen['encodings']]


def validate_rows(frozen,rows,tokenizer=None):
    if frozen['budget']!=BUDGET or len(rows)!=60 or len(frozen['encodings'])!=30:
        raise ValueError('Exact all60 paired accounting required')
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
    return {arm:dict(requested=30,accounted=sum(r['arm']==arm for r in rows),
        generated=sum(r['arm']==arm and r['status']!='unattempted' for r in rows),
        eos=sum(r['arm']==arm and r.get('finish_reason')=='eos' for r in rows),
        unknown=sum(r['arm']==arm and r.get('finish_reason')!='eos' for r in rows)) for arm in ARMS}


def memory(output,phase):
    import torch
    value=dict(phase=phase,allocated=torch.cuda.max_memory_allocated(),reserved=torch.cuda.max_memory_reserved())
    with (output/'memory.jsonl').open('a') as stream:stream.write(json.dumps(value)+'\n');stream.flush()
    base.greedy.memory_guard(value['allocated'],value['reserved'])
    return value


def preflight(net,frozen,output,arm,*,device='cuda',measure=None,release=None,test_only=False):
    """Full declared-context synthetic instrumentation, never a model sample."""
    import torch
    if device!='cuda' and not test_only:raise ValueError('Actual production memory preflight requires CUDA')
    measure=measure or (lambda phase:memory(output,phase))
    release=release or (lambda:train.release_unused_cache(device,True))
    length=frozen['declared_context'];ids=torch.full((1,length-1),1,device=device,dtype=torch.long)
    with torch.inference_mode(),train.autocast(device):
        result=net(input_ids=ids,attention_mask=torch.ones_like(ids),use_cache=True,logits_to_keep=1)
        before=measure(arm+'_preflight_prefill')
        cache=result.past_key_values
        if cache.get_seq_length()!=length-1:raise ValueError('Actual full-context causalKV prefill required')
        next_result=net(input_ids=ids[:,:1],attention_mask=torch.ones((1,length),device=device,dtype=torch.long),
            past_key_values=cache,use_cache=True,logits_to_keep=1)
        if device=='cuda':torch.cuda.synchronize()
        after=measure(arm+'_preflight_decode')
        if next_result.past_key_values.get_seq_length()!=length or not bool(torch.isfinite(next_result.logits).all()):
            raise ValueError('Actual full-context cacheddecode/finite logits required')
    report=dict(arm=arm,synthetic=True,model_result=False,context=length,prefill_tokens=length-1,decode_tokens=1,
        use_cache=True,logits_to_keep=1,token_id=1,logits_finite=True,device=device,test_only=test_only,
        prefill_memory=before,decode_memory=after)
    dump(output/(arm+'_preflight.json'),report)
    del result,next_result,cache,ids
    release()
    return report


def save_rng(output,arm,label):
    import torch
    path=output/(arm+'_rng_'+label+'.pt')
    torch.save(dict(seed=BUDGET['seed'],cpu=torch.get_rng_state(),cuda=torch.cuda.get_rng_state()),path)
    return file_sha(path)


def restore(net,a,frozen,arm):
    import torch
    path=a.parent_checkpoint if arm=='parent' else a.checkpoint
    saved=torch.load(path,map_location='cpu',weights_only=False)
    if base.stochastic.checkpoint_state(saved,frozen['model_files'])!=frozen['policies'][arm]['checkpoint_config_sha256']:
        raise ValueError('Actual arm checkpoint configuration changed')
    selected=train.restore_policy(net,saved,frozen['model_files'])
    initial={n:v.clone() for n,v in saved['trainable_state'].items()}
    base.stochastic.assert_unchanged(selected,initial)
    if any(p.requires_grad for p in net.parameters()):raise ValueError('All parameters frozen; no optimizer')
    return selected,initial


def _worker(a):
    started=time.monotonic();frozen=load(a.admission);finite(a.worker_seconds,3000)
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
        raise TimeoutError('Measured overhead leaves insufficient fixed60×30s plus post/restore reserve; no samples')
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
                if a.worker_seconds-(time.monotonic()-started)-post<30:
                    raise TimeoutError('Fixed sampletime unavailable; never shorten an arm')
                row=dict(encode(tokenizer,task),arm=arm)
                if {k:v for k,v in row.items() if k!='arm'}!=frozen['encodings'][index]:raise ValueError('Actual input token drift')
                ids=torch.tensor([row['input_token_ids']],device='cuda');item=time.monotonic()
                with torch.inference_mode(),train.autocast('cuda'):
                    result=net.generate(input_ids=ids,attention_mask=torch.ones_like(ids),do_sample=False,num_beams=1,
                        num_return_sequences=1,max_new_tokens=16384,max_time=30,pad_token_id=pad)
                torch.cuda.synchronize();elapsed=time.monotonic()-item
                tokens=common.trim_output(result[0,ids.shape[1]:].tolist(),set(common.EOS_IDS))
                row.update(output_fields(tokens,common.decode_reply(tokenizer,tokens),late=elapsed>30))
                rows[arm_index*30+index]=row;dump(a.output/'accounting.json',rows)
                stream.write(json.dumps(row)+'\n');stream.flush()
                timing.append(dict(arm=arm,id=task['id'],limit_seconds=30,actual_seconds=elapsed));dump(a.output/'timing.json',timing)
                memory(a.output,arm+'_sample_'+str(index));del result,ids
            base.stochastic.assert_unchanged(selected,initial);rng[arm]['after']=save_rng(a.output,arm,'after')
            del selected,initial
    validate_rows(frozen,rows,tokenizer);stable=paired_admit(a)==frozen
    final_memory=memory(a.output,'after_final_admission');elapsed=time.monotonic()-started
    summary=dict(complete=stable and elapsed<=a.worker_seconds,counts=accounting(rows),elapsed_seconds=elapsed,
        pre_admission_seconds=pre,post_admission_reserve_seconds=post,measured_presampling_seconds=overhead,
        worker_seconds=a.worker_seconds,
        memory=final_memory,rng_sha256=rng,weights_unchanged=True,restore_exact=True,full_admission_stable=stable,
        optimizer_updates=0,verification_pending=True,protected_outputs_never_train=True,gate_claim=False,
        policies=frozen['policies'],accounting_sha256=file_sha(a.output/'accounting.json'))
    dump(a.output/'worker_summary.json',summary)
    if not summary['complete']:raise RuntimeError('Incomplete bounded paired60; no admitted samples')


def worker(a):
    try:return _worker(a)
    except BaseException as exc:
        try:
            import torch
            if torch.cuda.is_available():memory(a.output,'worker_failure')
        except Exception:pass  # Retain raw peak before guard, never mask original failure.
        dump(a.output/'worker_failure.json',dict(error=type(exc).__name__+': '+str(exc),
            requested=60,complete=False,optimizer_updates=0,protected_outputs_never_train=True))
        raise


def validate_worker(frozen,output,tokenizer=None):
    import torch
    rows=load(output/'accounting.json');validate_rows(frozen,rows,tokenizer);summary=load(output/'worker_summary.json')
    if (summary['counts']!=accounting(rows) or any(r['status']=='unattempted' for r in rows) or
        any(summary.get(k) is not True for k in ('complete','weights_unchanged','restore_exact','full_admission_stable','verification_pending','protected_outputs_never_train')) or
        summary['optimizer_updates']!=0 or summary['gate_claim'] is not False or summary['policies']!=frozen['policies'] or
        summary['accounting_sha256']!=file_sha(output/'accounting.json')):raise ValueError('Complete actual paired60 worker evidence required')
    finite(summary['elapsed_seconds'],3000);finite(summary['pre_admission_seconds'],3000)
    finite(summary['worker_seconds'],3000);finite(summary['elapsed_seconds'],summary['worker_seconds'])
    finite(summary['measured_presampling_seconds'],summary['worker_seconds'])
    if (summary['measured_presampling_seconds']<summary['pre_admission_seconds'] or
        summary['worker_seconds']-summary['measured_presampling_seconds']-summary['post_admission_reserve_seconds']<1860):
        raise ValueError('Measured overhead must leave every fixed60×30s plus restore reserve')
    if summary['post_admission_reserve_seconds']!=reserve(summary['pre_admission_seconds']):raise ValueError('Measured final admission reserve required')
    raw=(output/'events.jsonl').read_bytes()
    if not raw.endswith(b'\n') or [json.loads(s) for s in raw.splitlines()]!=rows:raise ValueError('Exact all60 raw event binding required')
    timing=load(output/'timing.json')
    if [(r['arm'],r['id']) for r in timing]!=[(r['arm'],r['id']) for r in rows]:raise ValueError('All60 timing keys required')
    for record,row in zip(timing,rows):
        finite(record['actual_seconds'],3000)
        if record['limit_seconds']!=30 or row['deadline_exceeded']!=(record['actual_seconds']>30):raise ValueError('Actual fixed30s request timing required')
    records=[json.loads(s) for s in (output/'memory.jsonl').read_text().splitlines()]
    phases=['after_model_load']+[arm+'_preflight_'+phase for arm in ARMS for phase in ('restore','prefill','decode')]
    phases += [phase for arm in ARMS for phase in [arm+'_generation_restore']+[arm+'_sample_'+str(i) for i in range(30)]]+['after_final_admission']
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
    return result+['--expected-packet-sha256',a.expected_packet_sha256]


def validate_output(a,frozen):
    rows=validate_worker(frozen,a.output);worker=load(a.output/'worker_summary.json');summary=load(a.output/'summary.json')
    pre=summary['supervisor_pre_admission_seconds'];finite(pre,3000)
    post=reserve(pre);seconds=3000-pre-post
    if (summary['supervisor_post_admission_reserve_seconds']!=post or summary['worker_timeout_seconds']!=seconds or
        worker['worker_seconds']!=seconds):raise ValueError('Exact actual shared supervisor/worker budget required')
    process=load(a.output/'process.json');root=Path(process['cwd']).resolve()
    if file_sha(root/'tools/proof_fullmodule_holdout_eval.py')!=file_sha(Path(__file__)):
        raise ValueError('Actual evaluator source differs')
    command=[sys.executable,str(root/'tools/proof_fullmodule_holdout_eval.py'),'worker']+command_args(a)+[
        '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(seconds)]
    base.historical.process_ok(process,command,root,seconds)
    extras={'total_seconds','supervisor_pre_admission_seconds','supervisor_post_admission_reserve_seconds',
            'worker_timeout_seconds','process_sha256','admission_sha256'}
    if ({k:v for k,v in summary.items() if k not in extras}!=worker or
        summary['process_sha256']!=file_sha(a.output/'process.json') or summary['admission_sha256']!=file_sha(a.admission) or
        load(a.output/'admission.json')!=frozen):raise ValueError('Exact complete supervisor receipt required')
    finite(summary['total_seconds'],3000)
    return rows


def run(a):
    started=time.monotonic();a.output=a.output.resolve()
    for name in (*PATHS,'admission'):
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint immutable inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    frozen=load(a.admission);rows=initial_rows(frozen);dump(a.output/'accounting.json',rows)
    dump(a.output/'summary.json',dict(complete=False,counts=accounting(rows),optimizer_updates=0,protected_outputs_never_train=True))
    try:
        if paired_admit(a)!=frozen:raise ValueError('Authentic complete prelaunch paired admission changed')
        dump(a.output/'admission.json',frozen)
        pre=time.monotonic()-started;post=reserve(pre);seconds=3000-pre-post
        if seconds<1800+120+60:raise TimeoutError('Insufficient fixed all60 sample budget after measured admission')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']+command_args(a)+[
            '--admission',str(a.output/'admission.json'),'--output',str(a.output),'--worker-seconds',str(seconds)]
        process=run_owned(command,ROOT,seconds);dump(a.output/'process.json',process)
        base.historical.process_ok(process,command,ROOT,seconds)
        validate_worker(frozen,a.output)
        if paired_admit(a)!=frozen or load(a.admission)!=frozen:raise ValueError('Full final paired admission drift')
        elapsed=time.monotonic()-started;finite(elapsed,3000)
        summary=load(a.output/'worker_summary.json');finite(summary['elapsed_seconds'],seconds)
        summary.update(total_seconds=elapsed,supervisor_pre_admission_seconds=pre,supervisor_post_admission_reserve_seconds=post,
            worker_timeout_seconds=seconds,process_sha256=file_sha(a.output/'process.json'),admission_sha256=file_sha(a.admission))
        dump(a.output/'summary.json',summary);validate_output(a,frozen);return summary
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)))
        dump(a.output/'summary.json',dict(complete=False,requested=60,accounting_unverified=True,optimizer_updates=0,
            protected_outputs_never_train=True,gate_claim=False,total_seconds=time.monotonic()-started));raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','run','worker'))
    for name in PATHS:p.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    p.add_argument('--expected-packet-sha256',required=True);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--admission',type=Path);p.add_argument('--worker-seconds',type=float)
    a=p.parse_args()
    if a.mode=='admit':
        with a.output.open('x') as stream:json.dump(paired_admit(a),stream,indent=2);stream.write('\n')
    elif a.admission is None:p.error('Saved actual full target admission required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
