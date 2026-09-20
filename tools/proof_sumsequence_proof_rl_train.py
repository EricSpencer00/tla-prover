"""One bounded proof-reward CPU-AdamW update; no generation or auto-evaluation."""
import argparse
import json
import math
import os
from pathlib import Path
import random
import resource
import sys
import time

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
# Admission's allocator guard must execute before importing torch dependencies.
from tools import proof_sumsequence_proof_rl_packet as packet
from tools import proof_sumsequence_compact_offload_probe as probe
from tools.proof_cpu_gradient_update import CPUGradientUpdate,validate_prepared
from harness.proof_owned_process import run_owned,as_runner_tuple

train=probe.train
SECONDS=900
CHECKPOINT_RESERVE=120
HOST_LIMIT=64*1024**3
SEED=20261004
if SEED!=packet.BUDGET['seed']:raise ValueError('Training seed differs from frozen packet')
PATHS=packet.PATHS


def admit(a):return packet.admit(a)


def guard_host(value):
    if type(value) is not int or not 0<value<=HOST_LIMIT:raise ValueError('Actual process peak RSS exceeds64GiB or is unavailable')


def peak_rss():
    value=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    return int(value if sys.platform=='darwin' else value*1024)


def record_guard(output,events,phase,*,cuda=True):
    record=dict(phase=phase,peak_rss_bytes=peak_rss())
    if cuda:record['allocator']=probe.allocator_evidence()
    events.append(record)
    pending=output/'memory.pending';train.dump(pending,events);pending.replace(output/'memory.json')
    guard_host(record['peak_rss_bytes'])
    if cuda:probe.guard_allocator(record['allocator'])
    return record


def validate_selected(selected):
    import torch
    if (set(selected)!=set(probe.GRADIENT_ELEMENTS) or
        any(p.dtype!=torch.float32 or not p.requires_grad or p.numel()!=probe.GRADIENT_ELEMENTS[n]
            or not bool(torch.isfinite(p).all()) for n,p in selected.items()) or
        sum(p.numel() for p in selected.values())!=218112000):
        raise ValueError('Exact finite nine layer31 FP32 tensors/218112000 parameters required')


def bind_requests(update,rows,feedback):
    if update.groups!=feedback['groups'] or feedback['requested_samples']!=32 or feedback['accounted_samples']!=32:
        raise ValueError('Full32 frozen proof-feedback groups required')
    if [r['sample_id'] for r in update.requests]!=[r['sample_id'] for r in rows] or len(rows)!=4:
        raise ValueError('Exactly four admitted Barriers eligible responses required')


def save_reload(net,selected,prepared,config,probe_ids,path,*,device='cuda',guard=lambda phase:None):
    import torch
    config=dict(config)
    parent=config.pop('_parent_state')
    validate_prepared(prepared,parent)
    if any(not torch.equal(p.detach().cpu(),prepared['trainable_state'][n]) for n,p in selected.items()):
        raise ValueError('Committed exact CPU child required before save')
    saved=dict(trainable_state=prepared['trainable_state'],optimizer=prepared['optimizer_state'],
        cpu_update=prepared,config=config,torch_rng_state=torch.get_rng_state(),python_rng_state=random.getstate(),
        cuda_rng_state=torch.cuda.get_rng_state_all() if device=='cuda' else None)
    guard('before_checkpoint_save')
    with path.open('xb') as stream:torch.save(saved,stream)
    guard('after_checkpoint_save')
    ids=torch.tensor([probe_ids],device=device)
    with torch.no_grad(),train.autocast(device):
        before=net(input_ids=ids,use_cache=False).logits[:,-1].detach().cpu().clone()
    guard('before_checkpoint_reload')
    restored=torch.load(path,map_location='cpu',weights_only=False)
    validate_prepared(restored['cpu_update'],parent)
    if restored['config']!=config or set(restored['trainable_state'])!=set(selected):raise ValueError('Reloaded checkpoint contract changed')
    if any(not torch.equal(restored['trainable_state'][n],v) for n,v in prepared['trainable_state'].items()):
        raise ValueError('Reloaded CPU child tensors differ')
    with torch.no_grad():
        for p in selected.values():p.zero_()
        for n,p in selected.items():p.copy_(restored['trainable_state'][n])
    with torch.no_grad(),train.autocast(device):
        after=net(input_ids=ids,use_cache=False).logits[:,-1].detach().cpu().clone()
    exact=all(torch.equal(p.detach().cpu(),restored['trainable_state'][n]) for n,p in selected.items())
    if not exact or not torch.equal(before,after):raise ValueError('Checkpoint exact tensor/logit reload failed')
    guard('after_checkpoint_reload')
    # Both actual vectors are persisted; this is fixed-prompt next-token logits,
    # not newly generated text or a proof improvement claim.
    evidence=dict(probe_ids=probe_ids,logits_before=before.tolist(),logits_after=after.tolist(),
        reload_tensors_exact=True,reload_logits_exact=True,checkpoint_sha256=train.file_sha(path))
    return evidence


def worker(a):
    import torch
    started=time.monotonic();frozen=json.loads(a.admission.read_bytes());memory=[]
    stage=dict(phase='worker_start',optimizer_attempted=False,optimizer_updates=0,
               gpu_commit_attempted=False,gpu_committed=False,checkpoint_attempted=False,checkpoint_writes=0)
    def progress(phase,**changes):
        stage.update(phase=phase,**changes)
        pending=a.output/'stage.pending';train.dump(pending,stage);pending.replace(a.output/'stage.json')
    progress('worker_start')
    if not CHECKPOINT_RESERVE<a.worker_seconds<=SECONDS or admit(a)!=frozen:
        raise ValueError('Frozen full training admission and bounded remaining worker time required')
    record_guard(a.output,memory,'after_worker_admission',cuda=False)
    rows=probe.select_rows([json.loads(s) for s in a.rollouts.read_bytes().splitlines()])
    random.seed(SEED);torch.manual_seed(SEED);torch.cuda.manual_seed_all(SEED)
    torch.set_num_threads(4);torch.backends.cuda.matmul.allow_tf32=False;torch.cuda.reset_peak_memory_stats()
    net=train.load_policy(a.model_path)
    if net.config.vocab_size!=probe.VOCAB_SIZE or net.generation_config.eos_token_id!=probe.EOS_IDS:
        raise ValueError('Actual frozen vocabulary/EOS contract required')
    record_guard(a.output,memory,'after_model_load')
    original=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    model_files=frozen['probe_admission']['inference_admission']['model_files']
    selected=train.restore_policy(net,original,model_files)
    probe.scoring.assert_parent_unchanged(selected,original['trainable_state']);del original
    selected=train.select_final_layer(net,True);validate_selected(selected)
    update=CPUGradientUpdate(selected,frozen['feedback']['rewards']);bind_requests(update,rows,frozen['feedback'])
    record_guard(a.output,memory,'after_cpu_accumulator_creation')
    train.dump(a.output/'hardware.json',dict(device=torch.cuda.get_device_name(),
        capability=list(torch.cuda.get_device_capability()),torch_version=torch.__version__,cpu_threads=torch.get_num_threads()))
    results=[dict(sample_id=r['sample_id'],status='unattempted') for r in rows];probe.snapshot_rows(a.output,results)
    def deadline(reserve=0):
        value=a.worker_seconds-(time.monotonic()-started)-reserve
        if value<=0:raise TimeoutError('Training deadline/checkpoint reserve exhausted')
        return value
    def guard(phase):
        if phase=='before_checkpoint_save':progress(phase,checkpoint_attempted=True,checkpoint_writes=None)
        elif phase=='after_checkpoint_save':progress(phase,checkpoint_writes=1)
        record_guard(a.output,memory,phase);deadline()
    with (a.output/'events.jsonl').open('x') as stream:
        for index,row in enumerate(rows):
            def emit(value):
                results[index]=dict(value);probe.snapshot_rows(a.output,results)
                stream.write(json.dumps(value)+'\n');stream.flush()
                if value['status']=='complete':
                    # probe_one emits completion before its finally clears
                    # device gradients; consume those exact unweighted grads.
                    guard('before_cpu_accumulate_'+row['sample_id'])
                    update.accumulate(row['sample_id'])
                    train.dump(a.output/'gradient_ledger.json',update.ledger)
                    guard('after_cpu_accumulate_'+row['sample_id'])
                elif 'allocator_after_forward' in value and value['status']=='scoring':
                    record_guard(a.output,memory,'forward_'+row['sample_id'])
            probe.probe_one(net,selected,row,seconds=deadline(CHECKPOINT_RESERVE),
                context=lambda:train.autocast('cuda'),emit=emit)
            update._unchanged();deadline(CHECKPOINT_RESERVE)
    probe.validate_results(rows,results)
    if len(update.ledger)!=4:raise ValueError('All four actual CPU gradient transfers required')
    guard('before_cpu_adamw');deadline(CHECKPOINT_RESERVE)
    progress('cpu_adamw_attempt',optimizer_attempted=True,optimizer_updates=None)
    prepared=update.prepare()
    train.dump(a.output/'update_summary.json',prepared['summary'])
    progress('cpu_adamw_completed',optimizer_updates=prepared['summary']['actual_updates'])
    guard('after_cpu_adamw');deadline(CHECKPOINT_RESERVE)
    if prepared['summary']['actual_updates']!=1:raise ValueError('Exactly one authorized proof-reward update required')
    guard('before_child_commit');progress('gpu_commit_attempt',gpu_commit_attempted=True,gpu_committed=None)
    update.commit();progress('gpu_committed',gpu_committed=True);guard('after_child_commit')
    config=dict(model_files=model_files,dtype_profile=train.PROFILE,training_contract=frozen,
        parent_checkpoint_sha256=train.file_sha(a.checkpoint),algorithm='proof_reward_cpu_gradient_adamw',
        seed=SEED,_parent_state=update.initial)
    evidence=save_reload(net,selected,prepared,config,rows[0]['input_token_ids'][:64],
        a.output/'policy_optimizer.pt',guard=guard)
    train.dump(a.output/'reload.json',evidence)
    guard('before_final_admission');stable=admit(a)==frozen;guard('after_final_admission')
    if not stable:raise ValueError('Parent file/source/model/proof admission changed')
    elapsed=time.monotonic()-started
    summary=dict(complete=True,identity_stable=True,requested_samples=32,accounted_samples=32,
        required_gradient_samples=4,completed_gradient_samples=4,optimizer_updates=1,checkpoint_writes=1,
        new_generation=False,elapsed_seconds=elapsed,rows_sha256=train.file_sha(a.output/'rows.json'),
        update_summary_sha256=train.file_sha(a.output/'update_summary.json'),
        checkpoint_sha256=evidence['checkpoint_sha256'],reload_sha256=train.file_sha(a.output/'reload.json'),
        memory_sha256=train.file_sha(a.output/'memory.json'),proof_success_claim=False)
    deadline();progress('complete');train.dump(a.output/'worker_summary.json',summary)


def validate_execution_evidence(original,results,update,ledger,memory,reload,elapsed):
    if type(elapsed) not in (int,float) or not math.isfinite(elapsed) or not 0<elapsed<=SECONDS:
        raise ValueError('Finite positive bounded worker elapsed time required')
    required={'after_cpu_adamw','after_child_commit','before_checkpoint_save',
              'after_checkpoint_reload','after_final_admission'}
    required.update('after_cpu_accumulate_'+r['sample_id'] for r in original)
    if not isinstance(memory,list) or not memory or not required.issubset({r.get('phase') for r in memory}):
        raise ValueError('Complete nonempty phase memory ledger required')
    for row in memory:
        guard_host(row['peak_rss_bytes'])
        if 'allocator' in row:probe.guard_allocator(row['allocator'])
        elif row['phase'] in required:raise ValueError('Required phase lacks GPU memory evidence')
    if ledger!=update['ledger'] or len(ledger)!=len(original) or len(results)!=len(original):
        raise ValueError('CPU gradient ledger differs from actual update summary')
    for expected,raw,cpu in zip(original,results,ledger):
        if cpu['sample_id']!=expected['sample_id'] or raw['sample_id']!=expected['sample_id']:
            raise ValueError('CPU/GPU gradient sample order mismatch')
        if set(cpu['gradients'])!=set(probe.GRADIENT_ELEMENTS) or set(raw['gradients'])!=set(cpu['gradients']):
            raise ValueError('Every actual CPU/GPU gradient required')
        for name,g in cpu['gradients'].items():
            if (any(g.get(k)!=raw['gradients'][name].get(k) for k in ('norm','dtype','elements')) or
                g['elements']!=probe.GRADIENT_ELEMENTS[name] or math.prod(g['shape'])!=g['elements'] or
                not g['source_device'].startswith('cuda:')):
                raise ValueError('Raw GPU gradient differs from consumed CPU gradient')
    for key in ('logits_before','logits_after'):
        values=reload.get(key)
        if (not isinstance(values,list) or len(values)!=1 or not isinstance(values[0],list) or
            len(values[0])!=probe.VOCAB_SIZE or any(type(v) not in (int,float) or not math.isfinite(v) for v in values[0])):
            raise ValueError('Actual finite [1,128256] reload logits required')


def validate_output(a,frozen):
    import torch
    summary=json.loads((a.output/'worker_summary.json').read_bytes())
    original=probe.select_rows([json.loads(s) for s in a.rollouts.read_bytes().splitlines()])
    results=json.loads((a.output/'rows.json').read_bytes());probe.validate_results(original,results)
    for key,file in [('rows','rows.json'),('update_summary','update_summary.json'),('checkpoint','policy_optimizer.pt'),
                     ('reload','reload.json'),('memory','memory.json')]:
        if summary[key+'_sha256']!=train.file_sha(a.output/file):raise ValueError('Saved training evidence identity mismatch')
    if (summary.get('complete') is not True or summary.get('identity_stable') is not True or
        any(summary.get(k)!=v for k,v in dict(requested_samples=32,accounted_samples=32,required_gradient_samples=4,
            completed_gradient_samples=4,optimizer_updates=1,checkpoint_writes=1,new_generation=False).items())):
        raise ValueError('Complete one-update full32 training accounting required')
    reload=json.loads((a.output/'reload.json').read_bytes())
    if (reload['reload_tensors_exact'] is not True or reload['reload_logits_exact'] is not True or
        reload['logits_before']!=reload['logits_after'] or reload['probe_ids']!=original[0]['input_token_ids'][:64] or
        reload['checkpoint_sha256']!=summary['checkpoint_sha256']):raise ValueError('Actual fixed-prompt exact reload required')
    update=json.loads((a.output/'update_summary.json').read_bytes())
    validate_execution_evidence(original,results,update,json.loads((a.output/'gradient_ledger.json').read_bytes()),
        json.loads((a.output/'memory.json').read_bytes()),reload,summary['elapsed_seconds'])
    if update['groups']!=frozen['feedback']['groups'] or update['actual_updates']!=1:
        raise ValueError('Frozen actual proof reward groups required')
    parent=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    saved=torch.load(a.output/'policy_optimizer.pt',map_location='cpu',weights_only=False)
    validate_prepared(saved['cpu_update'],parent['trainable_state'])
    # digest canonicalizes JSON's tuple->list conversion in optimizer betas.
    if (probe.digest(saved['cpu_update']['summary'])!=probe.digest(update) or
        saved['config']['training_contract']!=frozen or saved['config']['dtype_profile']!=train.PROFILE or
        saved['config']['seed']!=SEED or saved['config']['algorithm']!='proof_reward_cpu_gradient_adamw' or
        saved['config']['model_files']!=frozen['probe_admission']['inference_admission']['model_files'] or
        saved['config']['parent_checkpoint_sha256']!=train.file_sha(a.checkpoint) or
        saved['trainable_state'] is not saved['cpu_update']['trainable_state'] or
        saved['optimizer'] is not saved['cpu_update']['optimizer_state']):
        raise ValueError('Actual saved CPU optimizer/child/full training contract mismatch')
    stage=json.loads((a.output/'stage.json').read_bytes())
    if (stage.get('phase')!='complete' or stage.get('optimizer_updates')!=1 or
        stage.get('gpu_committed') is not True or stage.get('checkpoint_writes')!=1):
        raise ValueError('Actual optimizer/commit/save stages incomplete')
    return summary


def run(a):
    started=time.monotonic();a.output=a.output.resolve()
    for name in (*PATHS,'admission'):
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Disjoint inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    initial=dict(complete=False,requested_samples=32,accounted_samples=0,completed_gradient_samples=0,
                 optimizer_updates=None,checkpoint_writes=0,new_generation=False)
    train.dump(a.output/'summary.json',initial)
    probe.snapshot_rows(a.output,[dict(sample_id=probe.TASK+':sample'+str(i),status='unattempted') for i in range(4)])
    try:
        frozen=admit(a)
        if frozen!=json.loads(a.admission.read_bytes()):raise ValueError('Saved full CPU admission changed')
        train.dump(a.output/'admission.json',frozen)
        initial['accounted_samples']=32
        remaining=SECONDS-(time.monotonic()-started)
        if remaining<=CHECKPOINT_RESERVE:raise TimeoutError('No training budget remains')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']
        for name in (*PATHS,'output'):command+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
        command+=['--admission',str(a.output/'admission.json'),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);train.dump(a.output/'process.json',process)
        rc,_,_,timeout=as_runner_tuple(process)
        if rc!=0 or timeout:raise RuntimeError('Owned proof-reward training worker incomplete')
        summary=validate_output(a,frozen)
        if admit(a)!=frozen:raise ValueError('Final outer admission changed')
        elapsed=time.monotonic()-started
        if elapsed>SECONDS:raise TimeoutError('Total900-second training deadline exceeded')
        summary.update(total_seconds=elapsed,process_sha256=train.file_sha(a.output/'process.json'))
        train.dump(a.output/'summary.json',summary);return summary
    except BaseException as exc:
        failure=probe.scoring.failure_record(exc)
        try:
            rows=json.loads((a.output/'rows.json').read_bytes())
            if not isinstance(rows,list):raise ValueError('Malformed row ledger')
        except (ValueError,OSError) as error:
            rows=[];failure['ledger_error']=str(error)
        train.dump(a.output/'failure.json',failure)
        try:
            stage=json.loads((a.output/'stage.json').read_bytes())
            if not isinstance(stage,dict):raise ValueError('Malformed stage')
        except (ValueError,OSError):stage={}
        initial.update(completed_gradient_samples=sum(isinstance(r,dict) and r.get('status')=='complete' for r in rows),
            optimizer_updates=stage.get('optimizer_updates'),gpu_committed=stage.get('gpu_committed'),
            checkpoint_writes=stage.get('checkpoint_writes'),checkpoint_file_present=(a.output/'policy_optimizer.pt').exists(),
            accounted_gradient_samples=len(rows),last_stage=stage)
        train.dump(a.output/'summary.json',initial);raise


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('admit','run','worker'))
    for name in (*PATHS,'output'):parser.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    parser.add_argument('--admission',type=Path);parser.add_argument('--worker-seconds',type=float)
    a=parser.parse_args()
    if a.mode=='admit':
        with a.output.open('x') as stream:json.dump(admit(a),stream,indent=2);stream.write('\n')
    elif a.admission is None:parser.error('Full saved CPU admission required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
