"""Single-variable native expandable allocator probe; no optimizer or gate change."""
import argparse
from contextlib import nullcontext
import json
import math
import os
from pathlib import Path
import sys
import time

ALLOCATOR_CONF='backend:native,expandable_segments:True'
TORCH_PREIMPORTED='torch' in sys.modules


def configure_allocator():
    for name in ('PYTORCH_CUDA_ALLOC_CONF','PYTORCH_NO_CUDA_MEMORY_CACHING'):
        if os.environ.get(name):raise ValueError('Conflicting allocator alias/cache override: '+name)
    current=os.environ.get('PYTORCH_ALLOC_CONF')
    if current not in (None,ALLOCATOR_CONF):raise ValueError('Only exact native expandable allocator configuration permitted')
    os.environ['PYTORCH_ALLOC_CONF']=ALLOCATOR_CONF


configure_allocator()  # Must precede the numerical-library dependency graph.
for _key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[_key]='4'
os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_stochastic_eval as inference
from tools import proof_token_rl_worker as scoring
from tools import proof_cuda_train as train
from tools.proof_token_rl_packet import digest,sha,EOS_IDS
from tools.proof_token_rl_cached_score import cached_token_logps
from harness.proof_owned_process import run_owned,as_runner_tuple

TASK='breadth-Barriers-LockExclusion'
PINS=dict(rollouts='ff6b385bfb2ad9c7c43b8ca9472419eeba8e82b008563ebe94b80cb5e51a16bf',
    verified_rows='5899398b30a06cb9f925e520283afd4fb71f76ff46d163d389f6046234349f79',
    verified_summary='095090c62dbc4e14ccf0109e27f52e9aa310e7a072c747fee261d77034d45643',
    rng_before='029138c1853c890a66f0eeabd019b62aceecac1f02ce0f866f53b3342b6b4d0c',
    rng_after='9b2c50897b6a759d58230706c47f6551d2ccedad3d7d46d9d7e9c9da0c6839fb')
PATHS=('broader_prompts','rollouts','inference_admission','model_path','checkpoint',
    'verified_rows','verified_summary','rng_before','rng_after')
SOURCES=tuple(sorted(set(inference.SOURCES+scoring.SOURCES)|{
    'tools/proof_sumsequence_expandable_probe.py','tools/proof_sumsequence_expandable_probe.pbs'}))
BUDGET=dict(seconds=900,requested_samples=4,full_rollouts_accounted=32,
    memory_limit=36*1024**3,max_context=8192,max_logprob_error=.03,mean_logprob_error=.003,
    optimizer_updates=0,checkpoint_writes=0,new_generation=False,
    method='cached_grad exact full response including actual EOS; summed logprob backward; causal KV retained; shared fresh outer autocast per response')
BUDGET['allocator']=ALLOCATOR_CONF
GRADIENT_ELEMENTS={'model.layers.31.'+name:count for name,count in {
    'input_layernorm.weight':4096,'post_attention_layernorm.weight':4096,
    'mlp.down_proj.weight':58720256,'mlp.gate_proj.weight':58720256,'mlp.up_proj.weight':58720256,
    'self_attn.k_proj.weight':4194304,'self_attn.v_proj.weight':4194304,
    'self_attn.q_proj.weight':16777216,'self_attn.o_proj.weight':16777216}.items()}


def snapshot_rows(output,rows):
    pending=output/'rows.pending'
    train.dump(pending,rows);pending.replace(output/'rows.json')


def validate_results(original,results):
    import torch
    if len(results)!=4 or [r['sample_id'] for r in results]!=[r['sample_id'] for r in original]:
        raise ValueError('All four ordered raw gradient results required')
    for row,result in zip(original,results):
        parity=scoring.check_logps(torch.tensor(result['actual_token_logprobs'],dtype=torch.float32),row['selected_token_logprobs'])
        gpu=result['parity_gpu']
        # Both independently retain .03/.003 admission. Only cross-device mean
        # reduction comparison permits tiny summation-order differences; maxima,
        # indices, limits and worst-token values remain exact.
        if (set(gpu)!=set(parity) or gpu['max_abs']>.03 or gpu['mean_abs']>.003
            or any(gpu[k]!=v for k,v in parity.items() if k!='mean_abs')
            or not math.isclose(gpu['mean_abs'],parity['mean_abs'],rel_tol=1e-6,abs_tol=1e-8)):
            raise ValueError('Actual GPU parity evidence differs from canonical CPU audit')
        if (result['status']!='complete' or result['parity']!=parity or result['optimizer_updates']!=0
            or result['input_tokens']!=len(row['input_token_ids']) or result['output_tokens']!=len(row['token_ids'])
            or set(result['gradients'])!=set(GRADIENT_ELEMENTS)):
            raise ValueError('Actual matching exact-token gradient result required')
        for name,entry in result['gradients'].items():
            if (entry['dtype']!='torch.float32' or entry['elements']!=GRADIENT_ELEMENTS[name]
                or type(entry['norm']) not in (int,float) or not math.isfinite(entry['norm']) or entry['norm']<0):
                raise ValueError('Finite exact FP32 gradient shape/norm required')
        if not any(v['norm']>0 for v in result['gradients'].values()):
            raise ValueError('Nonzero aggregate gradient required')
        for key in ('memory_after_forward','memory_after_backward'):
            values=result[key]
            if not 0<values['allocated']<=values['reserved']<=36*1024**3:
                raise ValueError('Recorded36GiB gradient memory guard required')
            evidence=result[key.replace('memory_','allocator_')]
            if guard_allocator(evidence)!=values:
                raise ValueError('Raw allocator snapshot and peak memory differ')


def select_rows(rows):
    if len(rows)!=32:raise ValueError('All32 original samples required')
    selected=[r for r in rows if r['task_id']==TASK]
    if ([r['sample_id'] for r in selected]!=[TASK+':sample'+str(i) for i in range(4)]
        or [len(r['input_token_ids']) for r in selected]!=[3432]*4
        or [len(r['token_ids']) for r in selected]!=[777,712,268,319]
        or any(r['finish_reason']!='eos' for r in selected)):
        raise ValueError('Exact ordered original Barriers4 full EOS responses required')
    longest=max((r for r in rows if r.get('finish_reason')=='eos'),
        key=lambda r:len(r['input_token_ids'])+len(r['token_ids']))
    if longest['sample_id']!=selected[0]['sample_id']:
        raise ValueError('Longest EOS sequence across original32 must be included')
    return selected


def admit(a):
    configure_allocator()
    if TORCH_PREIMPORTED:raise ValueError('Full production admission must import this allocator module before torch')
    import torch
    import transformers
    for name,pin in PINS.items():
        if train.file_sha(getattr(a,name))!=pin:raise ValueError('Exact original artifact required: '+name)
    source_args=argparse.Namespace(broader_prompts=a.broader_prompts,model_path=a.model_path,
        checkpoint=a.checkpoint,arm='child',output=a.output)
    current=inference.admit(source_args)
    original=json.loads(a.inference_admission.read_bytes())
    if current!=original:raise ValueError('Full original child inference admission changed')
    rows=[json.loads(s) for s in a.rollouts.read_bytes().splitlines()]
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    inference.validate_rows(original,rows,tokenizer)
    selected=select_rows(rows)
    for name in ('rng_before','rng_after'):
        value=torch.load(getattr(a,name),map_location='cpu',weights_only=True)
        if value.dtype!=torch.uint8 or value.ndim!=1 or not value.numel():
            raise ValueError('Original exact sampling RNG byte state required')
    return dict(schema=1,budget=BUDGET,inference_admission=original,
        allocator_environment=dict(PYTORCH_ALLOC_CONF=ALLOCATOR_CONF,configured_before_torch_import=True,
            backward_compat_alias_absent=True,no_cache_override_absent=True),
        original_artifacts={name:train.file_sha(getattr(a,name)) for name in PATHS if name!='model_path'},
        selected_sample_ids=[r['sample_id'] for r in selected],selected_rows_sha256=digest(selected),
        implementation_sha256={n:train.file_sha(ROOT/n) for n in SOURCES},
        selection_provenance='Frozen verified64 artifact hashes supplied after independent local audit; no reward labels exported, no training authorization',
        training_authorized=False,reward_export=False,proof_success_claim=False)


def allocator_evidence(torch_module=None):
    """Read compact actual runtime evidence without applying any pass/fail guard."""
    if torch_module is None:
        import torch as torch_module
    cuda=torch_module.cuda;record={}
    try:
        record['memory']=dict(allocated=cuda.max_memory_allocated(),reserved=cuda.max_memory_reserved())
        record['backend']=cuda.memory.get_allocator_backend()
        snapshot=cuda.memory._snapshot()
        record['settings']=snapshot.get('allocator_settings')
        keys=('device','address','total_size','allocated_size','active_size','is_expandable','segment_type','stream')
        record['segments']=[{k:s[k] for k in keys if k in s} for s in snapshot.get('segments',[])]
        stats=cuda.memory_stats()
        record['memory_stats']={k:v for k,v in stats.items() if k in ('num_alloc_retries','num_ooms')
            or any(k.startswith(prefix+'.') for prefix in ('allocated_bytes','reserved_bytes','active_bytes','inactive_split_bytes','requested_bytes'))}
    except Exception as exc:
        record['capture_error']=type(exc).__name__+': '+str(exc)
    return record


def guard_allocator(record):
    settings=record.get('settings')
    if (record.get('capture_error') or record.get('backend')!='native' or not isinstance(settings,dict)
        or settings.get('expandable_segments') is not True
        # PyTorch2.11's snapshot retains the legacy metadata key even when the
        # process is configured exclusively via PYTORCH_ALLOC_CONF.
        or settings.get('PYTORCH_CUDA_ALLOC_CONF')!=ALLOCATOR_CONF
        or not any(s.get('is_expandable') is True and s.get('total_size',0)>0 for s in record.get('segments',[]))):
        raise ValueError('Actual native expandable allocator not established by runtime snapshot')
    value=record['memory']
    if not 0<value['allocated']<=value['reserved']<=36*1024**3:
        raise ValueError('Unchanged36GiB memory guard: '+str(value))
    return value


def probe_one(net,selected,row,*,seconds,device='cuda',context=nullcontext,capture=allocator_evidence,emit=lambda r:None):
    import torch
    net.zero_grad(set_to_none=True)
    report=dict(sample_id=row['sample_id'],status='scoring',input_tokens=len(row['input_token_ids']),
        output_tokens=len(row['token_ids']),optimizer_updates=0)
    emit(report)
    values=None
    try:
        values=cached_token_logps(net,torch.tensor(row['input_token_ids'],dtype=torch.long,device=device),
            torch.tensor(row['token_ids'],dtype=torch.long,device=device),eos_token_ids=EOS_IDS,
            seconds=seconds,context_factory=context)
        report.update(actual_token_logprobs=values.detach().cpu().tolist())
        emit(report)
        report['allocator_after_forward']=capture()
        emit(report)
        report['memory_after_forward']=guard_allocator(report['allocator_after_forward'])
        emit(report)
        report['parity_gpu']=scoring.check_logps(values,row['selected_token_logprobs']);emit(report)
        report['parity']=scoring.check_logps(values.detach().cpu(),row['selected_token_logprobs']);emit(report)
        values.sum().backward()
        gradients={}
        for name,p in selected.items():
            if p.dtype!=torch.float32 or p.grad is None or p.grad.dtype!=torch.float32 or not bool(torch.isfinite(p.grad).all()):
                raise ValueError('Every selected FP32 tensor requires finite gradient: '+name)
            gradients[name]=dict(norm=float(p.grad.norm()),dtype=str(p.grad.dtype),elements=p.grad.numel())
        if any(not math.isfinite(v['norm']) for v in gradients.values()) or not any(v['norm']>0 for v in gradients.values()):
            raise ValueError('Finite nonzero aggregate gradient norm required')
        report['gradients']=gradients;emit(report)
        report['allocator_after_backward']=capture();emit(report)
        report['memory_after_backward']=guard_allocator(report['allocator_after_backward'])
        report['status']='complete'
        emit(report);return report
    except BaseException as exc:
        report.update(status='failed',failure=scoring.failure_record(exc))
        report['allocator_at_failure']=capture();emit(report);raise
    finally:
        del values
        net.zero_grad(set_to_none=True)


def worker(a):
    import torch
    started=time.monotonic();frozen=json.loads(a.admission.read_bytes())
    if not 30<a.worker_seconds<=900 or admit(a)!=frozen:
        raise ValueError('Frozen full probe admission and remaining900-second budget required')
    rows=select_rows([json.loads(s) for s in a.rollouts.read_bytes().splitlines()])
    torch.manual_seed(20261002);torch.cuda.manual_seed_all(20261002);torch.backends.cuda.matmul.allow_tf32=False
    torch.cuda.reset_peak_memory_stats();net=train.load_policy(a.model_path)
    allocator=allocator_evidence();train.dump(a.output/'allocator_after_load.json',allocator)
    guard_allocator(allocator)
    train.dump(a.output/'hardware.json',dict(device=torch.cuda.get_device_name(),
        capability=list(torch.cuda.get_device_capability()),cuda_device=torch.cuda.current_device(),
        torch_version=torch.__version__,cpu_threads=torch.get_num_threads()))
    saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    selected=train.restore_policy(net,saved,frozen['inference_admission']['model_files'])
    initial={n:v.clone() for n,v in saved['trainable_state'].items()};del saved
    scoring.assert_parent_unchanged(selected,initial)
    selected=train.select_final_layer(net,True)
    if set(selected)!=inference.NAMES or sum(p.numel() for p in selected.values())!=218112000:
        raise ValueError('Exact nine layer31 FP32 tensors required')
    results=[dict(sample_id=r['sample_id'],status='unattempted') for r in rows]
    snapshot_rows(a.output,results)
    with (a.output/'events.jsonl').open('x') as stream:
        for i,row in enumerate(rows):
            remaining=a.worker_seconds-(time.monotonic()-started)-30
            if remaining<=0:raise TimeoutError('No scoring budget before final identity reserve')
            def emit(value):
                results[i]=dict(value);snapshot_rows(a.output,results)
                stream.write(json.dumps(value)+'\n');stream.flush()
            probe_one(net,selected,row,seconds=remaining,context=lambda:train.autocast('cuda'),emit=emit)
            scoring.assert_parent_unchanged(selected,initial)
    scoring.assert_parent_unchanged(selected,initial)
    stable=admit(a)==frozen;elapsed=time.monotonic()-started
    summary=dict(complete=stable and elapsed<=a.worker_seconds,requested_samples=4,accounted_samples=4,
        completed_samples=sum(r['status']=='complete' for r in results),full_rollouts_accounted=32,
        parent_unchanged=True,identity_stable=stable,optimizer_updates=0,checkpoint_writes=0,
        new_generation=False,elapsed_seconds=elapsed,rows_sha256=train.file_sha(a.output/'rows.json'),
        proof_success_claim=False,training_authorized=False,reward_export=False,
        scope='No allocator cache release between responses; isolated gradients are cleared, so this is not accumulated-gradient or optimizer-state memory admission')
    final_allocator=allocator_evidence();train.dump(a.output/'allocator_final.json',final_allocator)
    summary['memory']=guard_allocator(final_allocator)
    summary['allocator_final_sha256']=train.file_sha(a.output/'allocator_final.json')
    train.dump(a.output/'worker_summary.json',summary)
    if not summary['complete']:raise RuntimeError('Probe incomplete; no numerical feasibility admission')


def run(a):
    started=time.monotonic();a.output=a.output.resolve()
    for name in (*PATHS,'admission'):
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:
            raise ValueError('Disjoint immutable inputs and output required')
    a.output.mkdir(parents=True,exist_ok=False)
    train.dump(a.output/'summary.json',dict(complete=False,requested_samples=4,completed_samples=0,
        optimizer_updates=0,checkpoint_writes=0))
    snapshot_rows(a.output,[dict(sample_id=TASK+':sample'+str(i),status='unattempted') for i in range(4)])
    try:
        frozen=admit(a)
        if frozen!=json.loads(a.admission.read_bytes()):raise ValueError('Saved actual CPU admission changed')
        train.dump(a.output/'admission.json',frozen)
        remaining=900-(time.monotonic()-started)
        if remaining<=30:raise TimeoutError('No worker budget remains')
        command=[sys.executable,str(Path(__file__).resolve()),'worker']
        for name in (*PATHS,'output'):command+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
        command+=['--admission',str(a.output/'admission.json'),'--worker-seconds',str(remaining)]
        process=run_owned(command,ROOT,remaining);train.dump(a.output/'process.json',process)
        rc,_,_,timeout=as_runner_tuple(process)
        if rc!=0 or timeout:raise RuntimeError('Owned no-update worker incomplete')
        summary=json.loads((a.output/'worker_summary.json').read_bytes())
        rows=json.loads((a.output/'rows.json').read_bytes())
        original=select_rows([json.loads(s) for s in a.rollouts.read_bytes().splitlines()])
        validate_results(original,rows)
        final_allocator=json.loads((a.output/'allocator_final.json').read_bytes())
        if (guard_allocator(final_allocator)!=summary['memory']
            or summary['allocator_final_sha256']!=train.file_sha(a.output/'allocator_final.json')):
            raise ValueError('Actual final native expandable allocator evidence required')
        if (not summary['complete'] or summary['completed_samples']!=4 or summary['parent_unchanged'] is not True
            or summary['identity_stable'] is not True or summary['optimizer_updates']!=0
            or summary['checkpoint_writes']!=0 or summary['new_generation'] is not False
            or summary['rows_sha256']!=train.file_sha(a.output/'rows.json')):
            raise ValueError('Complete raw four-sample gradient evidence required')
        elapsed=time.monotonic()-started
        if elapsed>900:raise TimeoutError('900-second total probe deadline exceeded')
        summary.update(total_seconds=elapsed,process_sha256=train.file_sha(a.output/'process.json'))
        train.dump(a.output/'summary.json',summary);return summary
    except BaseException as exc:
        failure=scoring.failure_record(exc)
        try:
            rows=json.loads((a.output/'rows.json').read_bytes())
            if not isinstance(rows,list):raise ValueError('Expected result row list')
        except (ValueError,OSError) as ledger_error:
            rows=[];failure['ledger_error']=type(ledger_error).__name__+': '+str(ledger_error)
        train.dump(a.output/'failure.json',failure)
        train.dump(a.output/'summary.json',dict(complete=False,requested_samples=4,
            completed_samples=sum(isinstance(r,dict) and r.get('status')=='complete' for r in rows),accounted_samples=len(rows),
            optimizer_updates=0,checkpoint_writes=0,new_generation=False))
        raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','run','worker'))
    for name in (*PATHS,'output'):p.add_argument('--'+name.replace('_','-'),type=Path,required=True)
    p.add_argument('--admission',type=Path);p.add_argument('--worker-seconds',type=float)
    a=p.parse_args()
    if a.mode=='admit':
        with a.output.open('x') as stream:json.dump(admit(a),stream,indent=2);stream.write('\n')
    elif a.admission is None:p.error('Saved full CPU admission required')
    else:globals()[a.mode](a)


if __name__=='__main__':main()
