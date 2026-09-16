"""Bounded TRAIN40 repair/retention SFT, immutable parent, fresh optimizer."""
import argparse
from collections import Counter
from contextlib import nullcontext
import json
import math
import os
from pathlib import Path
import random
import sys
import time

for _key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[_key]='4'
os.environ.update(HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',TOKENIZERS_PARALLELISM='false')
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_cuda_train as helpers
from tools import proof_cuda_broader_eval as common
from tools.proof_sumsequence_policy_eval import CHILD_SHA
from tools.proof_cuda_eval import digest
from harness.proof_owned_process import run_owned,as_runner_tuple

BUDGET=dict(rows=40,epochs=2,steps=80,seed=20261001,lr=1e-6,weight_decay=0.,clip=1.,
    seconds=900,checkpoint_reserve=90,max_tokens=8192,memory_limit=36*1024**3,cpu_threads=4)
ALGORITHM='response-only supervised reference repair and retention; fresh AdamW, not RL or full-state resume'
NAMES=('input_layernorm.weight','mlp.down_proj.weight','mlp.gate_proj.weight','mlp.up_proj.weight',
    'post_attention_layernorm.weight','self_attn.k_proj.weight','self_attn.o_proj.weight',
    'self_attn.q_proj.weight','self_attn.v_proj.weight')
EXPECTED_NAMES=tuple('model.layers.31.'+n for n in NAMES)
PARAMETERS=218112000
SOURCES=tuple(sorted(set(common.IMPLEMENTATION)|{
    'tools/proof_sumsequence_repair_train.py','tools/proof_sumsequence_repair_packet.py',
    'tools/proof_sumsequence_policy_eval.py','harness/proof_owned_process.py'}))


def schedule():
    rng=random.Random(BUDGET['seed']); result=[]
    for _ in range(2):
        epoch=list(range(40));rng.shuffle(epoch);result.extend(epoch)
    return result


def memory_guard(allocated,reserved):
    if any(type(v) is not int or v<=0 for v in (allocated,reserved)) or not allocated<=reserved<=BUDGET['memory_limit']:
        raise ValueError(f'36GiB allocated/reserved memory guard failed: allocated={allocated}, reserved={reserved}')


def gpu_memory():
    import torch
    value=dict(allocated=torch.cuda.max_memory_allocated(),reserved=torch.cuda.max_memory_reserved())
    memory_guard(**value);return value


def packet_rows(raw):
    from tools.proof_sumsequence_repair_packet import validate_training_packet
    packet=json.loads(raw);rows=validate_training_packet(packet)
    if len(rows)!=40 or packet['parent_checkpoint_sha256']!=CHILD_SHA:
        raise ValueError('Frozen TRAIN40 and actual current parent required')
    return rows


def admit(a):
    import torch
    import transformers
    torch.set_num_threads(4)
    raw=a.input.read_bytes();rows=packet_rows(raw)
    if helpers.sha(raw)!=a.expected_input_sha256 or helpers.file_sha(a.checkpoint)!=CHILD_SHA:
        raise ValueError('Exact prepared bytes and immutable parent required')
    files=helpers.model_files(a.model_path)
    if digest(files)!=common.MODEL_FILES_SHA or common.runtime_versions()!=common.FIRST_VERSIONS:
        raise ValueError('Pinned actual model/runtime required')
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
    encoded=[helpers.encode_row(tokenizer,row,8192) for row in rows]
    for row,e in zip(rows,encoded):
        actual=common.encode_prompt(tokenizer,row)
        if (actual['input_token_ids']!=e['input_ids'][:e['prompt_tokens']]
            or actual['rendered_prompt']!=e['rendered_prompt']):
            raise ValueError('Actual inference/training prefix mismatch')
    return dict(schema=1,budget=BUDGET,algorithm=ALGORITHM,dtype_profile=helpers.PROFILE,
        input_sha256=helpers.sha(raw),parent_checkpoint_sha256=CHILD_SHA,
        model_files=files,model_files_sha256=digest(files),versions=common.runtime_versions(),
        train_ids=[r['id'] for r in rows],schedule=schedule(),encodings=encoded,
        optimizer_initialization='fresh AdamW; parent optimizer/RNG deliberately not resumed',
        trainable_names=list(EXPECTED_NAMES),trainable_parameters=PARAMETERS,
        implementation_sha256={n:helpers.file_sha(ROOT/n) for n in SOURCES})


def gradients(selected):
    import torch
    norms={}
    for name,p in selected.items():
        if p.grad is None or not bool(torch.isfinite(p.grad).all()):
            raise ValueError('Every selected tensor requires a finite gradient: '+name)
        norms[name]=float(p.grad.detach().float().norm())
    if not any(norms.values()):raise ValueError('All gradients are zero')
    return norms


def forward_loss(net,e,device,context):
    import torch
    ids=torch.tensor([e['input_ids']],device=device)
    labels=torch.tensor([e['labels']],device=device)
    with context():
        result=net(input_ids=ids,attention_mask=torch.ones_like(ids),labels=labels,use_cache=False)
    if not bool(torch.isfinite(result.loss)):
        raise ValueError('Nonfinite response-only loss')
    return result


def preflight(net,selected,encoded,*,device,context,measure):
    """Actual longest schedule example, backward without constructing an optimizer."""
    import torch
    index=max(range(len(encoded)),key=lambda i:len(encoded[i]['input_ids']))
    initial={n:p.detach().cpu().clone() for n,p in selected.items()}
    net.zero_grad(set_to_none=True)
    result=forward_loss(net,encoded[index],device,context)
    probe=result.logits[0,-1].detach().float().cpu().clone()
    if not bool(torch.isfinite(probe).all()):raise ValueError('Nonfinite preflight logits')
    loss=result.loss;loss.backward(); norms=gradients(selected)
    value=dict(index=index,input_tokens=len(encoded[index]['input_ids']),loss=float(loss.detach()),
        gradient_norms=norms,optimizer_updates=0,memory=measure(),
        parameters_unchanged=all(torch.equal(p.detach().cpu(),initial[n]) for n,p in selected.items()),
        input_ids_sha256=digest(encoded[index]['input_ids']))
    del loss,result
    net.zero_grad(set_to_none=True)
    if not value['parameters_unchanged']:raise ValueError('Preflight changed parent parameters')
    return value,probe


def train_steps(net,selected,encoded,rows,*,deadline,emit,device='cuda',context=None,
                measure=gpu_memory,clock=time.monotonic,release=None):
    import torch
    context=context or (lambda:helpers.autocast(device))
    release=release or (lambda:helpers.release_unused_cache(device,True))
    optimizer=torch.optim.AdamW(selected.values(),lr=1e-6,weight_decay=0,foreach=False)
    metrics=[]
    for step,index in enumerate(schedule(),1):
        if clock()>=deadline:break
        optimizer.zero_grad(set_to_none=True)
        result=forward_loss(net,encoded[index],device,context)
        loss=result.loss;loss.backward(); per_tensor=gradients(selected)
        norm=torch.nn.utils.clip_grad_norm_(selected.values(),1.,error_if_nonfinite=True)
        before=measure()
        optimizer.step()
        if any(not bool(torch.isfinite(p).all()) for p in selected.values()):
            raise ValueError('Nonfinite trained parameter after optimizer update '+str(step))
        try:after=measure()
        except Exception as exc:
            raise RuntimeError('Memory guard after actual optimizer update '+str(step)+': '+str(exc)) from exc
        metric=dict(step=step,index=index,task=rows[index]['id'],loss=float(loss.detach()),
            gradient_norm=float(norm),gradient_norms=per_tensor,response_tokens=encoded[index]['response_tokens'],
            input_ids_sha256=digest(encoded[index]['input_ids']),memory_before_step=before,
            memory_after_step=after)
        del loss,result
        optimizer.zero_grad(set_to_none=True);release()
        metrics.append(metric);emit(metric)
    return optimizer,metrics


def validate_ledger(config,metrics):
    if config['budget']!=BUDGET or config['schedule']!=schedule() or len(config['train_ids'])!=40:
        raise ValueError('Immutable 40-row two-epoch schedule required')
    if len(metrics)!=80:
        raise ValueError('Exactly80 actual optimizer updates required')
    for step,(index,row) in enumerate(zip(schedule(),metrics),1):
        e=config['encodings'][index]
        if (row['step']!=step or row['index']!=index or row['task']!=config['train_ids'][index]
            or row['input_ids_sha256']!=digest(e['input_ids']) or row['response_tokens']!=e['response_tokens']
            or set(row['gradient_norms'])!=set(EXPECTED_NAMES)
            or any(not math.isfinite(v) or v<0 for v in row['gradient_norms'].values())
            or not any(row['gradient_norms'].values()) or not math.isfinite(row['loss'])
            or not math.isfinite(row['gradient_norm']) or row['gradient_norm']<=0):
            raise ValueError('Actual ordered finite-gradient update evidence required')
        memory_guard(**row['memory_before_step']);memory_guard(**row['memory_after_step'])
    if Counter(r['task'] for r in metrics)!=Counter({n:2 for n in config['train_ids']}):
        raise ValueError('Every TRAIN40 row requires exactly two updates')


def worker(a):
    import torch
    started=time.monotonic(); deadline=started+BUDGET['seconds']
    admission=json.loads(a.admission.read_bytes())
    if admit(a)!=admission:raise ValueError('Full worker admission mismatch')
    rows=packet_rows(a.input.read_bytes()); encoded=admission['encodings']
    random.seed(BUDGET['seed']);torch.manual_seed(BUDGET['seed']);torch.cuda.manual_seed_all(BUDGET['seed'])
    torch.backends.cuda.matmul.allow_tf32=False;torch.cuda.reset_peak_memory_stats()
    net=helpers.load_policy(a.model_path)
    parent=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    selected=helpers.restore_policy(net,parent,admission['model_files'])
    if (set(selected)!=set(EXPECTED_NAMES) or sum(p.numel() for p in selected.values())!=PARAMETERS
        or any(not torch.equal(p.detach().cpu(),parent['trainable_state'][n]) for n,p in selected.items())):
        raise ValueError('Exact nine-tensor 218112000-parameter parent restore required')
    initial={n:p.detach().cpu().clone() for n,p in selected.items()};del parent
    selected=helpers.select_final_layer(net,True)
    config=dict(admission,hardware=torch.cuda.get_device_name(),parent_restored_exactly=True,
        optimizer_parameter_names=list(selected),
        cuda_cache_policy='release_unused_after_each_optimizer_step')
    helpers.dump(a.output/'config.json',config)
    torch.save(dict(torch=torch.get_rng_state(),python=random.getstate(),cuda=torch.cuda.get_rng_state_all()),a.output/'rng_before.pt')
    probe,logits=preflight(net,selected,encoded,device='cuda',context=lambda:helpers.autocast('cuda'),measure=gpu_memory)
    helpers.dump(a.output/'preflight.json',probe);torch.save(logits,a.output/'preflight_logits.pt')
    helpers.release_unused_cache('cuda',True)
    if helpers.file_sha(a.checkpoint)!=CHILD_SHA or any(not torch.equal(p.detach().cpu(),initial[n]) for n,p in selected.items()):
        raise ValueError('Parent changed before first optimizer update')
    with (a.output/'steps.jsonl').open('x') as stream:
        def emit(row):
            stream.write(json.dumps(row)+'\n');stream.flush()
            helpers.dump(a.output/'progress.json',dict(complete=False,actual_updates=row['step'],requested_updates=80))
        optimizer,metrics=train_steps(net,selected,encoded,rows,deadline=deadline-90,emit=emit)
    # Short fixed probe avoids retaining another longest-sequence full-vocabulary
    # tensor during serialization. The actual longest gradient test is above.
    probe_ids=encoded[0]['input_ids'][:64]
    ids=torch.tensor([probe_ids],device='cuda')
    with torch.no_grad(),helpers.autocast('cuda'):
        before=net(input_ids=ids,use_cache=False).logits[:,-1].float().cpu().clone()
    result=helpers.save_reload(net,selected,optimizer,initial,config,metrics,probe_ids,a.output/'policy_optimizer.pt','cuda')
    with torch.no_grad(),helpers.autocast('cuda'):
        after=net(input_ids=ids,use_cache=False).logits[:,-1].float().cpu().clone()
    if not torch.equal(before,after) or not bool(torch.isfinite(after).all()) or result['parameter_delta_l2']<=0:
        raise ValueError('Actual changed child exact logit reload required')
    torch.save(dict(input_ids=probe_ids,before=before,after=after),a.output/'reload_logits.pt')
    memory=gpu_memory()
    stable=admit(a)==admission
    elapsed=time.monotonic()-started
    complete=len(metrics)==80 and elapsed<=900 and stable
    summary=dict(result,complete=complete,actual_updates=len(metrics),requested_updates=80,
        coverage=dict(Counter(r['task'] for r in metrics)),elapsed_seconds=elapsed,memory=memory,
        parent_checkpoint_sha256=CHILD_SHA,fresh_optimizer=True,full_state_resume=False,
        reload_logits_sha256=helpers.file_sha(a.output/'reload_logits.pt'),
        preflight_logits_sha256=helpers.file_sha(a.output/'preflight_logits.pt'),
        preflight_sha256=helpers.file_sha(a.output/'preflight.json'),
        rng_before_sha256=helpers.file_sha(a.output/'rng_before.pt'),
        steps_sha256=helpers.file_sha(a.output/'steps.jsonl'),identity_stable=stable,
        proof_success_claim=False,learning_improvement_claim=False)
    helpers.dump(a.output/'summary.json',summary)
    if not complete:raise RuntimeError('Incomplete bounded training; child is not admitted')
    validate_ledger(config,metrics)


def validate_training(output,admission,parent_path):
    import torch
    output=Path(output);summary=json.loads((output/'summary.json').read_bytes())
    config=json.loads((output/'config.json').read_bytes())
    if any(config.get(k)!=v for k,v in admission.items()) or not config.get('parent_restored_exactly'):
        raise ValueError('Actual admitted trainer configuration required')
    raw=(output/'train.json').read_bytes();rows=packet_rows(raw)
    if helpers.sha(raw)!=admission['input_sha256'] or [r['id'] for r in rows]!=config['train_ids']:
        raise ValueError('Saved exact supervised training packet required')
    if (summary.get('complete') is not True or summary.get('identity_stable') is not True
        or summary.get('actual_updates')!=80 or summary.get('parent_checkpoint_sha256')!=CHILD_SHA
        or helpers.file_sha(parent_path)!=CHILD_SHA or not 0<summary.get('elapsed_seconds',0)<=900
        or summary.get('fresh_optimizer') is not True or summary.get('full_state_resume') is not False):
        raise ValueError('Complete unchanged-parent 80-step result required')
    memory_guard(**summary['memory'])
    for name in ('steps','reload_logits','preflight_logits','rng_before'):
        path=output/(name+('.jsonl' if name=='steps' else '.pt'))
        if helpers.file_sha(path)!=summary[name+'_sha256']:raise ValueError('Raw training artifact changed')
    metrics=[json.loads(s) for s in (output/'steps.jsonl').read_text().splitlines()]
    validate_ledger(config,metrics)
    if summary.get('requested_updates')!=80 or summary.get('coverage')!=dict(Counter(r['task'] for r in metrics)):
        raise ValueError('Actual80 update full coverage summary required')
    saved=torch.load(output/'policy_optimizer.pt',map_location='cpu',weights_only=False)
    if helpers.file_sha(output/'policy_optimizer.pt')!=summary['checkpoint_sha256'] or saved['config']!=config or saved['metrics']!=metrics:
        raise ValueError('Exact child checkpoint provenance required')
    state=saved['trainable_state']
    if (set(state)!=set(EXPECTED_NAMES) or sum(v.numel() for v in state.values())!=PARAMETERS
        or any(v.dtype!=torch.float32 or not bool(torch.isfinite(v).all()) for v in state.values())):
        raise ValueError('Exact finite final nine-tensor state required')
    optimizer=saved['optimizer'];groups=optimizer['param_groups']
    if (len(groups)!=1 or groups[0]['lr']!=1e-6 or groups[0]['weight_decay']!=0
        or groups[0]['foreach'] is not False or len(optimizer['state'])!=9):
        raise ValueError('Frozen fresh AdamW configuration required')
    names=config['optimizer_parameter_names'];parameters=groups[0]['params']
    if (len(names)!=9 or set(names)!=set(state) or len(parameters)!=9 or len(set(parameters))!=9
        or set(parameters)!=set(optimizer['state']) or tuple(groups[0]['betas'])!=(.9,.999)
        or groups[0]['eps']!=1e-8 or groups[0]['amsgrad'] is not False or groups[0]['maximize'] is not False):
        raise ValueError('Exact optimizer parameter mapping/defaults required')
    for name,key in zip(names,parameters):
        item=optimizer['state'][key]
        if (item['step'].item()!=80 or any(item[k].shape!=state[name].shape or item[k].dtype!=torch.float32
            or not bool(torch.isfinite(item[k]).all()) for k in ('exp_avg','exp_avg_sq'))):
            raise ValueError('Every optimizer tensor requires80 finite updates')
    parent=torch.load(parent_path,map_location='cpu',weights_only=False)['trainable_state']
    delta=sum(float((state[n]-parent[n]).double().square().sum()) for n in state)**.5
    if delta<=0 or not math.isclose(delta,summary['parameter_delta_l2'],rel_tol=1e-12,abs_tol=1e-12):
        raise ValueError('Actual parent-child tensor delta mismatch')
    probe=torch.load(output/'reload_logits.pt',map_location='cpu',weights_only=True)
    if (probe['input_ids']!=config['encodings'][0]['input_ids'][:64]
        or not torch.equal(probe['before'],probe['after']) or not bool(torch.isfinite(probe['after']).all())
        or summary.get('reload_tensors_exact') is not True or summary.get('reload_logits_exact') is not True):
        raise ValueError('Exact raw checkpoint logit reload required')
    preflight=json.loads((output/'preflight.json').read_bytes())
    if helpers.file_sha(output/'preflight.json')!=summary['preflight_sha256']:
        raise ValueError('Raw preflight changed')
    longest=max(range(40),key=lambda i:len(config['encodings'][i]['input_ids']))
    if (preflight['index']!=longest or preflight['optimizer_updates']!=0 or preflight['parameters_unchanged'] is not True
        or set(preflight['gradient_norms'])!=set(EXPECTED_NAMES)
        or any(not math.isfinite(v) or v<0 for v in preflight['gradient_norms'].values())
        or not any(preflight['gradient_norms'].values()) or not math.isfinite(preflight['loss'])
        or preflight['input_tokens']!=len(config['encodings'][longest]['input_ids'])
        or preflight['input_ids_sha256']!=digest(config['encodings'][longest]['input_ids'])):
        raise ValueError('Actual longest-input finite-gradient preflight required')
    memory_guard(**preflight['memory'])
    preflight_logits=torch.load(output/'preflight_logits.pt',map_location='cpu',weights_only=True)
    if preflight_logits.ndim!=1 or not preflight_logits.numel() or not bool(torch.isfinite(preflight_logits).all()):
        raise ValueError('Actual finite longest-input logits required')
    before_rng=torch.load(output/'rng_before.pt',map_location='cpu',weights_only=False)
    if (before_rng['torch'].dtype!=torch.uint8 or not before_rng['cuda']
        or any(v.dtype!=torch.uint8 or not v.numel() for v in before_rng['cuda'])):
        raise ValueError('Initial torch/CUDA RNG state required')
    random.Random().setstate(before_rng['python'])
    for rng in (saved,):
        if (rng['torch_rng_state'].dtype!=torch.uint8 or not rng['cuda_rng_state']
            or any(v.dtype!=torch.uint8 or not v.numel() for v in rng['cuda_rng_state'])):
            raise ValueError('Complete saved torch/CUDA RNG state required')
        random.Random().setstate(rng['python_rng_state'])
    return summary


def supervise(a):
    admission=admit(a)
    if admission!=json.loads(a.admission.read_bytes()):raise ValueError('Saved full portable admission mismatch')
    a.output=a.output.resolve()
    for path in (a.input,a.checkpoint,a.model_path,a.admission):
        path=path.resolve()
        if a.output==path or a.output in path.parents or path in a.output.parents:
            raise ValueError('Output must be disjoint from immutable inputs')
    a.output.mkdir(parents=True,exist_ok=False)
    helpers.dump(a.output/'admission.json',admission)
    with (a.output/'train.json').open('xb') as stream:stream.write(a.input.read_bytes())
    helpers.dump(a.output/'summary.json',dict(complete=False,actual_updates=0,requested_updates=80))
    command=[sys.executable,str(Path(__file__).resolve()),'worker']
    for name in ('input','model_path','checkpoint','output'):
        command+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
    command+=['--expected-input-sha256',a.expected_input_sha256,'--admission',str(a.output/'admission.json')]
    process=run_owned(command,ROOT,900);helpers.dump(a.output/'process.json',process)
    rc,_,_,timeout=as_runner_tuple(process)
    if rc!=0 or timeout:raise RuntimeError('Owned training worker incomplete; no child admission')
    if admit(a)!=admission:raise ValueError('Post-training source/model/packet/parent drift')
    summary=validate_training(a.output,admission,a.checkpoint)
    helpers.dump(a.output/'admitted.json',dict(complete=True,summary_sha256=helpers.file_sha(a.output/'summary.json'),
        process_sha256=helpers.file_sha(a.output/'process.json')))
    return summary


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','train','worker','validate'))
    for name in ('input','model-path','checkpoint','output'):
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--expected-input-sha256',required=True);p.add_argument('--admission',type=Path)
    a=p.parse_args()
    if a.mode=='admit':
        with a.output.open('x') as stream:json.dump(admit(a),stream,indent=2);stream.write('\n')
    elif a.admission is None:p.error('Saved full admission required')
    elif a.mode=='validate':validate_training(a.output,json.loads(a.admission.read_bytes()),a.checkpoint)
    else:globals()['supervise' if a.mode=='train' else 'worker'](a)


if __name__=='__main__':main()
