"""Bounded one-example TRAIN-only full-module memorization discriminator."""
import argparse, json, math, random, sys, time
from contextlib import nullcontext
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_sany_checks as sany

ROW_INDEX=44; TASK_ID='w4-fullmodule:w4opus::d0-m0-p1-t0'
INPUT_SHA='a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
RESPONSE_SHA='1014e9b256c188e24ba4374d5125099d0af0475df5883896bdb41ca683bc7f94'
PROMPT_SHA='edf78ead117f730819e6ee1b6b7058b01c648f3e6983f688f7ec5bbd0c7eceea'
POLICY_SHA='fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d'
BUDGET=dict(updates=128,lr=1e-5,seed=20261011,max_new_tokens=256,item_seconds=45,
    sany_seconds=30,train_only=True,gate_claim=False,generalization_claim=False,proof_claim=False)
SOURCES=tuple(sorted(set(lineage.SOURCES)|set(sany.SOURCES)|{'tools/proof_fullmodule_one_example_probe.py'}))

def load(path): return json.loads(Path(path).read_bytes())
def dump(path,value): lineage.helpers.dump(Path(path),value)
def sources(): return {n:lineage.helpers.file_sha(ROOT/n) for n in SOURCES}

def selected(raw):
    if lineage.helpers.sha(raw)!=INPUT_SHA: raise ValueError('Exact immutable TRAIN169 packet required')
    value=json.loads(raw); rows=lineage.packet.validate_training_packet(value); row=rows[ROW_INDEX]; enc=value['encodings'][ROW_INDEX]
    if (row['id'],row['split'],row['response_sha256'],row['prompt_sha256']) != (TASK_ID,'train',RESPONSE_SHA,PROMPT_SHA):
        raise ValueError('Pinned shortest TRAIN row changed')
    if enc['response_tokens']!=139 or enc['prompt_tokens']!=385 or len(enc['input_ids'])!=524: raise ValueError('Pinned tokenization changed')
    return row,enc,value

def checker_task(value,row):
    candidates=json.loads(value['audit_rows_bytes']); target=next((x for x in candidates if x['id']=='w4opus::d0-m0-p1-t0'),None)
    if not target or target['exclusions']['status']!='lexically_clear': raise ValueError('Pinned TRAIN source missing or blocked')
    raw=target['raw']; text=raw['spec_text']
    if lineage.helpers.sha(text.encode())!=RESPONSE_SHA or raw['module']!='W4Od0m0p1t0': raise ValueError('Pinned reference source changed')
    # Paths are populated only in the new append-only run output by stage_task.
    return dict(id=target['id'],index=target['index'],module_name=raw['module'],dependencies={},
        source_text=text,description_text=raw['nl'],config_text=raw['cfg_text'])

def stage_task(task,output):
    root=Path(output)/'reference';root.mkdir(parents=True,exist_ok=False)
    paths={}
    for key,name,text in (('source','W4Od0m0p1t0.tla',task['source_text']),('description','description.txt',task['description_text']),('config','configuration.cfg',task['config_text'])):
        path=root/name;path.write_text(text);paths[key]=dict(path=str(path),sha256=lineage.helpers.sha(text.encode()))
    return dict(id=task['id'],index=task['index'],module_name=task['module_name'],dependencies={},**paths)

def output_fields(tokens,reply,elapsed):
    eos=set(lineage.common.EOS_IDS); tokens=list(tokens)
    if not all(type(x) is int and 0<=x<128256 for x in tokens): raise ValueError('Invalid generated token IDs')
    finish='eos' if tokens and tokens[-1] in eos and elapsed<=BUDGET['item_seconds'] else 'token_limit' if len(tokens)>=BUDGET['max_new_tokens'] else 'time_limit'
    return dict(token_ids=tokens,raw_reply=reply,raw_reply_sha256=lineage.helpers.sha(reply.encode()),output_tokens=len(tokens),
        finish_reason=finish,deadline_exceeded=elapsed>BUDGET['item_seconds'],elapsed_seconds=elapsed)

def validate_pins(lineage_checkpoint, checkpoint, *, file_hash=lineage.helpers.file_sha):
    if file_hash(lineage_checkpoint)!=lineage.CHILD_SHA: raise ValueError('Exact immutable8866 lineage checkpoint required')
    if file_hash(checkpoint)!=POLICY_SHA: raise ValueError('Exact fba starting policy required')

def decode(net,tokenizer,enc,device='cuda',clock=time.monotonic):
    import torch
    ids=torch.tensor([enc['input_ids'][:enc['prompt_tokens']]],device=device);started=clock()
    with torch.inference_mode(),lineage.helpers.autocast(device):
        result=net.generate(input_ids=ids,attention_mask=torch.ones_like(ids),do_sample=False,num_beams=1,num_return_sequences=1,
            max_new_tokens=BUDGET['max_new_tokens'],max_time=BUDGET['item_seconds'],pad_token_id=tokenizer.pad_token_id or tokenizer.eos_token_id)
    if device=='cuda': torch.cuda.synchronize()
    elapsed=clock()-started; tokens=lineage.common.trim_output(result[0,ids.shape[1]:].tolist(),set(lineage.common.EOS_IDS))
    return output_fields(tokens,lineage.common.decode_reply(tokenizer,tokens),elapsed)

def teacher(net,enc,device='cuda',context=None):
    import torch
    context=context or (lambda:lineage.helpers.autocast(device)); ids=torch.tensor([enc['input_ids']],device=device); labels=torch.tensor([enc['labels']],device=device)
    with context(): result=net(input_ids=ids,attention_mask=torch.ones_like(ids),labels=labels,use_cache=False)
    target=labels[:,1:]; predicted=result.logits[:,:-1].argmax(-1); mask=target.ne(-100)
    return result,dict(loss=float(result.loss.detach()),target_top1=float((predicted[mask]==target[mask]).float().mean().detach()))

def update(net,selected,enc,device='cuda',context=None,measure=lambda _:None):
    import torch
    context=context or (lambda:lineage.helpers.autocast(device)); opt=torch.optim.AdamW(selected.values(),lr=BUDGET['lr'],weight_decay=0.,foreach=False); rows=[]
    for step in range(1,BUDGET['updates']+1):
        opt.zero_grad(set_to_none=True); result,metric=teacher(net,enc,device,context);result.loss.backward(); norms=lineage.gradients(selected)
        grad=float(torch.nn.utils.clip_grad_norm_(selected.values(),1.,error_if_nonfinite=True));opt.step(); measure('after_step_'+str(step))
        if not math.isfinite(metric['loss']) or not math.isfinite(grad) or not any(norms.values()): raise ValueError('Nonfinite/zero training evidence')
        rows.append(dict(step=step,loss=metric['loss'],target_top1=metric['target_top1'],gradient_norm=grad,gradient_norms=norms));del result
    return opt,rows

def admit(a):
    raw=a.input.read_bytes();row,enc,value=selected(raw)
    # Reuse the existing full lineage admission; it authenticates model/runtime/parent/training inputs.
    values={n:getattr(a,n) for n in (*lineage.PATHS,'expected_input_sha256')}
    values['checkpoint']=a.lineage_checkpoint
    args=type('A',(),values)()
    base=lineage.admit(args)
    if a.expected_input_sha256!=INPUT_SHA or base['input_sha256']!=INPUT_SHA: raise ValueError('Exact TRAIN lineage required')
    validate_pins(a.lineage_checkpoint,a.checkpoint)
    return dict(schema=1,kind='one_example_train_only_fullmodule_probe',budget=BUDGET,row=row,encoding=enc,
        checker_task=checker_task(value,row),lineage_admission_sha256=lineage.helpers.sha(json.dumps(base,sort_keys=True).encode()),
        input_sha256=INPUT_SHA,lineage_checkpoint_sha256=lineage.CHILD_SHA,policy_checkpoint_sha256=POLICY_SHA,
        source_sha256=sources(),training_authorized=True,protected_outputs_never_train=True,
        train_only=True,gate_claim=False,generalization_claim=False,proof_claim=False)

def worker(a):
    import torch, transformers
    frozen=load(a.admission)
    if admit(a)!=frozen: raise ValueError('Admission drift')
    out=a.output; out.mkdir(parents=True,exist_ok=False); dump(out/'admission.json',frozen); task=stage_task(frozen['checker_task'],out); current=sany.identity([task])
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True); net=lineage.helpers.load_policy(a.model_path)
    parent=torch.load(a.checkpoint,map_location='cpu',weights_only=False); selected_t=lineage.helpers.restore_policy(net,parent,lineage.helpers.model_files(a.model_path)); initial={n:p.detach().cpu().clone() for n,p in selected_t.items()}; del parent
    selected_t=lineage.helpers.select_final_layer(net,True); enc=frozen['encoding']; before_result,before_teacher=teacher(net,enc); del before_result
    pre=decode(net,tokenizer,enc); opt,steps=update(net,selected_t,enc,measure=lambda _:None); after_result,after_teacher=teacher(net,enc);del after_result
    post=decode(net,tokenizer,enc); config=dict(frozen,model_files=lineage.helpers.model_files(a.model_path),dtype_profile=lineage.helpers.PROFILE)
    saved=lineage.helpers.save_reload(net,selected_t,opt,initial,config,steps,enc['input_ids'][:64],out/'policy_optimizer.pt','cuda')
    reference=sany.check(task,frozen['row']['response'],out/'sany_reference',current,timeout=BUDGET['sany_seconds']); candidate=sany.check(task,post['raw_reply'],out/'sany_candidate',current,timeout=BUDGET['sany_seconds']) if post['finish_reason']=='eos' else None
    delta=sum(float((p.detach().cpu()-initial[n]).double().square().sum()) for n,p in selected_t.items())**.5
    receipt=dict(complete=True,updates=128,parameter_delta_l2=delta,reload=saved,before_teacher=before_teacher,after_teacher=after_teacher,
        pre=pre,post=post,reference=reference,candidate=candidate,reference_sany_pass=reference['sany']==1,
        candidate_sany_pass=bool(candidate and candidate['sany']==1),train_only=True,gate_claim=False,generalization_claim=False,proof_claim=False)
    dump(out/'steps.json',steps);dump(out/'receipt.json',receipt); return receipt

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('admit','worker'))
    for n in (*lineage.PATHS,'output'):p.add_argument('--'+n.replace('_','-'),type=Path,required=True)
    p.add_argument('--lineage-checkpoint',type=Path,required=True)
    p.add_argument('--expected-input-sha256',required=True);p.add_argument('--admission',type=Path);a=p.parse_args()
    if a.mode=='admit':
        if a.output.exists():raise ValueError('Admission output must not exist')
        dump(a.output,admit(a))
    else:
        if a.admission is None:p.error('--admission required')
        print(json.dumps(worker(a)))
if __name__=='__main__':main()
