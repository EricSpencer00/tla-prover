"""Bounded DDP LoRA SFT for immutable full-module TLA+ rows.

The target is rendered in GPT-OSS harmony's FINAL channel.  Loss is masked on
the user prefix, so the optimizer learns serialized modules rather than the
prompt or hidden reference metadata.
"""
import argparse, hashlib, json, os, random, time
from pathlib import Path

def sha(data): return hashlib.sha256(data).hexdigest()

def harmony_prefix(user):
    return '<|start|>user<|message|>'+user+'<|end|><|start|>assistant<|channel|>final<|message|>'

def main(a):
    import torch
    import torch.distributed as dist
    from transformers import AutoTokenizer, AutoModelForCausalLM
    from peft import LoraConfig, get_peft_model
    rank=int(os.environ.get('RANK','0')); world=int(os.environ.get('WORLD_SIZE','1'))
    local=int(os.environ.get('LOCAL_RANK',rank)); torch.cuda.set_device(local)
    if world>1: dist.init_process_group('nccl')
    random.seed(a.seed); torch.manual_seed(a.seed)
    out=Path(a.output); out.mkdir(parents=True,exist_ok=False) if rank==0 else None
    all_rows=json.loads(Path(a.input).read_bytes())['rows']
    rows=[r for r in all_rows if 'fullmodule' in r.get('source_family','')][:a.rows]
    if len(rows)<a.rows: raise ValueError(f'need {a.rows} full-module rows, found {len(rows)}')
    tok=AutoTokenizer.from_pretrained(a.model,local_files_only=True)
    if tok.pad_token_id is None: tok.pad_token=tok.eos_token
    examples=[]; max_len=a.max_length
    for r in rows:
        prefix=harmony_prefix(r['prompt']); full=prefix+r['response']+'<|return|>'
        p=tok(prefix,add_special_tokens=False)['input_ids']; ids=tok(full,add_special_tokens=False)['input_ids'][:max_len]
        if len(ids)<=len(p): raise ValueError('response truncated or empty for '+r['id'])
        labels=[-100]*min(len(p),len(ids))+ids[len(p):]
        examples.append((ids,labels))
    load_kwargs=dict(torch_dtype=torch.bfloat16, local_files_only=True,
                     low_cpu_mem_usage=True)
    # GPT-OSS does not fit on one 40 GB device and its TP loader needs a
    # transient allocation larger than the remaining headroom.  A single
    # process with Accelerate's balanced device map keeps the base model
    # sharded across all four GPUs without replicated loader state.
    if world == 1:
        load_kwargs['device_map'] = 'auto'
    model=AutoModelForCausalLM.from_pretrained(a.model,**load_kwargs)
    model.config.use_cache=False; model.gradient_checkpointing_enable()
    model=get_peft_model(model,LoraConfig(r=16,lora_alpha=32,lora_dropout=0.05,
        target_modules=['q_proj','k_proj','v_proj','o_proj'],task_type='CAUSAL_LM'))
    model.print_trainable_parameters() if rank==0 else None
    input_device=next(model.parameters()).device
    opt=torch.optim.AdamW((p for p in model.parameters() if p.requires_grad),lr=a.lr,weight_decay=0.0)
    order=list(range(rank,len(examples),world)); metrics=[]; started=time.time()
    for epoch in range(a.epochs):
        random.Random(a.seed+epoch).shuffle(order)
        for idx in order:
            ids,labels=examples[idx]; x=torch.tensor([ids],device=input_device); y=torch.tensor([labels],device=input_device)
            opt.zero_grad(set_to_none=True)
            with torch.autocast('cuda',dtype=torch.bfloat16): loss=model(input_ids=x,labels=y,use_cache=False).loss
            if not torch.isfinite(loss): raise ValueError('nonfinite loss')
            loss.backward(); torch.nn.utils.clip_grad_norm_(model.parameters(),1.0); opt.step()
            metrics.append({'epoch':epoch,'row':rows[idx]['id'],'loss':float(loss.detach().cpu())})
    if world>1: dist.barrier()
    if rank==0:
        m=model.module if hasattr(model,'module') else model
        m.save_pretrained(out); tok.save_pretrained(out)
        (out/'receipt.json').write_text(json.dumps({'schema':1,'kind':'fullmodule_sft20b','complete':True,
            'rows':len(rows),'source_filter':'fullmodule','epochs':a.epochs,'world_size':world,'seed':a.seed,'lr':a.lr,
            'input_sha256':sha(Path(a.input).read_bytes()),'train_rows_never_eval':True,
            'algorithm':'response-only GPT-OSS harmony FINAL-channel LoRA SFT',
            'metrics':metrics,'elapsed_seconds':time.time()-started},indent=2)+'\n')
    if world>1: dist.destroy_process_group()

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--model',required=True); p.add_argument('--input',required=True); p.add_argument('--output',required=True); p.add_argument('--rows',type=int,default=169); p.add_argument('--epochs',type=int,default=1); p.add_argument('--max-length',type=int,default=4096); p.add_argument('--lr',type=float,default=2e-5); p.add_argument('--seed',type=int,default=20260908); main(p.parse_args())
