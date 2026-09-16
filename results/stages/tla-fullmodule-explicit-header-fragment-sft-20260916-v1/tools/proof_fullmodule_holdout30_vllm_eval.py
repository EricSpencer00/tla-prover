"""Protected official holdout30 FINAL-channel vLLM -> SANY/TLC evaluation."""
import argparse, hashlib, json, os, shutil, subprocess, time
from pathlib import Path
from harness import gen_eval, runner

def sha(b): return hashlib.sha256(b).hexdigest()

def owned(cmd, cwd, timeout):
    p=subprocess.run(cmd,cwd=cwd,text=True,capture_output=True,timeout=timeout)
    return p.returncode,p.stdout+p.stderr

def main(a):
    packet=json.loads(a.portable.joinpath('packet.json').read_bytes())
    all_rows = packet['tasks']
    end = a.limit if a.limit else len(all_rows)
    rows = all_rows[a.start:end]
    if not rows:
        raise ValueError('empty row range')
    out=a.output.resolve()
    if out.exists(): raise ValueError('append-only output already exists')
    out.mkdir(parents=True); (out/'rows').mkdir()
    import vllm
    from vllm import LLM, SamplingParams
    from vllm.lora.request import LoRARequest
    from transformers import AutoTokenizer
    tok=AutoTokenizer.from_pretrained(str(a.model_path),local_files_only=True)
    llm=LLM(model=str(a.model_path),tokenizer=str(a.model_path),tensor_parallel_size=4,
            max_model_len=32768,gpu_memory_utilization=.88,enforce_eager=True,
            trust_remote_code=True,enable_lora=True)
    sampling=SamplingParams(temperature=0.0,max_tokens=a.max_tokens)
    java=str(Path(a.java)); lib=':'.join(str(Path(a.base)/p) for p in ('tools/tlapm/lib/tlapm/stdlib','tools/community-modules','tools/extra-modules'))
    records=[]; started=time.monotonic()
    prompts=[]
    for row in rows:
        prompt=tok.apply_chat_template([{'role':'user','content':row['prompt']}],tokenize=False,add_generation_prompt=True)
        if not prompt.endswith('<|start|>assistant'): raise ValueError('unexpected chat template suffix')
        prompts.append(prompt + '<|channel|>final<|message|>')
    # Generate one immutable task at a time.  A single pathological prompt
    # must not stall a batched call and erase progress for all other rows.
    for row,prompt in zip(rows,prompts):
        result=llm.generate([prompt],sampling,use_tqdm=False,
                            lora_request=LoRARequest('repair',1,str(a.adapter)))[0]
        idx=rows.index(row)
        work=out/'rows'/str(row['id']); work.mkdir()
        raw=result.outputs[0].text
        # Preserve the exact generated text beside the verifier logs.  This
        # directory is a protected evaluation artifact (never training input)
        # and is required to diagnose SANY/TLC failures without relying on a
        # one-way hash alone.
        (work/'raw_reply.txt').write_text(raw)
        module=gen_eval.extract_module(raw)
        rec={'id':row['id'],'module_name':row['module_name'],'output_tokens':len(result.outputs[0].token_ids),
             'finish_reason':result.outputs[0].finish_reason,'raw_reply_sha256':sha(raw.encode()),'status':'model_extraction','sany':0,'tlc':None,'vacuity':[]}
        if module is not None and runner.module_name(module)==row['module_name']:
            name=row['module_name']; (work/f'{name}.tla').write_text(module)
            for h in row['dependencies'].values():
                depraw=(a.portable/'files'/f'{h}.tla').read_bytes(); depname=runner.module_name(depraw.decode())
                if depname: (work/f'{depname}.tla').write_bytes(depraw)
            tmp=work/'jtmp'; tmp.mkdir()
            rc,log=owned([java,f'-Djava.io.tmpdir={tmp}',f'-DTLA-Library={lib}','-cp',str(a.base/'tools/tla2tools.jar'),'tla2sany.SANY',f'{name}.tla'],work,a.timeout)
            (work/'sany.log').write_text(log); rec['status']='pass' if rc==0 and 'Fatal errors' not in log and '*** Errors:' not in log else 'model_sany_reject'; rec['sany']=1 if rec['status']=='pass' else 0
            if rec['sany']:
                cfg=row['config']['bytes']; (work/f'{name}.cfg').write_text(cfg)
                tlc,vac,tlclog,dt=runner.check_tlc(name,cfg,work,a.timeout)
                (work/'tlc.log').write_text(tlclog); rec.update(tlc=tlc,vacuity=vac)
        records.append(rec)
        (out/'records.json').write_text(json.dumps(records,indent=2)+'\n')
        (out/'partial_receipt.json').write_text(json.dumps({'schema':1,'complete':False,
            'start_row':a.start,'end_row':a.start+len(rows),'rows':len(records),'requested_rows':len(rows),'records':records,
            'input_packet_sha256':sha(a.portable.joinpath('packet.json').read_bytes()),
            'training_authorized':False,'protected_outputs_never_train':True},indent=2)+'\n')
    receipt={'schema':1,'kind':'protected_holdout30_direct_vllm_sany_tlc_nonvacuity','complete':True,'start_row':a.start,'end_row':a.start+len(rows),'rows':len(rows),
             'adapter':str(a.adapter),'max_tokens':a.max_tokens,'records':records,
             'sany_pass':sum(r['sany']==1 for r in records),'tlc_pass':sum(r['tlc']=='pass' for r in records),
             'nonvacuous_pass':sum(r['tlc']=='pass' and not r['vacuity'] for r in records),
             'elapsed_seconds':time.monotonic()-started,'input_packet_sha256':sha(a.portable.joinpath('packet.json').read_bytes()),
             'training_authorized':False,'protected_outputs_never_train':True}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--portable',type=Path,required=True); p.add_argument('--model-path',type=Path,required=True); p.add_argument('--adapter',type=Path,required=True); p.add_argument('--base',type=Path,required=True); p.add_argument('--output',type=Path,required=True); p.add_argument('--java',required=True); p.add_argument('--max-tokens',type=int,default=16384); p.add_argument('--timeout',type=int,default=60); p.add_argument('--item-timeout',type=int,default=30); p.add_argument('--start',type=int,default=0); p.add_argument('--limit',type=int,default=0); main(p.parse_args())
