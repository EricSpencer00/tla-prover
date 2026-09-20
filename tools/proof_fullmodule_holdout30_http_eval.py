"""Streaming HTTP holdout evaluator with a hard per-request wall budget."""
import argparse, hashlib, json, multiprocessing as mp, os, queue, signal, subprocess, time
from pathlib import Path
from harness import gen_eval, runner

def sha(b): return hashlib.sha256(b).hexdigest()
def run(cmd,cwd,timeout):
    proc=None
    try:
        proc=subprocess.Popen(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT,start_new_session=True)
        out,_=proc.communicate(timeout=timeout)
        return proc.returncode,out
    except subprocess.TimeoutExpired as e:
        if proc is not None:
            try: os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError: pass
            out,_=proc.communicate()
        else: out=''
        return -1,(out or '')

def evaluate_row(row, work, prompt, a, result_q):
    """Child boundary: perform exactly one request and one verifier pass.

    The parent deliberately does not execute any blocking operation here.  A
    crashed or wedged HTTP client, Java process, or TLC subprocess therefore
    cannot prevent the append-only parent receipt from advancing.
    """
    try:
        body=json.dumps({'model':'repair','prompt':prompt,'temperature':0.0,
                         'max_tokens':a.max_tokens,'stream':True}).encode()
        raw=''; tokens=0; finish='time_limit'
        cmd=['curl','--noproxy','*','--silent','--show-error','--no-buffer','--max-time',str(a.item_timeout),
             '-H','Content-Type: application/json','--data-binary',body.decode(),a.url+'/v1/completions']
        proc=subprocess.run(cmd,text=True,capture_output=True,timeout=a.item_timeout+5)
        (work/'http_response.sse').write_text(proc.stdout)
        for line in proc.stdout.splitlines():
            if not line.startswith('data:'): continue
            payload=line[5:].strip()
            if payload=='[DONE]': finish='stop'; break
            try: choice=json.loads(payload)['choices'][0]
            except (ValueError, KeyError, IndexError): continue
            # vLLM's GPT-OSS OpenAI adapter may place streamed text in either
            # the legacy completion field or a chat/reasoning delta. Preserve
            # every emitted channel for extraction; never synthesize content.
            delta=choice.get('delta') or {}
            message=choice.get('message') or {}
            piece=(choice.get('text') or delta.get('content') or
                   message.get('content') or choice.get('reasoning_content') or
                   delta.get('reasoning_content') or message.get('reasoning_content') or '')
            raw += piece; tokens += 1 if piece else 0
            if choice.get('finish_reason'):
                finish=choice['finish_reason']; break
        if proc.returncode == 0 and finish == 'time_limit': finish='stop'
        if not raw:
            try:
                err=json.loads(proc.stdout).get('error')
                if err:
                    finish='http_error'
            except (ValueError, TypeError):
                pass
        rec={'id':row['id'],'module_name':row['module_name'],'output_tokens':tokens,
             'finish_reason':finish,'raw_reply_sha256':sha(raw.encode()),
             'status':'model_extraction','sany':0,'tlc':None,'vacuity':[]}
        module=gen_eval.extract_module(raw)
        if module is not None and runner.module_name(module)==row['module_name']:
            name=row['module_name']; (work/f'{name}.tla').write_text(module)
            for h in row['dependencies'].values():
                depraw=(a.portable/'files'/f'{h}.tla').read_bytes()
                depname=runner.module_name(depraw.decode())
                if depname: (work/f'{depname}.tla').write_bytes(depraw)
            tmp=work/'jtmp'; tmp.mkdir(); rc,log=run(
                [a.java,f'-Djava.io.tmpdir={tmp}',f'-DTLA-Library={a.library}',
                 '-cp',str(a.base/'tools/tla2tools.jar'),'tla2sany.SANY',f'{name}.tla'],
                work,a.timeout)
            (work/'sany.log').write_text(log)
            rec['status']='pass' if rc==0 and 'Fatal errors' not in log and '*** Errors:' not in log else 'model_sany_reject'
            rec['sany']=1 if rec['status']=='pass' else 0
            if rec['sany']:
                cfg=row['config']['bytes']; (work/f'{name}.cfg').write_text(cfg)
                tlc,vac,tlclog,dt=runner.check_tlc(name,cfg,work,a.timeout)
                (work/'tlc.log').write_text(tlclog); rec.update(tlc=tlc,vacuity=vac)
        result_q.put(rec)
    except subprocess.TimeoutExpired:
        result_q.put({'id':row['id'],'module_name':row['module_name'],'output_tokens':0,
                      'finish_reason':'time_limit','raw_reply_sha256':sha(b''),
                      'status':'child_timeout','sany':0,'tlc':None,'vacuity':[]})
    except Exception as exc:
        result_q.put({'id':row['id'],'module_name':row['module_name'],'output_tokens':0,
                      'finish_reason':'child_error','raw_reply_sha256':sha(b''),
                      'status':'harness_error','error':repr(exc),'sany':0,'tlc':None,'vacuity':[]})

def main(a):
    packet=json.loads((a.portable/'packet.json').read_bytes()); rows=packet['tasks'][:a.limit] if a.limit else packet['tasks']
    out=a.output.resolve(); out.mkdir(parents=True,exist_ok=False); (out/'rows').mkdir()
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(str(a.tokenizer),local_files_only=True)
    records=[]; started=time.monotonic()
    def persist(done=False):
        receipt={'schema':1,'kind':'protected_holdout30_http_sany_tlc_nonvacuity',
                 'complete':done and len(records)==len(rows),'rows':len(records),
                 'requested_rows':len(rows),'records':records,
                 'elapsed_seconds':time.monotonic()-started,
                 'input_packet_sha256':sha((a.portable/'packet.json').read_bytes()),
                 'training_authorized':False,'protected_outputs_never_train':True}
        (out/('receipt.json' if done else 'partial_receipt.json')).write_text(json.dumps(receipt,indent=2)+'\n')
        (out/'records.json').write_text(json.dumps(records,indent=2)+'\n')
    persist(False)
    for row in rows:
        work=out/'rows'/str(row['id']); work.mkdir()
        prompt=tokenizer.apply_chat_template([{'role':'user','content':row['prompt']}],tokenize=False,add_generation_prompt=True)
        if not prompt.endswith('<|start|>assistant'): raise ValueError('unexpected chat template suffix')
        prompt += '<|channel|>final<|message|>'
        # Only the parent owns receipt persistence.  A fresh child owns the
        # request and verifier work and is forcibly torn down at the boundary.
        result_q=mp.Queue(); child=mp.Process(target=evaluate_row,
                                               args=(row,work,prompt,a,result_q),
                                               daemon=True)
        child.start(); child.join(a.item_timeout + a.timeout + 10)
        if child.is_alive():
            os.kill(child.pid, signal.SIGKILL); child.join()
            rec={'id':row['id'],'module_name':row['module_name'],'output_tokens':0,
                 'finish_reason':'supervisor_timeout','raw_reply_sha256':sha(b''),
                 'status':'supervisor_timeout','sany':0,'tlc':None,'vacuity':[]}
        else:
            # Queue feeder threads may flush just after the child exits; use a
            # bounded get instead of the racy empty() probe.
            try: rec=result_q.get(timeout=2)
            except queue.Empty:
                rec={'id':row['id'],'module_name':row['module_name'],'output_tokens':0,
                     'finish_reason':'child_exit','raw_reply_sha256':sha(b''),
                     'status':'child_exit','sany':0,'tlc':None,'vacuity':[]}
        if rec is None:
            rec={'id':row['id'],'module_name':row['module_name'],'output_tokens':0,
                 'finish_reason':'child_exit','raw_reply_sha256':sha(b''),
                 'status':'child_exit','sany':0,'tlc':None,'vacuity':[]}
        records.append(rec); persist(False)
    persist(True)

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--portable',type=Path,required=True); p.add_argument('--output',type=Path,required=True); p.add_argument('--base',type=Path,required=True); p.add_argument('--library',required=True); p.add_argument('--java',required=True); p.add_argument('--adapter',type=Path,required=True); p.add_argument('--tokenizer',required=True); p.add_argument('--url',default='http://127.0.0.1:8000'); p.add_argument('--max-tokens',type=int,default=16384); p.add_argument('--item-timeout',type=int,default=30); p.add_argument('--timeout',type=int,default=60); p.add_argument('--limit',type=int,default=0); main(p.parse_args())
