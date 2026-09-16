"""Inference-only protected SANY evaluation through vLLM's direct engine API."""
import argparse, hashlib, json, time
from pathlib import Path
from tools import proof_fullmodule_multiexample_probe as multi
from tools import proof_fullmodule_sany_checks as sany

ROWS=(47,107)

def run(a):
    out=Path(a.output)
    if out.exists(): raise ValueError('append-only output already exists')
    out.mkdir(parents=True)
    chosen, packet = multi.selected(Path(a.input).read_bytes())
    tasks={i:multi.stage_task(multi.checker_task(packet,chosen[i][0]),out,str(i)) for i in ROWS}
    identity=sany.identity(list(tasks.values()))
    import vllm
    from vllm import LLM, SamplingParams
    from vllm.lora.request import LoRARequest
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(str(a.model_path), local_files_only=True)
    llm=LLM(model=str(a.model_path), tokenizer=str(a.model_path),
            tensor_parallel_size=4, max_model_len=4096,
            gpu_memory_utilization=.88, enforce_eager=True,
            trust_remote_code=True, enable_lora=True)
    sampling=SamplingParams(temperature=0.0, max_tokens=int(a.max_tokens))
    records={}; started=time.monotonic()
    for i in ROWS:
        # The frozen packet encodings belong to the historical 8B tokenizer.
        # Re-render the immutable user prompt with the admitted model's exact
        # chat template; raw user text would violate the training/inference
        # prefix contract and can turn a valid model into prose.
        prompt=tokenizer.apply_chat_template(
            [dict(role='user', content=chosen[i][0]['prompt'])],
            tokenize=False, add_generation_prompt=True)
        # This tokenizer's generation prompt ends at `<|start|>assistant` and
        # leaves channel selection to the model. The corpus contract trains
        # serialized specs in FINAL, so append the exact Harmony FINAL prefix
        # explicitly; replacing an analysis marker would be a no-op here.
        if prompt.endswith('<|start|>assistant'):
            prompt += '<|channel|>final<|message|>'
        elif not prompt.endswith('<|channel|>final<|message|>'):
            raise ValueError('unexpected Harmony generation prompt suffix')
        result=llm.generate([prompt], sampling, use_tqdm=False,
                            lora_request=LoRARequest('repair',1,str(a.adapter_path)))[0]
        text=result.outputs[0].text
        # These protected rows are full-module generation prompts (not
        # proof-hole prompts), so the model response itself is the candidate.
        raw=text
        attempt=out/'sany'/str(i); checked=sany.check(tasks[i],raw,attempt,identity,timeout=30)
        records[str(i)]={'input':{'rendered_prompt_sha256':hashlib.sha256(prompt.encode()).hexdigest()},
                         'output':{'raw_reply':raw,'finish_reason':result.outputs[0].finish_reason,
                                   'output_tokens':len(result.outputs[0].token_ids)},'sany':checked}
    receipt={'schema':1,'kind':'protected_direct_vllm_fullmodule_sany_eval','complete':True,
             'eval_rows':list(ROWS),'eval_rows_never_train':True,'eval_rows_never_train_attested':True,
             'model_path':str(a.model_path),'adapter_path':str(a.adapter_path),
             'input_sha256':multi.INPUT_SHA,'sany_identity':identity,'results':records,
             'elapsed_seconds':time.monotonic()-started,'gate_claim':False,
             'generalization_claim':False,'proof_claim':False,'tlc_claim':False,'nonvacuity_claim':False}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    return receipt

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--input',type=Path,required=True)
    p.add_argument('--model-path',type=Path,required=True); p.add_argument('--adapter-path',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True); p.add_argument('--max-tokens',type=int,default=1024)
    run(p.parse_args())
