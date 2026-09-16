"""Bounded stochastic candidate search against real SANY on protected rows.

Inference-only: it does not alter the checkpoint or train on eval rows.
"""
import argparse, json, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT))
from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi
from tools import proof_fullmodule_sany_feedback_repair_probe as repair

EVAL_ROWS=(47,107); MODULE_NAMES={47:'W4Od2m7p4t2',107:'W4Od3m0p0t0'}
def load(p): return json.loads(Path(p).read_bytes())
def prompt_only(tokenizer,prompt):
    rendered=tokenizer.apply_chat_template([dict(role='user',content=prompt)],tokenize=False,add_generation_prompt=True)
    ids=tokenizer(rendered,add_special_tokens=False,truncation=False)['input_ids']
    return dict(input_ids=ids,prompt_tokens=len(ids),rendered_prompt=rendered)
def run(a):
    import torch, transformers
    chosen,packet=repair.selected(Path(a.input).read_bytes())
    out=Path(a.output)
    if out.exists(): raise ValueError('append-only output already exists')
    out.mkdir(parents=True)
    tasks={i:multi.stage_task(multi.checker_task(packet,chosen[i][0]),out,str(i)) for i in EVAL_ROWS}
    identity=multi.sany.identity(list(tasks.values()))
    tokenizer=transformers.AutoTokenizer.from_pretrained(str(a.model_path),local_files_only=True)
    net=lineage.helpers.load_policy(str(a.model_path)); saved=torch.load(a.checkpoint,map_location='cpu',weights_only=False)
    lineage.helpers.restore_policy(net,saved,lineage.helpers.model_files(a.model_path)); del saved
    prior=repair.validate_eval_receipt(a.eval_receipt)
    prompts={47:prompt_only(tokenizer,repair.eval_feedback_prompt(chosen[47][0]['prompt'],prior['draft'],prior['diagnostic'])),107:prompt_only(tokenizer,chosen[107][0]['prompt'])}
    records={}; started=time.monotonic()
    for i in EVAL_ROWS:
        attempts=[]; winner=None
        for k in range(int(a.samples)):
            torch.manual_seed(int(a.seed)+i*1000+k)
            candidate=multi.decode(net,tokenizer,prompts[i],forced_prefix='---- MODULE '+MODULE_NAMES[i]+' ----\n',do_sample=True,temperature=float(a.temperature),top_p=float(a.top_p))
            checked=None
            if candidate['finish_reason']=='eos': checked=multi.sany.check(tasks[i],candidate['raw_reply'],out/'sany'/str(i)/str(k),identity,timeout=30)
            attempts.append(dict(sample=k,decode=candidate,sany=checked))
            if checked and checked.get('sany')==1: winner=k; break
        records[str(i)]={'attempts':attempts,'winner':winner,'sany_pass':winner is not None}
    receipt=dict(schema=1,complete=True,kind='sany_candidate_search',samples=int(a.samples),seed=int(a.seed),temperature=float(a.temperature),top_p=float(a.top_p),eval_rows=list(EVAL_ROWS),eval_rows_never_train=True,checkpoint_sha256=lineage.helpers.file_sha(a.checkpoint),input_sha256=multi.INPUT_SHA,sany_identity=identity,results=records,elapsed_seconds=time.monotonic()-started,gate_claim=False,generalization_claim=False,proof_claim=False,tlc_claim=False,nonvacuity_claim=False)
    lineage.helpers.dump(out/'receipt.json',receipt); return receipt
if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--input',type=Path,required=True); p.add_argument('--model-path',type=Path,required=True); p.add_argument('--checkpoint',type=Path,required=True); p.add_argument('--eval-receipt',type=Path,required=True); p.add_argument('--output',type=Path,required=True); p.add_argument('--samples',type=int,default=8); p.add_argument('--seed',type=int,default=20260907); p.add_argument('--temperature',type=float,default=.7); p.add_argument('--top-p',type=float,default=.9); run(p.parse_args())
