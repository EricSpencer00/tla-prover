"""One bounded parent40 -> supervised80 -> child40 experiment, no gate claims."""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_repair_train as train
from tools import proof_sumsequence_repair_eval as evaluate
from tools.proof_cuda_eval import dump,digest,sha
from tools.proof_cuda_train import file_sha
from harness.proof_owned_process import run_owned,as_runner_tuple

SECONDS=3420


def source_identity():
    names=set(train.SOURCES)|set(evaluate.SOURCES)|{
        'tools/proof_sumsequence_repair_cycle.py','tools/proof_sumsequence_repair_cycle.pbs'}
    return {n:file_sha(ROOT/n) for n in sorted(names)}


def train_args(a,output,admission=None):
    return SimpleNamespace(input=a.input,expected_input_sha256=a.train_sha,
        model_path=a.model_path,checkpoint=a.checkpoint,output=output,admission=admission)


def eval_args(a,role,checkpoint,expected,output,admission=None):
    return SimpleNamespace(prompts=a.prompts,expected_input_sha256=a.prompts_sha,
        model_path=a.model_path,checkpoint=checkpoint,role=role,
        expected_checkpoint_sha256=expected,output=output,admission=admission)


def freeze(a):
    before=source_identity()
    training=train.admit(train_args(a,a.output))
    parent=evaluate.admit(eval_args(a,'parent',a.checkpoint,evaluate.PARENT_SHA,a.output))
    if training['model_files']!=parent['model_files'] or training['versions']!=parent['versions']:
        raise ValueError('Training/evaluation model and runtime must match')
    encodings=training['encodings']; inputs=parent['input_evidence']
    if len(encodings)!=40 or len(inputs)!=40:
        raise ValueError('Full training/evaluation populations required')
    for ti,ei in [(i,i) for i in range(32)]+[(i, i+4) for i in range(32,36)]:
        encoded=encodings[ti]; expected=inputs[ei]
        if (encoded['input_ids'][:encoded['prompt_tokens']]!=expected['input_token_ids']
            or encoded['rendered_prompt']!=expected['rendered_prompt']):
            raise ValueError('Generation training/inference prefix mismatch')
    if before!=source_identity():
        raise ValueError('Source drift during full admission')
    return dict(training=training,parent=parent,sources=before,seconds=SECONDS,
        train_sha=a.train_sha,prompts_sha=a.prompts_sha,parent_sha=evaluate.PARENT_SHA,
        method='Two-epoch supervised reference repair with unchanged32 retention and4 new generation targets; not RL',
        phase_order=['parent40','train80','child40'],proof_verification_pending=True)


def validate_freeze(a,frozen):
    if (frozen['sources']!=source_identity() or frozen['seconds']!=SECONDS
        or frozen['parent_sha']!=evaluate.PARENT_SHA
        or frozen['train_sha']!=a.train_sha or frozen['prompts_sha']!=a.prompts_sha
        or file_sha(a.input)!=a.train_sha or file_sha(a.prompts)!=a.prompts_sha):
        raise ValueError('Frozen cycle inputs/source mismatch')


def validate_training_receipt(output,summary):
    """Bind the validated return value to the successful owned worker's files."""
    receipt=json.loads((output/'admitted.json').read_bytes())
    saved=json.loads((output/'summary.json').read_bytes())
    process=json.loads((output/'process.json').read_bytes())
    rc,_,_,timeout=as_runner_tuple(process)
    if (receipt.get('complete') is not True or summary!=saved
        or saved.get('complete') is not True or saved.get('actual_updates')!=80
        or saved.get('parent_checkpoint_sha256')!=evaluate.PARENT_SHA
        or receipt.get('summary_sha256')!=file_sha(output/'summary.json')
        or receipt.get('process_sha256')!=file_sha(output/'process.json')
        or rc!=0 or timeout
        or saved.get('checkpoint_sha256')!=file_sha(output/'policy_optimizer.pt')):
        raise ValueError('Validated actual child receipt/checkpoint required')
    return receipt


def execute(a,*,clock=time.monotonic):
    frozen=json.loads(a.freeze.read_bytes());validate_freeze(a,frozen)
    started=clock()
    state=dict(complete=False,requested_parent=40,requested_child=40,requested_updates=80,
               phase='admitted',proof_verification_pending=True,
               unattempted_task_ids={role:[r['id'] for r in frozen['parent']['input_evidence']]
                                     for role in ('parent','child')})
    def save():dump(a.output/'summary.json',state)
    def guard(reserve):
        validate_freeze(a,frozen)
        if SECONDS-(clock()-started)<reserve:
            raise TimeoutError('Insufficient remaining cycle budget; no shortened phase')
    save()
    dump(a.output/'parent-admission.json',frozen['parent'])
    dump(a.output/'train-admission.json',frozen['training'])
    try:
        guard(2200);state['phase']='parent40';save()
        parent=evaluate.generate(eval_args(a,'parent',a.checkpoint,evaluate.PARENT_SHA,
            a.output/'parent',a.output/'parent-admission.json'))
        if parent.get('complete') is not True:
            raise ValueError('Complete parent baseline required before optimizer')
        state['parent']=parent;state['unattempted_task_ids']['parent']=parent['unattempted_ids']
        state['phase']='train80';save();guard(2200)
        training=train.supervise(train_args(a,a.output/'training',a.output/'train-admission.json'))
        # supervise must perform actual checkpoint/optimizer/ledger validation,
        # not simply return the worker's success flag.
        child=a.output/'training/policy_optimizer.pt'
        admitted=validate_training_receipt(a.output/'training',training)
        state['training']=training;state['training_admission']=admitted;save();guard(1020)
        args=eval_args(a,'child',child,training['checkpoint_sha256'],a.output/'child',a.output/'child-admission.json')
        child_admission=evaluate.admit(args)
        dump(args.admission,child_admission)
        dump(a.output/'training-linkage.json',dict(validated=True,
            training_admitted_sha256=file_sha(a.output/'training/admitted.json'),
            child_checkpoint_sha256=training['checkpoint_sha256'],parent_checkpoint_sha256=evaluate.PARENT_SHA,
            note='Inference alone never establishes training provenance'))
        state['phase']='child40';save();guard(1000)
        state['child']=evaluate.generate(args)
        state['unattempted_task_ids']['child']=state['child']['unattempted_ids']
        if state['child'].get('complete') is not True:
            raise ValueError('Complete child evaluation required')
        guard(0)
        state.update(complete=state['child'].get('complete') is True,phase='evaluated_pending_proof_checks',
                     elapsed_seconds=clock()-started)
        save()
    except BaseException as exc:
        state.update(complete=False,error=type(exc).__name__+': '+str(exc),elapsed_seconds=clock()-started)
        save();raise


def supervise(a):
    a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=False)
    frozen=json.loads(a.freeze.read_bytes());validate_freeze(a,frozen)
    dump(a.output/'freeze.json',frozen)
    dump(a.output/'summary.json',dict(complete=False,requested_parent=40,requested_child=40,
        requested_updates=80,phase='outer_started',proof_verification_pending=True,
        unattempted_task_ids={role:[r['id'] for r in frozen['parent']['input_evidence']]
                             for role in ('parent','child')}))
    cmd=[sys.executable,str(Path(__file__).resolve()),'_run','--train-sha',a.train_sha,'--prompts-sha',a.prompts_sha]
    for name in ('input','prompts','model_path','checkpoint','output'):
        cmd+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
    cmd+=['--freeze',str(a.output/'freeze.json')]
    process=run_owned(cmd,ROOT,SECONDS);dump(a.output/'cycle_process.json',process)
    rc,_,_,timeout=as_runner_tuple(process)
    summary=json.loads((a.output/'summary.json').read_bytes())
    if rc!=0 or timeout or summary.get('complete') is not True:
        dump(a.output/'cycle_incomplete.json',dict(complete=False,returncode=rc,timed_out=timeout,
            requested_parent=40,requested_child=40,requested_updates=80))
        raise RuntimeError('Cycle incomplete; preserve partial artifacts and do not relaunch blindly')
    return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('freeze','run','_run'))
    for name in ('input','prompts','model-path','checkpoint','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--freeze',type=Path)
    parser.add_argument('--train-sha',required=True);parser.add_argument('--prompts-sha',required=True)
    args=parser.parse_args()
    if args.mode=='freeze':dump(args.output,freeze(args))
    elif args.freeze is None:parser.error('Actual full admission required')
    elif args.mode=='run':supervise(args)
    else:execute(args)
