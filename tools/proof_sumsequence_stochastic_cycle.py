"""Frozen parent32/child32 stochastic diagnosis; no optimizer or proof claim."""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_stochastic_eval as sampling
from tools.proof_cuda_train import dump,file_sha
from harness.proof_owned_process import run_owned,as_runner_tuple

SECONDS=3420
ARMS=('parent','child')


def sources():
    names=set(sampling.SOURCES)|{'tools/proof_sumsequence_stochastic_cycle.py',
                                'tools/proof_sumsequence_stochastic_cycle.pbs'}
    return {n:file_sha(ROOT/n) for n in sorted(names)}


def arm_args(a,arm,admission=None):
    return SimpleNamespace(broader_prompts=a.broader_prompts,model_path=a.model_path,
        checkpoint=getattr(a,arm+'_checkpoint'),arm=arm,output=a.output/arm,admission=admission)


def freeze(a):
    before=sources()
    arms={arm:sampling.admit(arm_args(a,arm)) for arm in ARMS}
    value=dict(schema=1,seconds=SECONDS,phase_order=list(ARMS),requested_samples=64,
        optimizer_updates=0,broader_prompts_sha256=sampling.BROADER_SHA,
        policies=sampling.POLICIES,arms=arms,sources=before,verification_pending=True)
    validate_freeze(a,value)
    return value


def validate_freeze(a,value):
    raw=a.broader_prompts.read_bytes()
    if (value.get('schema')!=1 or value.get('seconds')!=SECONDS or
        value.get('phase_order')!=list(ARMS) or value.get('requested_samples')!=64 or
        value.get('optimizer_updates')!=0 or value.get('policies')!=sampling.POLICIES or
        value.get('sources')!=sources() or value.get('broader_prompts_sha256')!=sampling.BROADER_SHA or
        sampling.sha(raw)!=sampling.BROADER_SHA or set(value.get('arms',{}))!=set(ARMS)):
        raise ValueError('Exact frozen paired sources, inputs and budget required')
    for arm in ARMS:
        admitted=value['arms'][arm]
        if (admitted['evaluation']!=sampling.derive_requests(raw,arm) or
            admitted['checkpoint_sha256']!=sampling.POLICIES[arm] or len(admitted['encodings'])!=8):
            raise ValueError('Exact eight-task checkpoint admission required')
    for key in ('model_files','model_files_sha256','versions','dtype_profile','eos_token_ids','encodings'):
        if value['arms']['parent'][key]!=value['arms']['child'][key]:
            raise ValueError('Matched parent/child model, runtime and prompt encodings required')


def initial_state(frozen):
    return dict(complete=False,phase='pending',requested_samples=64,optimizer_updates=0,
        verification_pending=True,generalization_claim=False,
        unattempted_sample_ids={arm:[r['sample_id'] for r in frozen['arms'][arm]['evaluation']['requests']]
                                for arm in ARMS})


def validate_arm_result(output,arm,result):
    saved=json.loads((output/'summary.json').read_bytes())
    if (result!=saved or saved.get('phase_complete') is not True or
        saved.get('requested_samples')!=32 or saved.get('accounted_samples')!=32 or
        saved.get('generated_samples')!=32 or saved.get('unattempted_sample_ids')!=[] or
        saved.get('optimizer_updates')!=0 or saved.get('checkpoint_sha256')!=sampling.POLICIES[arm] or
        saved.get('process_sha256')!=file_sha(output/'process.json') or
        saved.get('rollouts_sha256')!=file_sha(output/'rollouts.jsonl')):
        raise ValueError('Complete exact raw arm evidence required')
    rc,_,_,timeout=as_runner_tuple(json.loads((output/'process.json').read_bytes()))
    if rc!=0 or timeout:raise ValueError('Owned arm execution and cleanup required')


def partial_accounting(output,frozen,state):
    """Do not relabel attempted samples as unattempted after an arm failure."""
    state['partial_accounting']={}
    for arm in ARMS:
        path=output/arm/'rollouts.jsonl'
        if not path.exists():continue
        try:
            rows=[json.loads(line) for line in path.read_bytes().splitlines()]
            sampling.validate_rows(frozen['arms'][arm],rows)
            state['unattempted_sample_ids'][arm]=[r['sample_id'] for r in rows if r['status']=='unattempted']
            state['partial_accounting'][arm]=dict(accounted_samples=32,
                generated_samples=sum(r['status'] in ('generated','generation_time_limit') for r in rows),
                worker_error_sample_ids=[r['sample_id'] for r in rows if r['status']=='worker_error'],
                rollouts_sha256=file_sha(path),verification_pending=True)
        except Exception as exc:
            state['unattempted_sample_ids'][arm]=None
            state['partial_accounting'][arm]=dict(accounting_unverified=True,
                unknown_sample_ids=[r['sample_id'] for r in frozen['arms'][arm]['evaluation']['requests']],
                error=type(exc).__name__+': '+str(exc),rollouts_sha256=file_sha(path))


def execute(a,*,clock=time.monotonic):
    frozen=json.loads(a.freeze.read_bytes());validate_freeze(a,frozen)
    started=clock();state=initial_state(frozen)
    def save():dump(a.output/'summary.json',state)
    save()
    try:
        for index,arm in enumerate(ARMS):
            validate_freeze(a,frozen)
            reserve=(2-index)*sampling.BUDGET['total_seconds']
            if SECONDS-(clock()-started)<reserve:
                raise TimeoutError('Insufficient paired budget; no shortened arm')
            admission=a.output/(arm+'-admission.json');dump(admission,frozen['arms'][arm])
            state['phase']=arm;save()
            result=sampling.generate(arm_args(a,arm,admission))
            validate_arm_result(a.output/arm,arm,result)
            state[arm]=result;state['unattempted_sample_ids'][arm]=[];save()
        validate_freeze(a,frozen)
        if clock()-started>SECONDS:raise TimeoutError('Total paired deadline exceeded')
        state.update(complete=True,phase='sampled_pending_verification',elapsed_seconds=clock()-started)
        save();return state
    except BaseException as exc:
        partial_accounting(a.output,frozen,state)
        state.update(complete=False,error=type(exc).__name__+': '+str(exc),elapsed_seconds=clock()-started)
        save();raise


def supervise(a):
    frozen=json.loads(a.freeze.read_bytes());validate_freeze(a,frozen)
    a.output=a.output.resolve()
    for path in (a.broader_prompts,a.model_path,a.parent_checkpoint,a.child_checkpoint,a.freeze):
        path=path.resolve()
        if a.output==path or a.output in path.parents or path in a.output.parents:
            raise ValueError('Paired output must be isolated from immutable inputs')
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'freeze.json',frozen);dump(a.output/'summary.json',initial_state(frozen))
    command=[sys.executable,str(Path(__file__).resolve()),'_run']
    for name in ('broader_prompts','model_path','parent_checkpoint','child_checkpoint','output'):
        command+=['--'+name.replace('_','-'),str(getattr(a,name).resolve())]
    command+=['--freeze',str(a.output/'freeze.json')]
    process=run_owned(command,ROOT,SECONDS);dump(a.output/'cycle_process.json',process)
    rc,_,_,timeout=as_runner_tuple(process)
    state=json.loads((a.output/'summary.json').read_bytes())
    if rc!=0 or timeout or state.get('complete') is not True:
        partial_accounting(a.output,frozen,state)
        state['complete']=False;dump(a.output/'summary.json',state)
        dump(a.output/'failure.json',dict(complete=False,returncode=rc,timed_out=timeout,requested_samples=64))
        raise RuntimeError('Paired run incomplete; preserve all artifacts')
    return state


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('freeze','run','_run'))
    for name in ('broader-prompts','model-path','parent-checkpoint','child-checkpoint','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--freeze',type=Path)
    a=parser.parse_args()
    if a.mode=='freeze':
        with a.output.open('x') as stream:json.dump(freeze(a),stream,indent=2);stream.write('\n')
    elif a.freeze is None:parser.error('Saved full paired admission required')
    elif a.mode=='run':supervise(a)
    else:execute(a)


if __name__=='__main__':main()
