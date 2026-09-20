"""Strict post-hoc TRAIN8 stochastic pass@4; two frozen arms, no training.

Each TLAPS invocation is isolated in its own Python process. The legacy runner
adapter is replaced only inside that dedicated process, never in this caller.
"""
import argparse
import json
from pathlib import Path
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_token_rl_policy_eval as policy
from tools import proof_token_rl_rewards as bridge
from tools.proof_token_rl_packet import digest,sha,validate_rollouts,validate_rollout,POLICY_SHA
from tools.proof_cuda_train import dump,file_sha
from harness import runner,proof_full_fragment_check as full
from harness.proof_owned_process import run_owned,as_runner_tuple
from tools.proof_outcome_audit import classify_outcome

PARENT=ROOT/'results/runs/proof-token-rl-cycle-20260906-v3/training'
CHILD=ROOT/'results/runs/proof-token-policy-eval-20260906-v2'
SANY=ROOT/'results/runs/proof-token-policy-sany-20260906-v2'
REQUESTS=ROOT/'results/runs/proof-token-rl-requests-20260906-v1/requests.json'
CONTROLS=ROOT/'results/runs/proof-token-rl-sany-controls-20260906-v1'
PINNED={PARENT/'rollouts.jsonl':'dc8e76971781ac26430c7aaeae482718c71d9273c90a3988fa736513ab0c99f9',
    PARENT/'rewards.json':'9117ef416dbaf00cea675ff3604b11b40ea5c5d7e1083a08caf8a9fcf2ff211c',
    CHILD/'rollouts.jsonl':'cbb6785693b9d7c2136bd6f2fdcc573350b6677d83eab5597c7fd4eec8b8f128',
    SANY/'rows.json':'0708bf14b0e17b073dbca0f5ecefb41dfe4baf02fc2849357212e3402f14b99a'}
SOURCES=('tools/proof_token_rl_stochastic_tlaps.py','harness/proof_full_fragment_check.py',
    'harness/proof_ladder_check.py','harness/proof_owned_process.py','tools/proof_outcome_audit.py',
    'tools/proof_token_rl_policy_eval.py','tools/proof_token_rl_rewards.py',
    'tools/proof_token_rl_packet.py','tools/proof_hierarchical_packet.py')


def checked(path,expected):
    raw=Path(path).read_bytes()
    if sha(raw)!=expected:raise ValueError('Frozen artifact hash mismatch: '+str(path))
    return raw


def audit_sany(packet,tasks,tokenizer,rows,records,current,*,child):
    requests=policy.derive_requests(packet)['requests'] if child else packet['requests']
    if len(rows)!=32 or len(records)!=32:raise ValueError('Exact32 ordered samples required')
    prepared=[]
    for request,row,record in zip(requests,rows,records):
        validate_rollout(request,row)
        if record.get('sample_id')!=request['sample_id'] or record.get('task_id')!=request['task_id']:
            raise ValueError('SANY ordered sample identity mismatch')
        finish=row.get('finish_reason',row['status'])
        if record.get('finish_reason')!=finish:raise ValueError('SANY finish evidence changed')
        task=tasks[request['task_id']];extraction=None
        if row['status'] in ('generated','generation_time_limit'):
            prompt=next(t for t in packet['tasks'] if t['id']==request['task_id'])
            encoded=bridge.encode_prompt(tokenizer,prompt)
            for key in ('input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256'):
                if row[key]!=encoded[key]:raise ValueError('Exact prompt/token identity mismatch')
            if bridge.decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:
                raise ValueError('Exact reply decoding mismatch')
        value=record.get('sany') if child else record.get('reward')
        if finish=='eos':
            extraction=bridge.extract(row['raw_reply'],task)
            if record.get('evidence',{}).get('extraction')!=extraction:
                raise ValueError('Raw exact extraction evidence mismatch')
            verdict=record.get('evidence',{}).get('sany')
            if verdict is not None:
                if extraction.get('fragment') is None:raise ValueError('SANY verdict without extracted fragment')
                bridge.audit_check(task,extraction['fragment'],verdict,current)
                expected=None if verdict['reward'] is None else bool(verdict['reward']) if child else verdict['reward']
                if record['status']!=verdict['status'] or value!=expected:
                    raise ValueError('SANY verdict accounting mismatch')
            elif extraction.get('fragment') is None:
                if record['status']!='model_extraction' or value!=0:raise ValueError('Extraction rejection mismatch')
            elif value is not None:raise ValueError('Measured SANY without raw check')
        elif value is not None or record.get('evidence')!={}:
            raise ValueError('Incomplete generation cannot be measured')
        prepared.append(dict(request=request,rollout_sha256=digest(row),finish_reason=finish,
            extraction=extraction,sany_status=record['status'],sany_pass=value==1,
            measured_sany=value is not None))
    return prepared


def prepare():
    packet,tasks,tokenizer=bridge.prepare(REQUESTS);current=bridge.identity(tasks)
    bridge.admit_controls(CONTROLS,packet,tasks,current)
    raw={path:checked(path,h) for path,h in PINNED.items()}
    parent_rows=[json.loads(line) for line in raw[PARENT/'rollouts.jsonl'].splitlines()]
    validate_rollouts(packet,parent_rows)
    reward=policy.worker.validate_rewards(packet,parent_rows,raw[PARENT/'rewards.json'],
        json.loads((PARENT/'rewards.receipt.json').read_bytes()),
        rollouts_sha256=PINNED[PARENT/'rollouts.jsonl'],
        bridge_source_sha256=file_sha(ROOT/'tools/proof_token_rl_rewards.py'))
    if reward['verifier_identity']!=current:raise ValueError('Parent raw SANY runtime identity changed')
    child_rows=[json.loads(line) for line in raw[CHILD/'rollouts.jsonl'].splitlines()]
    if current!=json.loads((SANY/'identity_before.json').read_bytes()) or current!=json.loads((SANY/'identity_after.json').read_bytes()):
        raise ValueError('Current raw SANY identity required')
    arms=dict(parent=audit_sany(packet,tasks,tokenizer,parent_rows,reward['rows'],current,child=False),
        child=audit_sany(packet,tasks,tokenizer,child_rows,json.loads(raw[SANY/'rows.json']),current,child=True))
    return tasks,arms


def identity(tasks):
    from tools.proof_hierarchical_packet import runtime_identity
    return dict(sany=bridge.identity(tasks),tlaps=runtime_identity(),
        sources={p:file_sha(ROOT/p) for p in SOURCES},
        inputs={str(p):sha(checked(p,h)) for p,h in PINNED.items()})


def worker(input_path,output):
    """Only invoked by the isolated owned subprocess, never the parent evaluator."""
    payload=json.loads(Path(input_path).read_bytes());task=payload['task']
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    for path,h in task['dependency_sha256'].items():checked(path,h)
    checked(task['source_path'],task['source_sha256'])
    original=runner.run_cmd
    def command(cmd,cwd,timeout):
        process=run_owned(cmd,cwd,timeout)
        dump(Path(cwd)/'owned_process.json',process)
        return as_runner_tuple(process)
    runner.run_cmd=command
    try:
        result=full.certify_fragment(task['prefix'],payload['fragment'],task['suffix'],
            theorem_name=task['theorem_name'],dependencies=tuple(map(Path,task['dependency_sha256'])),
            work_root=output/'check',timeout=payload['timeout'])
        dump(output/'result.json',result)
    finally:runner.run_cmd=original


def audit_strict(task,fragment,record):
    from harness.proof_ladder_check import _audit_tlaps
    work=Path(record['workdir'])
    expected=dict(prefix=task['prefix'],fragment=fragment,suffix=task['suffix'],
        theorem_name=task['theorem_name'],contract_version=full.CONTRACT_VERSION)
    if (record['sha256']!=sha((task['prefix']+fragment+task['suffix']).encode()) or
            json.loads((work/'input.json').read_bytes())!=expected or
            json.loads((work/'result.json').read_bytes())!=record or
            (work/'tlapm.log').read_text()!=record['output']):
        raise ValueError('Exact immutable strict input/log/result mismatch')
    if record.get('command'):
        deps={Path(p).name:h for p,h in task['dependency_sha256'].items()}
        _audit_tlaps(record,task['prefix'],fragment,task['suffix'],task['theorem_name'],deps)
        expected_command=[str(runner.TLAPM),'--strict','--nofp','--cache-dir',str(work/'.tlacache')]
        for directory in runner.TLA_LIBRARY.split(':'):expected_command+=['-I',directory]
        expected_command.append(Path(record['candidate_path']).name)
        process=json.loads((work/'owned_process.json').read_bytes())
        if record['command']!=expected_command or process['command']!=expected_command or Path(process['cwd']).resolve()!=work.resolve():
            raise ValueError('Exact strict owned command required')
        rc,out,seconds,timed_out=as_runner_tuple(process)
        if (rc,out,seconds,timed_out)!=(record['returncode'],record['output'],record['seconds'],record['timed_out']):
            raise ValueError('Strict owned process evidence mismatch')
    return classify_outcome(record,provenance_verified=True)


def check(task,fragment,work,timeout):
    work=Path(work).resolve();work.mkdir(parents=True,exist_ok=False)
    payload=dict(task=task,fragment=fragment,timeout=max(.01,timeout-1.5))
    dump(work/'input.json',payload)
    cmd=[sys.executable,str(Path(__file__).resolve()),'worker','--input',str(work/'input.json'),'--output',str(work/'worker')]
    process=run_owned(cmd,work,timeout);dump(work/'process.json',process)
    if json.loads((work/'process.json').read_bytes())!=process:
        raise ValueError('Persisted dedicated process evidence changed')
    rc,out,elapsed,timed_out=as_runner_tuple(process)
    if json.loads((work/'input.json').read_bytes())!=payload:raise ValueError('Dedicated checker input changed')
    result=dict(classification='unmeasured_infrastructure',measured_model_outcome=False,
        certified=False,workdir=str(work),process=process,seconds=elapsed)
    if process['command']!=cmd or Path(process['cwd']).resolve()!=work:
        raise ValueError('Dedicated process command/cwd changed')
    if timed_out or rc!=0 or elapsed>timeout:return result
    record=json.loads((work/'worker/result.json').read_bytes())
    diagnostic=audit_strict(task,fragment,record)
    result.update(classification=diagnostic['classification'],measured_model_outcome=diagnostic['measured_model_outcome'],
        certified=diagnostic['classification']=='proof_success',strict=record)
    return result


def summarize(rows,complete):
    result={}
    for arm in ('parent','child'):
        records=[r for r in rows if r['arm']==arm];tasks={}
        for r in records:tasks.setdefault(r['task_id'],[]).append(r)
        result[arm]=dict(requested_samples=32,accounted_samples=len(records),
            certified_samples=sum(r['certified'] for r in records) if complete else 0,
            measured_rejections=sum(r['measured'] and not r['certified'] for r in records),
            unknown_samples=sum(not r['measured'] for r in records),
            stochastic_sample0_pass_tasks=sum(any(r['attempt']==0 and r['certified'] for r in rs) for rs in tasks.values()) if complete else 0,
            pass_at4_tasks=sum(any(r['certified'] for r in rs) for rs in tasks.values()) if complete else 0,
            requested_tasks=8,per_task={key:dict(requested=4,accounted=len(rs),
                certified=sum(r['certified'] for r in rs) if complete else 0,
                sample0_pass=complete and any(r['attempt']==0 and r['certified'] for r in rs),
                pass_at4=complete and any(r['certified'] for r in rs)) for key,rs in tasks.items()})
    return result


def evaluate(tasks,arms,output,*,checker=check,attest=identity,clock=time.monotonic):
    if set(arms)!={'parent','child'} or len(tasks)!=8:raise ValueError('Exact paired TRAIN8 required')
    keys=None
    for arm,rows in arms.items():
        if len(rows)!=32:raise ValueError('Exact32 ordered samples per arm required')
        actual=[(r['request']['task_id'],r['request']['attempt']) for r in rows]
        if keys is None:keys=[(task,i) for task in tasks for i in range(4)]
        if actual!=keys:raise ValueError('Frozen task/sample order required')
        if any(r['request']['policy_sha256']!=(POLICY_SHA if arm=='parent' else policy.CHILD_SHA) for r in rows):
            raise ValueError('Exact arm policy hash required')
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    frozen=digest(dict(tasks=tasks,arms=arms));before=attest(tasks);dump(output/'identity_before.json',before)
    dump(output/'config.json',dict(inputs_sha256=frozen,seconds_per_arm=1000,timeout=30,
        requested_per_arm=32,scope=policy.SCOPE,post_hoc_replay=True,optimizer_updates=0,
        stochastic_sample0_not_greedy=True,pooling=False,retries=0))
    config=json.loads((output/'config.json').read_bytes())
    config['subprocess_budget_policy']=dict(outer_max_seconds=30,worker_startup_and_exit_allowance_seconds=1.5,
        inner_max_timeout_seconds=28.5,owned_cleanup_reserve_seconds=.5,
        note='Outer and inner owned deadlines include cleanup; both stochastic arms match. Not the greedy wrapper budget.')
    dump(output/'config.json',config)
    rows=[]
    with (output/'rows.jsonl').open('x') as stream:
        for arm in ('parent','child'):
            started=clock()
            for item in arms[arm]:
                request=item['request'];task=tasks[request['task_id']]
                r=dict(arm=arm,task_id=task['id'],attempt=request['attempt'],sample_id=request['sample_id'],
                    policy_sha256=request['policy_sha256'],input_sha256=digest(item),certified=False,
                    measured=False,status='unmeasured_generation',evidence=None)
                remaining=1000-(clock()-started)
                if item['finish_reason']=='eos':
                    if not item['sany_pass']:
                        r.update(measured=item['measured_sany'],status=item['sany_status'])
                    elif remaining<2:r['status']='unmeasured_budget'
                    else:
                        result=checker(task,item['extraction']['fragment'],output/'checks'/arm/request['sample_id'],min(30,remaining))
                        r.update(certified=result['certified'],measured=result['measured_model_outcome'],
                            status=result['classification'],evidence=result)
                rows.append(r);stream.write(json.dumps(r)+'\n');stream.flush()
                dump(output/'summary.json',dict(complete=False,per_arm=summarize(rows,False)))
    after=attest(tasks);dump(output/'identity_after.json',after)
    if before!=after or frozen!=digest(dict(tasks=tasks,arms=arms)):
        raise ValueError('Frozen inputs or verifier source drift; no completed claims')
    result=dict(complete=True,per_arm=summarize(rows,True),rows_sha256=file_sha(output/'rows.jsonl'),
        scope=policy.SCOPE,model_sampling=False,training=False,generalization_claim=False)
    dump(output/'summary.json',result);return result


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('evaluate','worker'))
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--input',type=Path)
    a=parser.parse_args()
    if a.mode=='worker':worker(a.input,a.output)
    else:
        tasks,arms=prepare();print(json.dumps(evaluate(tasks,arms,a.output)))


if __name__=='__main__':main()
