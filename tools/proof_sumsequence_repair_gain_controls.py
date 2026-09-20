"""Independent positive/FALSE confirmation of five fixed, observed TRAIN gains."""
import argparse
import json
from pathlib import Path
import sys
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_repair_verify as verify
from tools.proof_cuda_eval import dump,digest,sha
from tools.proof_cuda_train import file_sha
from tools.proof_breadth26_manifest import wrong_conclusion
from tools.proof_sumsequence_controls import intended_false_failure

IDS=('breadth-Lock-MutualExclusion','breadth-Barriers-LockExclusion',
    'breadth-ReachabilityProofs-Reachable2','breadth26-LamportMutex_proofs-ContainsTail','sumsequence-Lemma2')
ROWS_SHA='5e8221c03b4899d4b1d9113bed72cd690cd77ad7f15930f3be1dc90e4a5306d0'
SUMMARY_SHA='72db5e0148c32e2de85bf6b5ad0d0c8b4e155e345a24f97b2f12d1820bf02429'


def load(path):return json.loads(Path(path).read_bytes())


def select(tasks,contexts,arms,replayed):
    if len(tasks)!=40 or len(replayed)!=80:raise ValueError('Complete40/80 paired inputs required')
    if [(r['arm'],r['id']) for r in replayed]!=[(arm,t['id']) for arm in ('parent','child') for t in tasks]:
        raise ValueError('Exact full ordered replay required')
    gains=tuple(t['id'] for i,t in enumerate(tasks) if replayed[40+i]['certified'] and not replayed[i]['certified'])
    if gains!=IDS:raise ValueError('Exact five observed gains required; no adaptive replacement')
    selected=[]
    for i,task in enumerate(tasks):
        if task['id'] not in IDS:continue
        row=arms['child']['rows'][i];record=replayed[40+i]
        if task['split']!='train' or row['finish_reason']!='eos':raise ValueError('Completed TRAIN child outputs required')
        fragment=verify.extract_proof_block(row['raw_reply']) if i<36 else verify.seq.extract(row['raw_reply'],contexts[i])['fragment']
        if fragment is None or fragment!=record['fragment'] or row['raw_reply_sha256']!=record['raw_reply_sha256']:
            raise ValueError('Exact actual child fragment/reply binding required')
        negative=dict(task,prefix=wrong_conclusion(task) if i<36 else task['negative_prefix'])
        if any(task[k]!=negative[k] for k in task if k!='prefix'):
            raise ValueError('Only conclusion-control prefix may change')
        selected.append(dict(task=task,negative=negative,fragment=fragment,
            raw_reply_sha256=row['raw_reply_sha256'],previous=record))
    return selected


def prepare(a):
    verify.strict.checked(a.verified/'rows.json',ROWS_SHA)
    verify.strict.checked(a.verified/'summary.json',SUMMARY_SHA)
    if load(a.verified/'summary.json').get('complete') is not True:
        raise ValueError('Completed prior strict replay required')
    verify.admit_integration_controls(a.controls)
    tasks,contexts,arms=verify.prepare(a)
    selected=select(tasks,contexts,arms,load(a.verified/'rows.json'))
    for item in selected:
        task=item['task'];prior=item['previous']['evidence']
        diagnostic=verify.audit_original(task,item['fragment'],prior['strict'])
        if diagnostic['classification']!='proof_success':raise ValueError('Prior raw proof not certified')
        if task['id'].startswith('sumsequence-'):
            verify.seq.audit_result(task,item['fragment'],prior,Path(prior['workdir']))
    return tasks,selected


def identity(a,tasks):
    result=verify.identity(a,tasks)
    result['gain_control_source']=file_sha(Path(__file__))
    result['previous_verification']={str(p):file_sha(p) for p in a.verified.rglob('*') if p.is_file()}
    return result


def audit_result(task,fragment,result,work):
    # All five are whole-target TRAIN proofs and use the exact unchanged
    # original adapter. Reconstruct the result from persisted inner/outer logs.
    record=result.get('strict')
    process=load(work/'process.json')
    if process!=result['process'] or load(work/'input.json')!=dict(task=task,fragment=fragment):
        raise ValueError('Exact raw gain-control outer evidence required')
    command=[sys.executable,str(ROOT/'tools/proof_sumsequence_repair_verify.py'),'worker',
        '--input',str(work/'input.json'),'--output',str(work/'worker')]
    rc,_,seconds,timed_out=verify.as_runner_tuple(process)
    if process['command']!=command or Path(process['cwd']).resolve()!=work:
        raise ValueError('Exact gain-control process command required')
    if timed_out or rc!=0 or seconds>30:
        if record is not None or result['certified'] or result['measured_model_outcome']:
            raise ValueError('Incomplete gain control cannot certify')
        return
    if record!=load(work/'worker/result.json'):raise ValueError('Raw strict gain result changed')
    diagnostic=verify.audit_original(task,fragment,record)
    if (result['classification']!=diagnostic['classification'] or
        result['measured_model_outcome']!=diagnostic['measured_model_outcome'] or
        result['certified']!=(diagnostic['classification']=='proof_success')):
        raise ValueError('Gain control classification changed')


def evaluate(a,*,checker=verify.check_original,clock=time.monotonic):
    a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=False)
    rows=[dict(id=key,label=label,accepted=False,status='unmeasured_pending') for key in IDS for label in ('positive','false_conclusion')]
    def save(complete=False):
        dump(a.output/'rows.json',rows)
        value=dict(complete=complete,requested_controls=10,accounted_controls=10,
            accepted_controls=sum(r['accepted'] for r in rows) if complete else 0,
            observed_accepted_controls=sum(r['accepted'] for r in rows),
            scope='Post-hoc five observed TRAIN gains; no additional model sampling, optimization, or generalization claim',
            rows_sha256=file_sha(a.output/'rows.json'))
        dump(a.output/'summary.json',value);return value
    save()
    try:
        tasks,selected=prepare(a);before=identity(a,tasks);dump(a.output/'identity_before.json',before)
        frozen=digest(selected)
        dump(a.output/'config.json',dict(selected_sha256=frozen,ids=IDS,previous_rows_sha256=ROWS_SHA,
            previous_summary_sha256=SUMMARY_SHA,requested_controls=10,seconds=400,
            timeout=30,inner_timeout=28.5,cleanup_reserve=.5,retries=0,
            mutation='Only FALSE target conclusion; preserve assumptions, bindings, dependencies and exact child fragment'))
        started=clock()
        for index,item in enumerate(selected):
            for offset,label in enumerate(('positive','false_conclusion')):
                row=rows[2*index+offset];task=item['task'] if offset==0 else item['negative']
                row.update(task=task,fragment=item['fragment'],raw_reply_sha256=item['raw_reply_sha256'])
                if clock()-started>370:row['status']='unmeasured_budget';save();continue
                work=a.output/'checks'/task['id']/label
                result=checker(task,item['fragment'],work)
                audit_result(task,item['fragment'],result,work)
                accepted=result['certified'] if offset==0 else ('strict' in result and intended_false_failure(result['strict']))
                row.update(result=result,accepted=accepted,status=result['classification']);save()
        elapsed=clock()-started;after=identity(a,tasks);dump(a.output/'identity_after.json',after)
        if before!=after or digest(selected)!=frozen or elapsed>400:
            raise ValueError('Source/runtime/control identity or budget changed')
        result=save(True);result['check_seconds']=elapsed;dump(a.output/'summary.json',result)
        if not all(r['accepted'] for r in rows):raise ValueError('One or more intended gain controls unsupported; no confirmation claim')
        return result
    except BaseException as exc:
        save(False);dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)));raise


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('prompts','generations','tokenizer-path','parent-checkpoint','controls','verified','output'):
        parser.add_argument('--'+name,type=Path,required=True)
    for name in ('remote-root','remote-parent','remote-model'):parser.add_argument('--'+name,required=True)
    print(json.dumps(evaluate(parser.parse_args())))


if __name__=='__main__':main()
