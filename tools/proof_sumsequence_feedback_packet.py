"""Audited same-policy proof feedback; numerical admission still required to train."""
import argparse
import json
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_stochastic_verify as verifier
from tools.proof_token_rl_objective import group_advantages
from tools.proof_cuda_train import dump,file_sha
from tools.proof_token_rl_packet import digest

ROWS_SHA='5899398b30a06cb9f925e520283afd4fb71f76ff46d163d389f6046234349f79'
SUMMARY_SHA='095090c62dbc4e14ccf0109e27f52e9aa310e7a072c747fee261d77034d45643'


def build(evaluation,rollouts,records):
    if evaluation['arm']!='child' or evaluation['policy_sha256']!=verifier.sampling.POLICIES['child']:
        raise ValueError('Exact current child policy required')
    if len(rollouts)!=32 or len(records)!=32 or len(evaluation['requests'])!=32:
        raise ValueError('All32 attempts required; no selected-success packet')
    rewards=[]
    for request,raw,record in zip(evaluation['requests'],rollouts,records):
        verifier.sampling.validate_rollout(request,raw)
        if (record['arm']!='child' or any(record[k]!=request[k] for k in ('sample_id','task_id','attempt'))
            or record['rollout_sha256']!=digest(raw)):
            raise ValueError('Exact ordered raw proof-feedback binding required')
        score=record['proof'];finish=raw.get('finish_reason',raw['status'])
        if score is not None and (type(score) is not int or score not in (0,1) or finish!='eos'):
            raise ValueError('Only complete measured binary proof outcomes may train')
        if record['finish_reason']!=finish:raise ValueError('Completion evidence changed')
        rewards.append(dict(request,finish_reason=finish,reward=score,
            measured_model_outcome=score is not None,reward_eligible=score is not None,
            status=record['status'],rollout_sha256=digest(raw),proof_record_sha256=digest(record)))
    groups=[group_advantages(rewards[i:i+4]) for i in range(0,32,4)]
    return dict(schema=1,kind='verified_same_policy_proof_feedback',policy_sha256=evaluation['policy_sha256'],
        requested_samples=32,accounted_samples=32,rewards=rewards,groups=groups,
        eligible_groups=sum(g['eligible'] for g in groups),optimizer_updates=0,
        training_authorized=False,numerical_admission_required=True,generalization_claim=False,
        provenance='Saved samples from this exact unchanged policy; not a fresh online sampling run',
        reward_scope='Strict proof success is positive; measured syntax/contract/proof failures are negative; unknowns excluded')


def create(a):
    # Nested raw-process audits require absolute local paths.
    for name,value in vars(a).items():
        if isinstance(value,Path):setattr(a,name,value.resolve())
    if a.output.exists():raise ValueError('Append-only fresh output required')
    if file_sha(a.verified/'rows.json')!=ROWS_SHA or file_sha(a.verified/'summary.json')!=SUMMARY_SHA:
        raise ValueError('Exact completed strict64 replay required')
    tasks,arms=verifier.prepare(a)
    before=verifier.load(a.verified/'identity_before.json')
    if before!=verifier.load(a.verified/'identity_after.json') or before!=verifier.identity(a,tasks):
        raise ValueError('Current complete verifier/input identity required')
    records=verifier.load(a.verified/'rows.json')
    expected=[(arm,t,i) for arm in ('parent','child') for t in verifier.IDS for i in range(4)]
    if [(r['arm'],r['task_id'],r['attempt']) for r in records]!=expected:
        raise ValueError('Full64 ordered replay required')
    for row in records:
        raw=arms[row['arm']][verifier.IDS.index(row['task_id'])*4+row['attempt']]
        if row['rollout_sha256']!=digest(raw):raise ValueError('Raw replay linkage changed')
        if raw['finish_reason']!='eos':
            if row['proof'] is not None or row['sany'] is not None:raise ValueError('Incomplete response rewarded')
            continue
        task=tasks[row['task_id']];extracted=verifier.bridge.extract(raw['raw_reply'],task)
        if extracted!=row['extraction']:raise ValueError('Extraction changed')
        if extracted['fragment'] is None:
            if row['proof']!=0 or row['sany']!=0 or row['status']!='model_extraction':raise ValueError('Extraction verdict changed')
        else:
            verifier.audit_check(task,extracted['fragment'],row['evidence'],a.verified/'checks'/row['arm']/row['sample_id'],before['verifier'])
            if any(row[k]!=row['evidence'][k] for k in ('proof','sany','status')):raise ValueError('Raw proof verdict changed')
    evaluation=verifier.load(a.generations/'freeze.json')['arms']['child']['evaluation']
    result=build(evaluation,arms['child'],records[32:])
    result.update(verified_rows_sha256=ROWS_SHA,verified_summary_sha256=SUMMARY_SHA,
        identity_sha256=digest(before),packet_source_sha256=file_sha(Path(__file__)),
        child_rollouts_sha256=file_sha(a.generations/'child/rollouts.jsonl'))
    if before!=verifier.identity(a,tasks):raise ValueError('Inputs changed during packet audit')
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as stream:json.dump(result,stream,indent=2);stream.write('\n')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('output','verified','broader-prompts','generations','parent-checkpoint','child-checkpoint','training-cycle','gain-controls','controls','tokenizer-path'):
        parser.add_argument('--'+name,type=Path,required=True)
    for name in ('remote-root','remote-model','remote-parent','remote-child'):parser.add_argument('--'+name,required=True)
    result=create(parser.parse_args())
    print(json.dumps({k:result[k] for k in ('requested_samples','eligible_groups','training_authorized')}))


if __name__=='__main__':main()
