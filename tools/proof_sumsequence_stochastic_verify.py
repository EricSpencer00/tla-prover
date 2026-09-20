"""Fresh TRAIN8/G4 paired SANY/strict-proof diagnosis; no optimizer or gate claim."""
import argparse
import json
from pathlib import Path
import sys
import time
from types import SimpleNamespace
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_stochastic_eval as sampling,proof_sumsequence_stochastic_cycle as cycle
from tools import proof_token_rl_rewards as bridge,proof_token_rl_stochastic_tlaps as strict
from tools import proof_sumsequence_repair_verify as repair,proof_sumsequence_repair_gain_controls as gains
from tools.proof_token_rl_packet import INDICES,digest,sha
from tools.proof_cuda_train import dump,file_sha
from tools.proof_breadth26_manifest import wrong_conclusion
from tools.proof_sumsequence_controls import intended_false_failure
from harness.proof_owned_process import as_runner_tuple

REQUESTS=ROOT/'results/runs/proof-token-rl-requests-20260906-v1/requests.json'
SANY_CONTROLS=ROOT/'results/runs/proof-token-rl-sany-controls-20260906-v1'
GAIN_ROWS_SHA='70809da49392c9eb4f6bc214c3b1b91c12be0f465c56014568457c50e6a17d2f'
CONTROL_SOURCES=tuple(sorted(set(bridge.SOURCES)|set(strict.SOURCES)|set(repair.SOURCES)|{
    'tools/proof_sumsequence_stochastic_verify.py','tools/proof_sumsequence_repair_gain_controls.py'}))
from tools.proof_broader_packet import TRAIN_IDS
IDS=[TRAIN_IDS[i] for i in INDICES]


def load(path):return json.loads(Path(path).read_bytes())


def task_packet():
    packet,tasks,tokenizer=bridge.prepare(REQUESTS)
    for t in tasks.values():
        extracted=bridge.extract(t['reference_fragment'],t)
        if extracted.get('fragment') is None or extracted['fragment'].strip()!=t['reference_fragment'].strip():
            raise ValueError('Actual TRAIN8 reference extractor control failed')
    current=bridge.identity(tasks);bridge.admit_controls(SANY_CONTROLS,packet,tasks,current)
    return packet,tasks,tokenizer


def control_identity(tasks):
    from tools.proof_hierarchical_packet import runtime_identity
    return dict(sany=bridge.identity(tasks),tlaps=runtime_identity(),tasks_sha256=digest(tasks),
        sources={n:file_sha(ROOT/n) for n in CONTROL_SOURCES})


def check(task,fragment,work,current):
    work=work.resolve();work.mkdir(parents=True,exist_ok=False)
    sany=bridge.check(task,fragment,work/'sany',timeout=30)
    bridge.audit_check(task,fragment,sany,current['sany'])
    proof=None;status=sany['status'];result=None
    if sany['reward']==1:
        result=strict.check(task,fragment,work/'tlaps',30)
        repair.seq.audit_result(task,fragment,result,work/'tlaps')
        status=result['classification']
        proof=int(result['certified']) if result['measured_model_outcome'] else None
    elif sany['reward']==0:proof=0
    value=dict(sany=sany['reward'],proof=proof,status=status,sany_evidence=sany,proof_evidence=result,
        fragment_sha256=sha(fragment.encode()),task_sha256=digest(task))
    dump(work/'result.json',value);return value


def audit_check(task,fragment,value,work,current):
    if any(v is not None and (type(v) is not int or v not in (0,1)) for v in (value['sany'],value['proof'])):
        raise ValueError('Only explicit binary or unknown pipeline outcomes required')
    if load(work/'result.json')!=value or value['fragment_sha256']!=sha(fragment.encode()) or value['task_sha256']!=digest(task):
        raise ValueError('Exact pipeline task/fragment/result binding required')
    bridge.audit_check(task,fragment,value['sany_evidence'],current['sany'])
    sany=value['sany_evidence']['reward'];proof=value['proof_evidence']
    if value['sany']!=sany:raise ValueError('SANY feedback changed')
    if sany==1:
        if proof is None:raise ValueError('SANY-positive pipeline lacks strict result')
        repair.seq.audit_result(task,fragment,proof,work/'tlaps')
        expected=int(proof['certified']) if proof['measured_model_outcome'] else None
        if value['proof']!=expected or value['status']!=proof['classification']:raise ValueError('Strict binary feedback changed')
    elif proof is not None or value['proof']!=(0 if sany==0 else None) or value['status']!=value['sany_evidence']['status']:
        raise ValueError('Unknown or rejected SANY incorrectly promoted to proof')


def controls(output):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    packet,tasks,_=task_packet();before=control_identity(tasks);dump(output/'identity_before.json',before)
    requested=[(task,'reference') for task in tasks.values()]+[(dict(tasks[IDS[0]],prefix=wrong_conclusion(tasks[IDS[0]])),'false_conclusion')]
    rows=[dict(id=t['id'],label=label,accepted=False,status='unmeasured_pending') for t,label in requested]
    dump(output/'rows.json',rows);started=time.monotonic()
    for i,(task,label) in enumerate(requested):
        if time.monotonic()-started>540:rows[i]['status']='unmeasured_budget';continue
        value=check(task,task['reference_fragment'],output/'checks'/str(i),before)
        audit_check(task,task['reference_fragment'],value,output/'checks'/str(i),before)
        accepted=value['sany']==1 and (value['proof']==1 if label=='reference' else
            value['proof_evidence'] is not None and intended_false_failure(value['proof_evidence'].get('strict',{})))
        rows[i].update(task=task,result=value,accepted=accepted,status=value['status']);dump(output/'rows.json',rows)
    after=control_identity(tasks);dump(output/'identity_after.json',after)
    summary=dict(complete=before==after and all(r['accepted'] for r in rows) and time.monotonic()-started<=600,requested=9,accounted=9,
        accepted=sum(r['accepted'] for r in rows),reference_extractor_controls=8,
        rows_sha256=file_sha(output/'rows.json'),check_seconds=time.monotonic()-started)
    dump(output/'summary.json',summary)
    if not summary['complete']:raise ValueError('Actual pipeline controls not admitted')
    return summary


def admit_controls(directory,tasks):
    before=control_identity(tasks);rows=load(directory/'rows.json');summary=load(directory/'summary.json')
    if (summary.get('complete') is not True or summary.get('accepted')!=9 or summary.get('requested')!=9 or
        summary.get('accounted')!=9 or summary.get('reference_extractor_controls')!=8 or len(rows)!=9 or
        summary.get('rows_sha256')!=file_sha(directory/'rows.json') or
        not 0<=summary.get('check_seconds',float('inf'))<=600 or
        load(directory/'identity_before.json')!=before or load(directory/'identity_after.json')!=before):
        raise ValueError('Current complete raw nine pipeline controls required')
    expected=[(t,'reference') for t in tasks.values()]+[(dict(tasks[IDS[0]],prefix=wrong_conclusion(tasks[IDS[0]])),'false_conclusion')]
    for i,(row,(task,label)) in enumerate(zip(rows,expected)):
        if row['task']!=task or row['label']!=label or row['id']!=task['id']:raise ValueError('Exact control population required')
        audit_check(task,task['reference_fragment'],row['result'],directory/'checks'/str(i),before)
        value=row['result']
        if row['accepted'] is not True or value['sany']!=1 or not (value['proof']==1 if label=='reference' else
            intended_false_failure(value['proof_evidence'].get('strict',{}))):raise ValueError('Intended actual control outcome missing')
    return before


def training_linkage(a):
    from tools.proof_hierarchical_packet import runtime_identity
    frozen=load(a.training_cycle/'freeze.json')
    if file_sha(a.training_cycle/'freeze.json')!=repair.FREEZE_SHA:raise ValueError('Exact previously validated training cycle required')
    admission=load(a.training_cycle/'training/admission.json')
    if admission!=frozen['training'] or frozen['sources']!=repair.cycle.source_identity():raise ValueError('Training source/admission changed')
    trained=repair.train.validate_training(a.training_cycle/'training',admission,a.parent_checkpoint)
    repair.cycle.validate_training_receipt(a.training_cycle/'training',trained)
    if trained['checkpoint_sha256']!=sampling.POLICIES['child'] or file_sha(a.child_checkpoint)!=sampling.POLICIES['child']:
        raise ValueError('Actual80update child linkage required')
    rows=load(a.gain_controls/'rows.json');summary=load(a.gain_controls/'summary.json')
    before=load(a.gain_controls/'identity_before.json');after=load(a.gain_controls/'identity_after.json')
    if (file_sha(a.gain_controls/'rows.json')!=GAIN_ROWS_SHA or before!=after or summary.get('complete') is not True or
        summary.get('accepted_controls')!=10 or len(rows)!=10 or before['gain_control_source']!=file_sha(Path(gains.__file__))):
        raise ValueError('Actual ten gain controls required')
    if before['runtime']!=runtime_identity():raise ValueError('Gain controls use different current verifier runtime')
    for name,h in {**before['inputs'],**before['previous_verification']}.items():bridge.checked(name,h)
    for name,h in before['sources'].items():bridge.checked(ROOT/name,h)
    for row in rows:
        work=a.gain_controls/'checks'/row['id']/row['label']
        gains.audit_result(row['task'],row['fragment'],row['result'],work)
        if row['accepted'] is not True or not (row['result']['certified'] if row['label']=='positive' else
            intended_false_failure(row['result']['strict'])):raise ValueError('Gain confirmation changed')
    return trained


def read_rows(path):
    raw=path.read_bytes()
    if not raw.endswith(b'\n'):raise ValueError('Truncated stochastic ledger')
    return [json.loads(line) for line in raw.splitlines()]


def validate_arm(a,arm,admitted,tokenizer):
    import torch
    root=a.generations/arm;raw=a.broader_prompts.read_bytes()
    checkpoint=getattr(a,arm+'_checkpoint')
    if (admitted['evaluation']!=sampling.derive_requests(raw,arm) or
        admitted['implementation_sha256']!={n:file_sha(ROOT/n) for n in sampling.SOURCES} or
        admitted['checkpoint_sha256']!=sampling.POLICIES[arm] or file_sha(checkpoint)!=sampling.POLICIES[arm] or
        admitted['versions']!=sampling.common.FIRST_VERSIONS or
        admitted['model_files_sha256']!=sampling.common.MODEL_FILES_SHA or
        digest(admitted['model_files'])!=sampling.common.MODEL_FILES_SHA or
        admitted['dtype_profile']!=sampling.train.PROFILE or admitted['eos_token_ids']!=sampling.EOS_IDS):
        raise ValueError('Exact inference policy/model/runtime/source required')
    saved=torch.load(checkpoint,map_location='cpu',weights_only=False)
    if sampling.checkpoint_state(saved,admitted['model_files'])!=admitted['checkpoint_config_sha256']:
        raise ValueError('Actual checkpoint configuration changed')
    del saved
    expected={n:h for n,h in admitted['model_files'].items() if n.endswith('.json') or n in ('tokenizer.model','chat_template.jinja')}
    actual={p.name:file_sha(p) for p in a.tokenizer_path.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))}
    if actual!=expected:raise ValueError('Exact tokenizer inventory required')
    if admitted['encodings']!=[sampling.common.encode_prompt(tokenizer,t) for t in admitted['evaluation']['tasks']]:
        raise ValueError('Actual tokenizer input reconstruction changed')
    if load(root/'admission.json')!=admitted or load(a.generations/(arm+'-admission.json'))!=admitted:
        raise ValueError('Full per-arm admission mismatch')
    rows=read_rows(root/'rollouts.jsonl');sampling.validate_rows(admitted,rows,tokenizer)
    if read_rows(root/'events.jsonl')!=rows:raise ValueError('Append-only event ledger disagrees with final rows')
    summary=load(root/'summary.json');worker=load(root/'worker_summary.json')
    sampling.validate_worker_summary(worker,rows,root,arm)
    cycle.validate_arm_result(root,arm,summary)
    if {k:v for k,v in summary.items() if k not in ('total_arm_seconds','process_sha256')}!=worker:
        raise ValueError('Worker and supervisor summary disagree')
    if any(summary.get(k)!=v for k,v in sampling.accounting(rows).items()):raise ValueError('Full raw32 accounting mismatch')
    if (summary.get('identity_stable') is not True or summary.get('frozen_weights_verified') is not True or
        summary.get('checkpoint_restored_exactly') is not True or summary.get('failure') is not None or
        summary.get('optimizer_updates')!=0 or not 0<summary.get('total_arm_seconds',float('inf'))<=1500):
        raise ValueError('Frozen no-update inference evidence required')
    memory=summary['memory']
    if not 0<memory['allocated']<=memory['reserved']<=sampling.BUDGET['memory_limit']:raise ValueError('36GiB memory limit exceeded')
    remote=Path(a.remote_root);out=remote/'results/cycle'/arm
    command=[repair.PYTHON,str(remote/'tools/proof_sumsequence_stochastic_eval.py'),'worker',
        '--broader-prompts',str(remote/'prompts.json'),'--model-path',a.remote_model,
        '--checkpoint',getattr(a,'remote_'+arm),'--output',str(out),'--arm',arm,'--admission',str(out/'admission.json'),'--worker-seconds']
    process=load(root/'process.json')
    if process['command'][:-1]!=command:raise ValueError('Exact sampler process command required')
    seconds=float(process['command'][-1])
    if not 30<seconds<=1500 or not 0<summary['elapsed_seconds']<=seconds:raise ValueError('Fixed worker deadline required')
    repair.process_ok(process,command+[process['command'][-1]],remote,seconds)
    states={}
    for name in ('before','after'):
        path=root/('sampling_generator_'+name+'.pt')
        if file_sha(path)!=summary['sampling_generator_sha256'][name]:raise ValueError('Raw explicit RNG artifact hash changed')
        states[name]=torch.load(path,map_location='cpu',weights_only=True)
        if states[name].dtype!=torch.uint8 or states[name].ndim!=1 or not states[name].numel():
            raise ValueError('Nonempty exact RNG byte state required')
    return rows,states['before']


def prepare(a):
    import torch,transformers
    _,tasks,tokenizer=task_packet()
    training_linkage(a);admit_controls(a.controls,tasks)
    frozen=load(a.generations/'freeze.json');cycle.validate_freeze(SimpleNamespace(broader_prompts=a.broader_prompts),frozen)
    arms={};rng={}
    for arm in ('parent','child'):arms[arm],rng[arm]=validate_arm(a,arm,frozen['arms'][arm],tokenizer)
    if not torch.equal(rng['parent'],rng['child']):raise ValueError('Paired same-seed initial CUDA RNG states differ')
    state=load(a.generations/'summary.json')
    if (state.get('complete') is not True or state.get('phase')!='sampled_pending_verification' or
        state.get('requested_samples')!=64 or state.get('optimizer_updates')!=0 or
        state.get('unattempted_sample_ids')!={'parent':[],'child':[]}):raise ValueError('Complete paired64 cycle required')
    for arm in arms:
        if state[arm]!=load(a.generations/arm/'summary.json'):raise ValueError('Cycle/arm linkage changed')
    remote=Path(a.remote_root);out=remote/'results/cycle'
    command=[repair.PYTHON,str(remote/'tools/proof_sumsequence_stochastic_cycle.py'),'_run',
        '--broader-prompts',str(remote/'prompts.json'),'--model-path',a.remote_model,
        '--parent-checkpoint',a.remote_parent,'--child-checkpoint',a.remote_child,'--output',str(out),'--freeze',str(out/'freeze.json')]
    repair.process_ok(load(a.generations/'cycle_process.json'),command,remote,cycle.SECONDS)
    return tasks,arms


def identity(a,tasks):
    paths=[a.broader_prompts,a.parent_checkpoint,a.child_checkpoint]
    for root in (a.generations,a.training_cycle,a.gain_controls,a.controls,a.tokenizer_path):
        paths += [p for p in root.rglob('*') if p.is_file()]
    return dict(verifier=control_identity(tasks),sampling_sources=cycle.sources(),
        files={str(p.resolve()):file_sha(p) for p in paths})


def summarize(rows,complete):
    arms={}
    for arm in ('parent','child'):
        per_task={}
        for task in IDS:
            group=[r for r in rows if r['arm']==arm and r['task_id']==task]
            measured=len(group)==4 and all(r.get('finish_reason')=='eos' and type(r['proof']) is int and r['proof'] in (0,1) for r in group)
            values=[r['proof'] for r in group] if measured else []
            variance=sum((v-sum(values)/4)**2 for v in values)/4 if values else None
            per_task[task]=dict(requested=4,accounted=len(group),proof_passes=sum(r['proof']==1 for r in group) if complete else 0,
                sany_passes=sum(r['sany']==1 for r in group) if complete else 0,
                sample0_proved=complete and bool(group and group[0]['proof']==1),
                pass_at4=complete and any(r['proof']==1 for r in group),
                unknown_proofs=sum(r['proof'] is None for r in group),
                distinct_outputs=len({r['raw_reply_sha256'] for r in group if r.get('raw_reply_sha256')}),
                complete_measured_group=complete and measured,proof_variance=variance if complete else None,
                variance_eligible=complete and measured and variance>0)
        arms[arm]=dict(requested_samples=32,requested_tasks=8,tasks=per_task,
            proof_passes=sum(t['proof_passes'] for t in per_task.values()),
            sany_passes=sum(t['sany_passes'] for t in per_task.values()),
            sample0_pass_tasks=sum(t['sample0_proved'] for t in per_task.values()),
            pass_at4_tasks=sum(t['pass_at4'] for t in per_task.values()),
            variance_eligible_groups=sum(t['variance_eligible'] for t in per_task.values()))
    return arms


def evaluate(a,*,clock=time.monotonic):
    a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=False)
    rows=[dict(arm=arm,task_id=task,attempt=i,sample_id=task+':sample'+str(i),proof=None,sany=None,status='unmeasured_pending')
        for arm in ('parent','child') for task in IDS for i in range(4)]
    def save(complete=False):
        dump(a.output/'rows.json',rows);summary=dict(complete=complete,requested_samples=64,accounted_samples=64,
            per_arm=summarize(rows,complete),optimizer_updates=0,generalization_claim=False,training_authorized=False,
            scope='Reused TRAIN8 fresh-seed stochastic diagnosis; variance eligibility is not proof-learning evidence')
        dump(a.output/'summary.json',summary);return summary
    save()
    try:
        tasks,arms=prepare(a);before=identity(a,tasks);dump(a.output/'identity_before.json',before)
        frozen=digest(dict(tasks=tasks,arms=arms));current=before['verifier']
        dump(a.output/'config.json',dict(inputs_sha256=frozen,seconds_per_arm=2000,sany_timeout=30,tlaps_outer_timeout=30,
            tlaps_inner_timeout=28.5,cleanup_reserve=.5,repair_attempts=0,seed=sampling.BUDGET['seed'],
            sample0='first stochastic draw, not greedy',reward_delivery=False))
        for arm in ('parent','child'):
            started=clock()
            for i,generated in enumerate(arms[arm]):
                row=rows[(0 if arm=='parent' else 32)+i];task=tasks[row['task_id']]
                row.update(finish_reason=generated.get('finish_reason',generated['status']),status='unmeasured_generation',
                    raw_reply_sha256=generated.get('raw_reply_sha256'),rollout_sha256=digest(generated))
                if row['finish_reason']!='eos':save();continue
                extraction=bridge.extract(generated['raw_reply'],task);row['extraction']=extraction
                if extraction['fragment'] is None:row.update(proof=0,sany=0,status='model_extraction')
                elif clock()-started>1940:row['status']='unmeasured_budget'
                else:
                    work=a.output/'checks'/arm/row['sample_id'];value=check(task,extraction['fragment'],work,current)
                    audit_check(task,extraction['fragment'],value,work,current)
                    row.update(proof=value['proof'],sany=value['sany'],status=value['status'],evidence=value)
                save()
        after=identity(a,tasks);dump(a.output/'identity_after.json',after)
        if before!=after or digest(dict(tasks=tasks,arms=arms))!=frozen:raise ValueError('Raw input/source/verifier drift')
        return save(True)
    except BaseException as exc:
        save(False);dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc)));raise


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('controls','evaluate'))
    for name in ('output','broader-prompts','generations','parent-checkpoint','child-checkpoint','training-cycle','gain-controls','controls','tokenizer-path'):
        p.add_argument('--'+name,type=Path,required=name=='output')
    for name in ('remote-root','remote-model','remote-parent','remote-child'):p.add_argument('--'+name)
    a=p.parse_args();print(json.dumps(controls(a.output) if a.mode=='controls' else evaluate(a)))


if __name__=='__main__':main()
