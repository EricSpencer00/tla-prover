"""Fresh seed20261003 paired TRAIN8/G4 SANY+strict replay; no training export."""
import argparse
import json
import math
from pathlib import Path
import sys
import time
from types import SimpleNamespace
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_proof_rl_stochastic as sampler
from tools import proof_sumsequence_proof_rl_verify as common
from tools import proof_sumsequence_proof_rl_checks as checks
from tools.proof_cuda_train import file_sha,dump
from tools.proof_cuda_eval import digest,sha

LOCAL_PATHS=tuple(n for n in common.LOCAL_PATHS if n!='baseline_cycle')
SECONDS_PER_ARM=2000
SEED=20261003
SOURCES=tuple(sorted(set(sampler.SOURCES)|set(common.SOURCES)|{'tools/proof_sumsequence_proof_rl_stochastic_verify.py'}))


def load(path):return json.loads(Path(path).read_bytes())


def validate_pair_receipt(a,tokenizer):
    """Actual local byte/config audit; never call remote-only model admission."""
    import torch
    if file_sha(a.target_admission)!=a.target_admission_sha256:raise ValueError('Authentic paired target receipt SHA required')
    value=load(a.target_admission)
    if load(a.generations/'admission.json')!=value:raise ValueError('Original paired admission bytes changed')
    if (value.get('schema')!=1 or value.get('kind')!='proof_rl_fresh_matched_train8_g4' or
        value.get('seconds')!=3420 or value.get('arm_seconds')!=1500 or value.get('phase_order')!=['parent','child'] or
        value.get('requested_samples')!=64 or value.get('optimizer_updates')!=0 or value.get('sources')!=sampler.sources() or
        value.get('overhead')!=sampler.OVERHEAD or value.get('verification_pending') is not True or
        value.get('generalization_claim') is not False or set(value.get('arms',{}))!={'parent','child'} or
        sampler.SEED!=SEED or sampler.BUDGET['seed']!=SEED):raise ValueError('Exact fresh64 paired seed/source/budget contract required')
    child=file_sha(a.child_checkpoint)
    if child==sampler.evaluation.PARENT_SHA or file_sha(a.parent_checkpoint)!=sampler.evaluation.PARENT_SHA:
        raise ValueError('Exact24d5 parent and distinct actual proof-RL child required')
    for arm in ('parent','child'):
        admitted=value['arms'][arm];path=getattr(a,arm+'_checkpoint')
        args=SimpleNamespace(prompts=a.prompts,arm=arm,evaluation='stochastic32')
        expected=sampler.evaluation.packet(args,child)
        if (admitted['evaluation']!=expected or admitted['evaluation']['budget']!=sampler.BUDGET or
            admitted['checkpoint_sha256']!=file_sha(path) or admitted['source_sha256']!=sampler.evaluation.source_identity() or
            admitted['model_files_sha256']!=sampler.common.MODEL_FILES_SHA or digest(admitted['model_files'])!=sampler.common.MODEL_FILES_SHA or
            admitted['versions']!=sampler.common.FIRST_VERSIONS or admitted['profile']!=sampler.train.PROFILE or
            admitted['eos_token_ids']!=sampler.common.EOS_IDS or admitted['cpu_environment']!=sampler.evaluation.CPU_ENV or
            admitted['historical_baseline'] is not None or admitted['optimizer_updates']!=0 or
            admitted['generalization_claim'] is not False or admitted['verification_pending'] is not True):
            raise ValueError('Actual paired policy/model/runtime/receipt identity required')
        saved=torch.load(path,map_location='cpu',weights_only=False)
        if sampler.old.checkpoint_state(saved,admitted['model_files'])!=admitted['checkpoint_config_sha256']:
            raise ValueError('Actual collected checkpoint configuration differs from paired receipt')
        del saved
        if admitted['encodings']!=[sampler.common.encode_prompt(tokenizer,t) for t in expected['tasks']]:
            raise ValueError('Actual eight prompt/tokenizer encodings changed')
        expected_files={n:h for n,h in admitted['model_files'].items() if n.endswith('.json') or n in ('tokenizer.model','chat_template.jinja')}
        actual_files={p.name:file_sha(p) for p in a.tokenizer_path.iterdir() if p.is_file() and (p.suffix=='.json' or p.name in ('tokenizer.model','chat_template.jinja'))}
        if actual_files!=expected_files:raise ValueError('Exact complete local tokenizer inventory required')
    for key in ('model_files','model_files_sha256','versions','profile','eos_token_ids','encodings','training_receipt','cpu_environment'):
        if value['arms']['parent'][key]!=value['arms']['child'][key]:raise ValueError('Paired input/runtime/training lineage differs')
    return value


def remote_command(remote,*,arm=None):
    args=[]
    for key in sampler.evaluation.INPUTS:
        value=remote[key]
        if key=='checkpoint' and arm=='parent':value=remote['parent_checkpoint']
        args+=['--'+key.replace('_','-'),value]
    return args+['--baseline-remote-root',remote['baseline_remote_root'],'--baseline-remote-parent',remote['baseline_remote_parent']]


def audit_arm(a,arm,pair,remote,tokenizer):
    import torch
    output=a.generations/arm;admitted=pair['arms'][arm]
    rows=sampler.rows_at(output/'rollouts.jsonl');sampler.validate_rows(admitted,rows,tokenizer)
    worker=load(output/'worker_summary.json');sampler.validate_worker(admitted,rows,worker,output)
    summary=load(output/'summary.json')
    extras=('total_arm_seconds','process_sha256','supervisor_pre_admission_seconds','supervisor_post_admission_reserve_seconds','worker_timeout_seconds')
    if {k:v for k,v in summary.items() if k not in extras}!=worker:raise ValueError('Raw arm supervisor/worker mismatch')
    pre=summary['supervisor_pre_admission_seconds'];post=summary['supervisor_post_admission_reserve_seconds'];seconds=summary['worker_timeout_seconds']
    if type(pre) not in (int,float) or not math.isfinite(pre) or not 0<=pre<1500 or post!=sampler.reserve(pre) or seconds!=1500-pre-post or seconds<=30:
        raise ValueError('Actual measured admission reservation and arm deadline required')
    common.finite_budget(seconds,1500);common.finite_budget(summary['total_arm_seconds'],1500)
    common.finite_budget(worker['elapsed_seconds'],seconds)
    if load(output/'admission.json')!=admitted or load(a.generations/(arm+'-admission.json'))!=admitted:
        raise ValueError('Exact paired/per-arm original admissions required')
    root=Path(remote['output'])/arm
    command=[common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_sumsequence_proof_rl_stochastic.py'),'worker']+remote_command(remote,arm=arm)+[
        '--arm',arm,'--admission',str(root/'admission.json'),'--output',str(root),'--worker-seconds',str(seconds)]
    process=load(output/'process.json');common.audit_process(process,command,remote['evaluation_root'],seconds)
    if summary['process_sha256']!=file_sha(output/'process.json'):raise ValueError('Raw arm process hash mismatch')
    rng={label:torch.load(output/('sampling_generator_'+label+'.pt'),map_location='cpu',weights_only=True) for label in ('before','after')}
    return rows,rng,summary


def prepare(a):
    import torch,transformers
    remote=common.remote_paths(a);training_paths=load(a.training_inputs)
    remote=dict(remote,parent_checkpoint=training_paths['checkpoint'])
    all_tasks=checks.admit_tasks(load(a.prompts));current=checks.admit_controls(a.controls,all_tasks)
    command=[sys.executable,str(Path(checks.__file__).resolve()),'--worker','--prompts',str(a.prompts.resolve()),'--output',str((a.controls/'controls').resolve())]
    common.audit_process(load(a.controls/'process.json'),command,str(ROOT),checks.SECONDS)
    tokenizer=transformers.AutoTokenizer.from_pretrained(a.tokenizer_path,local_files_only=True)
    pair=validate_pair_receipt(a,tokenizer)
    linkage=common.training_linkage(a,pair['arms']['child'],remote)
    ids=[t['id'] for t in pair['arms']['parent']['evaluation']['tasks']]
    tasks=[next(t for t in all_tasks if t['id']==ident) for ident in ids]
    if ids!=[all_tasks[i]['id'] for i in sampler.INDICES] or any(t['split']!='train' for t in tasks):
        raise ValueError('Exact original TRAIN8 indices required')
    arms={};rngs={};summaries={}
    for arm in ('parent','child'):arms[arm],rngs[arm],summaries[arm]=audit_arm(a,arm,pair,remote,tokenizer)
    if not torch.equal(rngs['parent']['before'],rngs['child']['before']):raise ValueError('Actual paired initial sampling RNG differs')
    state=load(a.generations/'summary.json');process=load(a.generations/'cycle_process.json')
    if (state.get('complete') is not True or state.get('phase')!='sampled_pending_verification' or
        state.get('requested_samples')!=64 or state.get('accounted_samples')!=64 or state.get('optimizer_updates')!=0 or
        state.get('verification_pending') is not True or state.get('generalization_claim') is not False or
        state.get('unattempted_sample_ids')!={'parent':[],'child':[]} or
        any(state[arm]!=summaries[arm] for arm in ('parent','child')) or
        state.get('process_sha256')!=file_sha(a.generations/'cycle_process.json')):
        raise ValueError('Complete raw paired64 cycle linkage required')
    command=[common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_sumsequence_proof_rl_stochastic.py'),'_run']+remote_command(remote)+[
        '--admission',str(Path(remote['output'])/'admission.json'),'--output',remote['output'],'--worker-seconds']
    if process['command'][:-1]!=command:raise ValueError('Exact paired owned cycle command required')
    seconds=float(process['command'][-1]);common.finite_budget(seconds,3420)
    common.audit_process(process,command+[process['command'][-1]],remote['evaluation_root'],seconds)
    common.finite_budget(state['elapsed_seconds'],seconds);common.finite_budget(state['total_seconds'],3420)
    return all_tasks,tasks,arms,current,linkage


def identity(a,all_tasks):
    paths={}
    for key in LOCAL_PATHS:
        path=getattr(a,key)
        for item in sorted(path.rglob('*')) if path.is_dir() else [path]:
            if item.is_file():paths[str(item.resolve())]=file_sha(item)
    return dict(verifier=checks.identity(all_tasks),sources={n:file_sha(ROOT/n) for n in SOURCES},files=paths,
        seed=SEED,scope='Fresh seed20261003 only; authentic target receipt and local artifact/raw decoder audit; no remote model admission rerun')


def group_result(rows,field):
    values=[r[field] for r in rows]
    if len(values)!=4 or any(v is not None and (type(v) is not int or v not in (0,1)) for v in values):
        raise ValueError('Exactly four binary-or-unknown outcomes required')
    full=all(v is not None for v in values)
    mean=sum(values)/4 if full else None
    variance=sum((v-mean)**2 for v in values)/4 if full else None
    return dict(sample0=values[0],pass_at4=1 if 1 in values else 0 if full else None,
        complete_group=full,variance=variance,nonzero_variance=bool(full and variance>0),
        exclusion=None if full and variance>0 else 'zero_variance' if full else 'unknown_or_incomplete',values=values)


def summarize(rows,tasks,complete):
    result=dict(complete=complete,seed=SEED,requested_per_arm=32,requested_tasks=8,samples_per_task=4,
        training_authorized=False,proof_reward_export=False,arms={},paired={},
        scope='Fresh matched full-vocabulary T1 seed20261003 TRAIN8/G4; sample0 is stochastic, not greedy; no pooling with training seed20261002 or prior runs')
    for arm in ('parent','child'):
        selected=[r for r in rows if r['arm']==arm];groups={}
        for task in tasks:
            group=[r for r in selected if r['task_id']==task['id']]
            groups[task['id']]={field:group_result(group,field) for field in ('sany','proof')}
            hashes=[r['token_ids_sha256'] for r in group if r.get('token_ids_sha256') is not None]
            groups[task['id']]['duplicate_samples']=len(hashes)-len(set(hashes))
        hashes=[r['token_ids_sha256'] for r in selected if r.get('token_ids_sha256') is not None]
        result['arms'][arm]=dict(requested_samples=32,accounted_samples=len(selected),
            sany_pass=sum(r['sany']==1 for r in selected),proof_pass=sum(r['proof']==1 for r in selected),
            sany_unknown=sum(r['sany'] is None for r in selected),proof_unknown=sum(r['proof'] is None for r in selected),
            token_caps=sum(r['finish_reason']=='token_limit' for r in selected),generation_timeouts=sum(r['finish_reason']=='time_limit' for r in selected),
            generated_samples=len(hashes),distinct_token_outputs=len(set(hashes)),duplicate_samples=len(hashes)-len(set(hashes)),
            tasks=groups,**{field:dict(sample0_pass_tasks=sum(g[field]['sample0']==1 for g in groups.values()),
                pass_at4_tasks=sum(g[field]['pass_at4']==1 for g in groups.values()),
                pass_at4_unknown_tasks=sum(g[field]['pass_at4'] is None for g in groups.values()),
                complete_groups=sum(g[field]['complete_group'] for g in groups.values()),
                nonzero_variance_groups=sum(g[field]['nonzero_variance'] for g in groups.values())) for field in ('sany','proof')})
    for field in ('sany','proof'):
        result['paired'][field]={}
        for metric in ('sample0','pass_at4'):
            groups={name:[] for name in ('gains','losses','unknown','unchanged')}
            for task in tasks:
                left=result['arms']['parent']['tasks'][task['id']][field][metric]
                right=result['arms']['child']['tasks'][task['id']][field][metric]
                category='unknown' if left is None or right is None else 'gains' if right>left else 'losses' if right<left else 'unchanged'
                groups[category].append(task['id'])
            result['paired'][field][metric]=groups
    return result


def evaluate(tasks,arms,current,output,*,checker=checks.check,clock=time.monotonic):
    keys=[(t['id'],i) for t in tasks for i in range(4)]
    if len(tasks)!=8 or set(arms)!={'parent','child'} or any([(r['task_id'],r['attempt']) for r in arms[arm]]!=keys for arm in arms):
        raise ValueError('Exact paired ordered TRAIN8/G4 required')
    rows=[dict(arm=arm,task_id=r['task_id'],sample_id=r['sample_id'],attempt=r['attempt'],split='train',
        seed=SEED,policy_sha256=r['policy_sha256'],finish_reason=r.get('finish_reason',r['status']),
        token_ids_sha256=r.get('token_ids_sha256'),raw_row_sha256=digest(r),sany=None,proof=None,status='unattempted',evidence=None)
        for arm in ('parent','child') for r in arms[arm]]
    output=Path(output);dump(output/'rows.json',rows);complete=True
    for arm_index,arm in enumerate(('parent','child')):
        started=clock()
        for index,raw in enumerate(arms[arm]):
            row=rows[arm_index*32+index];task=tasks[index//4]
            if raw.get('finish_reason')!='eos':row['status']='unmeasured_generation'
            elif clock()-started>SECONDS_PER_ARM-61:row['status']='unmeasured_budget';complete=False
            else:
                value=checker(task,raw['raw_reply'],output/'checks'/arm/raw['sample_id'],current)
                row.update(sany=value['sany'],proof=value['proof'],status=value['status'],evidence=value)
            dump(output/'rows.json',rows);dump(output/'summary.json',summarize(rows,tasks,False))
        if clock()-started>SECONDS_PER_ARM:complete=False
    return rows,summarize(rows,tasks,complete)


def audit_rows(tasks,arms,rows,current,output):
    if len(rows)!=64:raise ValueError('Every requested stochastic result required')
    for ai,arm in enumerate(('parent','child')):
        for index,raw in enumerate(arms[arm]):
            row=rows[ai*32+index];task=tasks[index//4]
            if (row['arm']!=arm or row['sample_id']!=raw['sample_id'] or row['task_id']!=task['id'] or
                row['attempt']!=raw['attempt'] or row['policy_sha256']!=raw['policy_sha256'] or row['raw_row_sha256']!=digest(raw) or
                row['seed']!=SEED or row['token_ids_sha256']!=raw.get('token_ids_sha256') or
                row['finish_reason']!=raw.get('finish_reason',raw['status'])):raise ValueError('Exact stochastic raw row provenance required')
            if raw.get('finish_reason')!='eos' or row['status']=='unmeasured_budget':
                if row['sany'] is not None or row['proof'] is not None or row['evidence'] is not None:raise ValueError('Unknown/capped sample was measured')
                continue
            value=row['evidence'];extraction=checks.extract(task,raw['raw_reply'])
            if value is None or value['extraction']!=extraction or value['raw_reply_sha256']!=sha(raw['raw_reply'].encode()):raise ValueError('Exact stochastic extraction required')
            if extraction['fragment'] is None:
                if any(value[k]!=v for k,v in dict(sany=0,proof=0,status='model_extraction',evidence=None).items()):raise ValueError('Exact extraction rejection required')
            else:
                checks.audit_check(task,extraction['fragment'],value['evidence'],Path(output)/'checks'/arm/raw['sample_id'],current)
                if any(value[k]!=value['evidence'][k] for k in ('sany','proof','status')):raise ValueError('Pipeline/raw proof evidence mismatch')
            if any(row[k]!=value[k] for k in ('sany','proof','status')):raise ValueError('Final stochastic classification mismatch')


def verify(a):
    a.output=a.output.resolve()
    for name in LOCAL_PATHS:
        path=getattr(a,name).resolve()
        if path==a.output or path in a.output.parents or a.output in path.parents:raise ValueError('Isolated immutable inputs/output required')
    a.output.mkdir(parents=True,exist_ok=False)
    all_tasks=checks.admit_tasks(load(a.prompts));before=identity(a,all_tasks);dump(a.output/'identity_before.json',before)
    actual,tasks,arms,current,linkage=prepare(a)
    if actual!=all_tasks or identity(a,actual)!=before:raise ValueError('Input identity changed during local admission')
    dump(a.output/'config.json',dict(seed=SEED,seconds_per_arm=SECONDS_PER_ARM,requested_per_arm=32,training_linkage=linkage,
        target_admission_sha256=a.target_admission_sha256,training_authorized=False,proof_reward_export=False,pooling=False,retries=0))
    rows,summary=evaluate(tasks,arms,current,a.output);audit_rows(tasks,arms,rows,current,a.output)
    after=identity(a,actual);dump(a.output/'identity_after.json',after)
    summary.update(identity_stable=before==after,rows_sha256=file_sha(a.output/'rows.json'),training_linkage=linkage)
    summary['complete']=summary['complete'] and before==after;dump(a.output/'summary.json',summary)
    if not summary['complete']:raise ValueError('Stochastic verification incomplete;64 requested outcomes preserved')
    return summary


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in (*LOCAL_PATHS,'output'):p.add_argument('--'+key.replace('_','-'),type=Path,required=True)
    p.add_argument('--target-admission-sha256',required=True);a=p.parse_args();print(json.dumps(verify(a)))


if __name__=='__main__':main()
