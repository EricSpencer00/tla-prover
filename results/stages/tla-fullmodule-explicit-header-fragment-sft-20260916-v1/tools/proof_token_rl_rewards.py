"""Local exact-byte SANY-partial reward bridge; never a proof-success claim."""
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

from harness import runner
from harness.proof_full_fragment_check import validate_fragment
from harness.proof_fragment_check import _code
from harness.proof_ladder_check import classify_sany
from harness.proof_owned_process import run_owned,as_runner_tuple
from tools.proof_outcome_audit import CONTRACT_REASONS
from tools.proof_token_rl_packet import load_requests,validate_rollouts,sha,digest,canonical_bytes,POLICY_SHA
from tools.proof_fenced_extract import extract
from tools.proof_cuda_eval import encode_prompt,decode_reply
from tools.proof_whole_packet import TOKENIZER,TOKENIZER_HASHES,checked

ROOT=Path(__file__).resolve().parents[1]
REQUEST_SHA='fa56d5234e710ec646ab4ba2fc3e5771dc699780ea4f05a4da3763fdafb7ebf5'
UNDEFINED='CodexUndefinedControlFact_731946'
BROADER=ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json'
SOURCES=('tools/proof_token_rl_rewards.py','tools/proof_token_rl_packet.py',
 'tools/proof_fenced_extract.py','tools/proof_cuda_eval.py','tools/proof_broader_packet.py',
 'tools/proof_whole_packet.py','harness/proof_owned_process.py','harness/proof_ladder_check.py',
 'harness/proof_full_fragment_check.py','harness/proof_fragment_check.py','harness/runner.py',
 'tools/proof_outcome_audit.py')


def dump(path,value):Path(path).write_bytes(canonical_bytes(value)+b'\n')


def prepare(requests):
    from tools.proof_broader_packet import export_tasks
    from transformers import AutoTokenizer
    packet=load_requests(Path(requests).read_bytes(),REQUEST_SHA,broader_raw=BROADER.read_bytes())
    if packet['reward_stage']!='sany_partial':raise ValueError('Only explicit partial SANY reward supported')
    exported,all_tasks=export_tasks()
    if (json.dumps(exported,indent=2)+'\n').encode()!=BROADER.read_bytes():raise ValueError('Exact controlled TRAIN export required')
    selected={t['id']:t for t in all_tasks if t['id'] in {r['id'] for r in packet['tasks']}}
    if len(selected)!=8 or any(t['split']!='train' for t in selected.values()):raise ValueError('TRAIN8 only')
    for name,h in TOKENIZER_HASHES.items():checked(TOKENIZER/name,h)
    tokenizer=AutoTokenizer.from_pretrained(TOKENIZER,local_files_only=True)
    return packet,selected,tokenizer


def identity(tasks):
    if Path(runner.CLASSPATH).resolve()!=Path(runner.TLA2TOOLS).resolve():raise ValueError('Unattested SANY classpath')
    java=shutil.which('java')
    if not java:raise ValueError('Java unavailable')
    version=subprocess.run([java,'-version'],capture_output=True,text=True,timeout=10,check=True)
    paths={ROOT/p for p in SOURCES}|{Path(java).resolve(),Path(runner.TLA2TOOLS).resolve(),BROADER}
    paths.update(TOKENIZER/name for name in TOKENIZER_HASHES)
    paths.update(p for root in runner.TLA_LIBRARY.split(':') for p in Path(root).rglob('*.tla') if p.is_file())
    for task in tasks.values():
        checked(task['source_path'],task['source_sha256']);paths.add(Path(task['source_path']))
        for p,h in task['dependency_sha256'].items():checked(p,h);paths.add(Path(p))
    return dict(files={str(p):sha(p.read_bytes()) for p in sorted(paths)},
        java=str(Path(java).resolve()),java_version=version.stdout+version.stderr,
        library=runner.TLA_LIBRARY,classpath=runner.CLASSPATH,
        scope='SANY jar, Java launcher/version, configured TLA libraries, source/tokenizer/code; not system dynamic libraries')


def check(task,fragment,work,timeout=30,execute=run_owned):
    work=Path(work).resolve();work.mkdir(parents=True,exist_ok=False)
    started=time.monotonic();candidate=task['prefix']+fragment+task['suffix']
    result=dict(status='unmeasured_unknown',reward=None,workdir=str(work),candidate_sha256=sha(candidate.encode()),
        partial_reward=True,proof_certified=False,reason='')
    dump(work/'input.json',dict(prefix=task['prefix'],fragment=fragment,suffix=task['suffix'],theorem_name=task['theorem_name']))
    try:
        try:name=validate_fragment(task['prefix'],fragment,task['suffix'],task['theorem_name'])
        except ValueError as exc:
            reason=str(exc);result.update(status='model_contract' if reason in CONTRACT_REASONS else 'unmeasured_contract',
                reward=0 if reason in CONTRACT_REASONS else None,reason=reason)
            return result
        path=work/(name+'.tla');path.write_bytes(candidate.encode());deps={};seen={path.name}
        for source,expected in task['dependency_sha256'].items():
            source=Path(source);raw=checked(source,expected)
            if source.name in seen or source.suffix!='.tla' or re.search(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM)\b',_code(raw.decode())):
                raise ValueError('Untrusted or duplicate dependency')
            seen.add(source.name);(work/source.name).write_bytes(raw);deps[source.name]=expected
        java=shutil.which('java')
        if not java:raise OSError('Java unavailable')
        if Path(runner.CLASSPATH).resolve()!=Path(runner.TLA2TOOLS).resolve():raise ValueError('Unattested SANY classpath')
        tmp=work/'jtmp';tmp.mkdir()
        command=[str(Path(java).resolve()),'-Djava.io.tmpdir='+str(tmp),'-DTLA-Library='+runner.TLA_LIBRARY,
            '-cp',runner.CLASSPATH,'tla2sany.SANY',path.name]
        remaining=timeout-(time.monotonic()-started)
        if remaining<=0:result['status']='unmeasured_budget';return result
        evidence=execute(command,work,remaining)
        dump(work/'process.json',evidence)
        rc,out,_,timed_out=as_runner_tuple(evidence)
        (work/'sany.log').write_text(out)
        if json.loads((work/'input.json').read_bytes())!=dict(prefix=task['prefix'],fragment=fragment,suffix=task['suffix'],theorem_name=task['theorem_name']):
            raise ValueError('Raw input changed')
        if path.read_bytes()!=candidate.encode() or any(sha((work/n).read_bytes())!=h for n,h in deps.items()):
            raise ValueError('Checked source bytes changed')
        status=classify_sany(rc,out,timed_out,name)
        if time.monotonic()-started>timeout:status='unmeasured_budget'
        result.update(status=status,reward=1 if status=='pass' else 0 if status=='model_sany_reject' else None,
            command=command,returncode=rc,output=out,process=evidence,dependency_sha256=deps)
    except (OSError,ValueError) as exc:result.update(status='unmeasured_infrastructure',reward=None,reason=str(exc))
    except Exception as exc:result.update(status='unmeasured_checker',reward=None,reason=type(exc).__name__+': '+str(exc))
    finally:
        result['seconds']=time.monotonic()-started;dump(work/'result.json',result)
    return result


def audit_check(task,fragment,record,current):
    work=Path(record['workdir']);saved=json.loads((work/'result.json').read_bytes())
    if {k:v for k,v in record.items() if k not in ('task_id','control')}!=saved:raise ValueError('Saved reward check changed')
    inp=dict(prefix=task['prefix'],fragment=fragment,suffix=task['suffix'],theorem_name=task['theorem_name'])
    if json.loads((work/'input.json').read_bytes())!=inp:raise ValueError('Immutable check input changed')
    candidate=task['prefix']+fragment+task['suffix']
    if record['candidate_sha256']!=sha(candidate.encode()):raise ValueError('Candidate hash changed')
    if record.get('command') is None:
        if record.get('reward') is not None and not(record['status']=='model_contract' and record['reward']==0 and record['reason'] in CONTRACT_REASONS):
            raise ValueError('Unsupported command-free reward')
        return True
    name=validate_fragment(task['prefix'],fragment,task['suffix'],task['theorem_name'])
    if (work/(name+'.tla')).read_bytes()!=candidate.encode():raise ValueError('Checked candidate changed')
    deps={Path(p).name:h for p,h in task['dependency_sha256'].items()}
    if record['dependency_sha256']!=deps:raise ValueError('Checked dependency inventory changed')
    for dep,h in deps.items():checked(work/dep,h)
    command=[current['java'],'-Djava.io.tmpdir='+str(work/'jtmp'),'-DTLA-Library='+current['library'],
        '-cp',current['classpath'],'tla2sany.SANY',name+'.tla']
    process=record['process']
    if record['command']!=command or process['command']!=command or Path(process['cwd']).resolve()!=work.resolve():
        raise ValueError('SANY command not bound to attested runtime')
    if json.loads((work/'process.json').read_bytes())!=process:raise ValueError('Raw process evidence changed')
    rc,out,_,timed_out=as_runner_tuple(process)
    if (work/'sany.log').read_text()!=out or record['output']!=out or record['returncode']!=rc:
        raise ValueError('Raw SANY outcome changed')
    status=classify_sany(rc,out,timed_out,name)
    if record['status']=='unmeasured_budget':
        if record['reward'] is not None:raise ValueError('Late check rewarded')
    elif record['status']!=status or record['reward']!=(1 if status=='pass' else 0 if status=='model_sany_reject' else None):
        raise ValueError('SANY reward classification mismatch')
    return True


def admit_controls(directory,packet,tasks,current):
    directory=Path(directory);summary=json.loads((directory/'summary.json').read_bytes())
    config=json.loads((directory/'config.json').read_bytes());raw=(directory/'rows.json').read_bytes();rows=json.loads(raw)
    if (summary.get('complete') is not True or summary.get('requested_controls')!=16 or summary.get('accounted_controls')!=16 or
        summary.get('correct_controls')!=16 or summary.get('partial_sany_only') is not True or
        sha(raw)!=summary.get('rows_sha256') or config.get('requests_sha256')!=REQUEST_SHA or config.get('timeout')!=30 or
        current!=json.loads((directory/'identity_before.json').read_bytes()) or current!=json.loads((directory/'identity_after.json').read_bytes()) or len(rows)!=16):
        raise ValueError('Complete current16 SANY controls required')
    for i,prompt in enumerate(packet['tasks']):
        task=tasks[prompt['id']]
        for row,label,fragment in zip(rows[2*i:2*i+2],('reference','undefined_fact'),(task['reference_fragment'],'BY '+UNDEFINED)):
            if row.get('task_id')!=task['id'] or row.get('control')!=label:raise ValueError('Exact ordered control population required')
            audit_check(task,fragment,row,current)
            if row['status']!=('pass' if label=='reference' else 'model_sany_reject') or row['reward']!=(1 if label=='reference' else 0):
                raise ValueError('Control disposition mismatch')
            if label=='undefined_fact' and ("Unknown operator: `"+UNDEFINED+"'" not in row['output'] or not re.search(r'\*\*\* Errors:\s*1\b',row['output'])):
                raise ValueError('Intended single undefined-fact diagnostic required')
    return True


def controls(requests,output):
    packet,tasks,_=prepare(requests);output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    before=identity(tasks);dump(output/'identity_before.json',before);rows=[]
    dump(output/'config.json',dict(requests_sha256=REQUEST_SHA,requested_controls=16,timeout=30,
        partial_sany_only=True,training_executed=False,
        hypothesis='Every fixed TRAIN8 reference parses, while an undefined proof fact is rejected'))
    for task in tasks.values():
        for label,fragment in (('reference',task['reference_fragment']),('undefined_fact','BY '+UNDEFINED)):
            result=check(task,fragment,output/task['id']/label)
            rows.append(dict(result,task_id=task['id'],control=label));dump(output/'rows.json',rows)
    after=identity(tasks);dump(output/'identity_after.json',after)
    complete=before==after and len(rows)==16 and all(r['status']==('pass' if r['control']=='reference' else 'model_sany_reject') for r in rows)
    summary=dict(complete=complete,requested_controls=16,accounted_controls=len(rows),
        correct_controls=sum(r['status']==('pass' if r['control']=='reference' else 'model_sany_reject') for r in rows),
        identity_stable=before==after,rows_sha256=sha((output/'rows.json').read_bytes()),partial_sany_only=True)
    dump(output/'summary.json',summary)
    if complete:
        try:admit_controls(output,packet,tasks,before)
        except Exception as exc:
            summary.update(complete=False,admission_error=str(exc));dump(output/'summary.json',summary)
    return summary


def rewards(requests,rollouts,control_dir,output):
    packet,tasks,tokenizer=prepare(requests);output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    before=identity(tasks);control_dir=Path(control_dir)
    admit_controls(control_dir,packet,tasks,before)
    raw=Path(rollouts).read_bytes();rows=[json.loads(line) for line in raw.splitlines()]
    validate_rollouts(packet,rows);prompts={t['id']:t for t in packet['tasks']};results=[]
    dump(output/'identity_before.json',before);started=time.monotonic()
    for request,row in zip(packet['requests'],rows):
        result={k:request[k] for k in ('sample_id','task_id','prompt_sha256','policy_sha256','split','reward_stage')}
        result.update(finish_reason=row.get('finish_reason',row['status']),reward=None,measured_model_outcome=False,
            reward_eligible=False,status='unmeasured_generation',evidence={})
        if row['status'] in ('generated','generation_time_limit'):
            encoded=encode_prompt(tokenizer,prompts[request['task_id']])
            for key in ('rendered_prompt','rendered_prompt_sha256','input_token_ids','input_token_ids_sha256','input_tokens'):
                if row[key]!=encoded[key]:raise ValueError('Exact prompt tokenization mismatch: '+key)
            if decode_reply(tokenizer,row['token_ids'])!=row['raw_reply']:raise ValueError('Exact output decoding mismatch')
            if row['finish_reason']=='eos':
                task=tasks[request['task_id']];extraction=extract(row['raw_reply'],task)
                result['evidence']['extraction']=extraction
                if extraction.get('fragment') is None:
                    result.update(status='model_extraction',reward=0)
                elif time.monotonic()-started>=1000:
                    result['status']='unmeasured_budget'
                else:
                    verdict=check(task,extraction['fragment'],output/'checks'/request['sample_id'],
                        timeout=min(30,1000-(time.monotonic()-started)))
                    audit_check(task,extraction['fragment'],verdict,before)
                    result.update(status=verdict['status'],reward=verdict['reward']);result['evidence']['sany']=verdict
        measured=result['reward'] is not None
        result.update(measured_model_outcome=measured,reward_eligible=measured)
        results.append(result);dump(output/'reward_rows.json',results)
    after=identity(tasks);dump(output/'identity_after.json',after)
    if before!=after:raise ValueError('Reward runtime changed; no receipt issued')
    reward=dict(schema=1,requests_sha256=REQUEST_SHA,rollouts_sha256=sha(raw),policy_sha256=POLICY_SHA,
        reward_stage='sany_partial',complete=True,rows=results,verifier_identity=before)
    dump(output/'rewards.json',reward)
    receipt=dict(schema=1,rewards_sha256=sha((output/'rewards.json').read_bytes()),requests_sha256=REQUEST_SHA,
        rollouts_sha256=sha(raw),bridge_source_sha256=sha(Path(__file__).read_bytes()),provenance_verified=True)
    dump(output/'rewards.receipt.json',receipt)
    return dict(accounted_samples=32,measured_samples=sum(r['reward'] is not None for r in results),
        positives=sum(r['reward']==1 for r in results),reward_stage='sany_partial',receipt=receipt)


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('mode',choices=('controls','rewards'))
    parser.add_argument('--requests',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--rollouts',type=Path);parser.add_argument('--controls',type=Path)
    args=parser.parse_args()
    result=controls(args.requests,args.output) if args.mode=='controls' else rewards(args.requests,args.rollouts,args.controls,args.output)
    print(json.dumps(result))
    if args.mode=='controls' and not result['complete']:raise SystemExit(1)


if __name__=='__main__':main()
