"""Exact greedy40 SANY/strict-TLAPS adapters; separate syntax/proof evidence."""
import argparse
import json
from pathlib import Path
import re
import shutil
import sys
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_repair_verify as repair
from tools import proof_token_rl_rewards as bridge
from tools import proof_sumsequence_repair_eval as policy
from tools import proof_sumsequence_policy_verify as seq
from tools.proof_cuda_eval import dump,digest,sha
from tools.proof_cuda_train import file_sha
from tools.proof_whole_packet import checked
from tools.proof_outcome_audit import CONTRACT_REASONS
from tools.proof_breadth26_manifest import wrong_conclusion
from harness import runner,proof_full_fragment_check as full,proof_fragment_check as legacy
from harness.proof_fragment_check import _code
from harness.proof_ladder_check import classify_sany
from harness.proof_owned_process import run_owned,as_runner_tuple
from harness.proof_gen import extract_proof_block

SECONDS=1200
SOURCES=tuple(sorted(set(repair.SOURCES)|set(bridge.SOURCES)|{
    'tools/proof_sumsequence_proof_rl_checks.py'}))


def _validator(task):
    if task['split'] not in ('train','development'):raise ValueError('Exact TRAIN/DEV split required')
    return legacy.validate_fragment if task['split']=='development' else full.validate_fragment


def admit_tasks(packet):
    portable=policy.validate_export(packet)
    old,original=policy.broader.export_tasks();new,fresh=policy.extra.export_tasks()
    if json.loads(packet['original_packet_bytes'])!=old or json.loads(packet['new_packet_bytes'])!=new:
        raise ValueError('Actual admitted source packets differ from portable40')
    tasks=original+fresh
    if [t['id'] for t in tasks]!=[t['id'] for t in portable]:raise ValueError('Exact ordered40 required')
    contexts=repair.contexts(tasks)
    for task,context in zip(tasks,contexts):
        # Metadata errors escape candidate rejection and invalidate admission.
        extracted=extract(task,task['reference_fragment'])
        if extracted['fragment'] is None or extracted['fragment'].strip()!=task['reference_fragment'].strip():
            raise ValueError('Actual40 reference extractor integration failure')
        _validator(task)(task['prefix'],extracted['fragment'],task['suffix'],task['theorem_name'])
    return tasks


def extract(task,raw_reply):
    if task['id'] in policy.broader.TRAIN_IDS+policy.broader.DEV_IDS:
        fragment=extract_proof_block(raw_reply)
        return dict(fragment=fragment,extractor='unchanged-original36-extract_proof_block')
    context=seq.extraction_context(task)
    value=seq.extract(raw_reply,context)
    return dict(value,extractor='unchanged-SumSequence-fenced-context')


def identity(tasks):
    from tools.proof_hierarchical_packet import runtime_identity
    return dict(sany=bridge.identity({t['id']:t for t in tasks}),tlaps=runtime_identity(),
        tasks_sha256=digest(tasks),sources={n:file_sha(ROOT/n) for n in SOURCES},
        semantics='Original36 extraction, original32 whole proof, originalDEV4 legacy repair; SumSequence4 fenced extractor; 30s each SANY/strict-owned check; no proof/TLC equivalence')


def sany_check(task,fragment,work,timeout=30,execute=run_owned):
    work=Path(work).resolve();work.mkdir(parents=True,exist_ok=False)
    started=time.monotonic();candidate=task['prefix']+fragment+task['suffix']
    result=dict(status='unmeasured_unknown',reward=None,workdir=str(work),candidate_sha256=sha(candidate.encode()),
        partial_reward=True,proof_certified=False,reason='')
    dump(work/'input.json',dict(prefix=task['prefix'],fragment=fragment,suffix=task['suffix'],theorem_name=task['theorem_name']))
    try:
        try:name=_validator(task)(task['prefix'],fragment,task['suffix'],task['theorem_name'])
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


def audit_sany(task,fragment,record,current):
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
    name=_validator(task)(task['prefix'],fragment,task['suffix'],task['theorem_name'])
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


def check_fragment(task,fragment,work,current):
    work=Path(work).resolve();work.mkdir(parents=True,exist_ok=False)
    checked(task['source_path'],task['source_sha256'])
    sany=sany_check(task,fragment,work/'sany',30)
    audit_sany(task,fragment,sany,current['sany'])
    proof=None;strict=None;status=sany['status']
    if sany['reward']==1:
        strict=repair.check_original(task,fragment,work/'tlaps',30)
        proof=int(strict['certified']) if strict['measured_model_outcome'] else None
        status=strict['classification']
    elif sany['reward']==0:proof=0
    value=dict(sany=sany['reward'],proof=proof,status=status,sany_evidence=sany,proof_evidence=strict,
        fragment_sha256=sha(fragment.encode()),task_sha256=digest(task))
    checked(task['source_path'],task['source_sha256']);dump(work/'result.json',value)
    audit_check(task,fragment,value,work,current);return value


def check(task,raw_reply,work,current):
    extraction=extract(task,raw_reply)
    if extraction['fragment'] is None:
        return dict(sany=0,proof=0,status='model_extraction',extraction=extraction,
                    raw_reply_sha256=sha(raw_reply.encode()),evidence=None)
    result=check_fragment(task,extraction['fragment'],work,current)
    return dict(sany=result['sany'],proof=result['proof'],status=result['status'],extraction=extraction,
                raw_reply_sha256=sha(raw_reply.encode()),evidence=result)


def audit_check(task,fragment,value,work,current):
    work=Path(work)
    if (json.loads((work/'result.json').read_bytes())!=value or value['fragment_sha256']!=sha(fragment.encode()) or
        value['task_sha256']!=digest(task)):raise ValueError('Exact task/fragment/pipeline result required')
    audit_sany(task,fragment,value['sany_evidence'],current['sany'])
    sany=value['sany_evidence']['reward'];proof=value['proof_evidence']
    if value['sany']!=sany:raise ValueError('SANY pipeline feedback changed')
    if sany!=1:
        if proof is not None or value['proof']!=(0 if sany==0 else None) or value['status']!=value['sany_evidence']['status']:
            raise ValueError('Unknown/rejected SANY cannot become a proof')
        return
    outer=work/'tlaps';payload=dict(task=task,fragment=fragment)
    command=[sys.executable,str(Path(repair.__file__).resolve()),'worker','--input',str(outer/'input.json'),'--output',str(outer/'worker')]
    process=json.loads((outer/'process.json').read_bytes())
    if (proof is None or proof['process']!=process or json.loads((outer/'input.json').read_bytes())!=payload or
        process['command']!=command or process['cwd']!=str(outer)):
        raise ValueError('Exact dedicated strict proof process required')
    rc,_,seconds,timeout=as_runner_tuple(process)
    classification='unmeasured_infrastructure';measured=False;certified=False
    if rc==0 and not timeout and seconds<=30:
        raw=json.loads((outer/'worker/result.json').read_bytes())
        if proof.get('strict')!=raw:raise ValueError('Raw strict result mismatch')
        diagnostic=repair.audit_original(task,fragment,raw)
        classification=diagnostic['classification'];measured=diagnostic['measured_model_outcome']
        certified=classification=='proof_success'
    elif proof.get('strict') is not None:raise ValueError('Incomplete owned process cannot certify')
    if (proof['classification']!=classification or proof['measured_model_outcome']!=measured or
        proof['certified']!=certified or value['proof']!=(int(certified) if measured else None) or value['status']!=classification):
        raise ValueError('Raw strict classification differs from pipeline')


def negative_task(task):
    prefix=task['prefix']
    if task['id'] in ('crdt-type-step','crdt-safety-step'):
        conclusion="TypeOK'" if task['id']=='crdt-type-step' else "Safety'"
        match=re.search(r'=> '+re.escape(conclusion)+r'(?P<space>\s*)\Z',prefix)
        if match is None:raise ValueError('Exact immutable legacy step conclusion required')
        changed=prefix[:match.start()]+'=> FALSE'+match.group('space')
    elif task['id'] in ('crdt-sum-type-proof','crdt-sum-zero-proof'):
        start=prefix.rfind('\nLEMMA '+task['theorem_name']+' ==')
        match=re.search(r'\bPROVE\s+[^\n]+',prefix[start:])
        if start<0 or match is None:raise ValueError('Exact immutable legacy ASSUME/PROVE conclusion required')
        end=start+match.end();begin=start+match.start()
        changed=prefix[:begin]+'PROVE FALSE'+prefix[end:]
    elif 'goal_offsets' not in task:
        seq.extraction_context(task)
        statement=task['statement']
        declaration=re.match(r'\s*(?:THEOREM|LEMMA)\s+'+re.escape(task['theorem_name'])+r'\s*==',statement)
        start=len(prefix)-len(statement)+declaration.end()
        changed=wrong_conclusion(dict(task,goal_offsets=[start,len(prefix)]))
    else:changed=wrong_conclusion(task)
    result=dict(task,prefix=changed)
    _validator(result)(changed,task['reference_fragment'],task['suffix'],task['theorem_name'])
    return result


def intended_negative(task,value):
    record=(value.get('proof_evidence') or {}).get('strict',{});output=record.get('output','')
    if (value['sany']!=1 or record.get('status')!='verifier_reject' or record.get('returncode')!=10 or
        record.get('timed_out') is not False or record.get('certified') is not False or
        re.findall(r'\[ERROR\]:\s+(\d+)/[1-9][0-9]* obligations? failed\.',output)!=['1'] or
        re.search(r'(?i)parse|syntax|unknown operator|not found|exception|cannot find|could not load|segmentation|out of memory',output)):
        return False
    if task['id'] in ('crdt-type-step','crdt-safety-step'):
        antecedent='TypeOK /\\ [Next]_vars' if task['id']=='crdt-type-step' else 'TypeOK /\\ Safety /\\ [Next]_vars'
        return re.search(r'PROVE\s+'+re.escape(antecedent)+r'\s*=>\s*FALSE\s*$',output,re.M) is not None
    return re.search(r'^\s*PROVE\s+FALSE\s*$',output,re.M) is not None


def control_population(tasks):
    return [(t,'reference') for t in tasks]+[(negative_task(tasks[i]),'false_conclusion') for i in (0,32,33,34,35,36)]


def controls(prompts,output):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    tasks=admit_tasks(json.loads(Path(prompts).read_bytes()));before=identity(tasks)
    dump(output/'identity_before.json',before);requested=control_population(tasks)
    rows=[dict(id=t['id'],label=label,status='unattempted',accepted=False) for t,label in requested]
    dump(output/'rows.json',rows);started=time.monotonic()
    dump(output/'config.json',dict(seconds=SECONDS,requested_controls=46,reference_extractor_controls=40,
        sany_seconds=30,strict_seconds=30,prompts_sha256=file_sha(prompts),source_identity=before))
    for index,(task,label) in enumerate(requested):
        if time.monotonic()-started>SECONDS-65:break
        work=output/'checks'/str(index)
        value=check_fragment(task,task['reference_fragment'],work,before)
        accepted=value['sany']==1 and (value['proof']==1 if label=='reference' else intended_negative(task,value))
        rows[index].update(task=task,status=value['status'],result=value,accepted=accepted)
        dump(output/'rows.json',rows)
    after=identity(tasks);dump(output/'identity_after.json',after)
    elapsed=time.monotonic()-started
    summary=dict(complete=before==after and all(r['accepted'] for r in rows) and elapsed<=SECONDS,
        requested_controls=46,accounted_controls=len(rows),attempted_controls=sum('result' in r for r in rows),
        accepted_controls=sum(r['accepted'] for r in rows),reference_extractor_controls=40,
        unknown_controls=sum('result' not in r or r['result']['proof'] is None for r in rows),
        elapsed_seconds=elapsed,rows_sha256=file_sha(output/'rows.json'))
    dump(output/'summary.json',summary)
    if not summary['complete']:raise ValueError('Full greedy40 checker controls not admitted')
    return summary


def admit_controls(directory,tasks):
    directory=Path(directory).resolve();work=directory/'controls';current=identity(tasks)
    rows=json.loads((work/'rows.json').read_bytes());summary=json.loads((work/'summary.json').read_bytes())
    process=json.loads((directory/'process.json').read_bytes());rc,_,seconds,timeout=as_runner_tuple(process)
    if (rc!=0 or timeout or not 0<seconds<=SECONDS or
        summary.get('complete') is not True or summary.get('requested_controls')!=46 or
        summary.get('accounted_controls')!=46 or summary.get('attempted_controls')!=46 or
        summary.get('accepted_controls')!=46 or summary.get('reference_extractor_controls')!=40 or
        summary.get('unknown_controls')!=0 or summary.get('rows_sha256')!=file_sha(work/'rows.json') or
        json.loads((work/'identity_before.json').read_bytes())!=current or
        json.loads((work/'identity_after.json').read_bytes())!=current or len(rows)!=46):
        raise ValueError('Complete current owned46 controls required')
    expected=control_population(tasks)
    for index,(row,(task,label)) in enumerate(zip(rows,expected)):
        if row.get('id')!=task['id'] or row.get('label')!=label or row.get('task')!=task:
            raise ValueError('Exact control population/task binding required')
        audit_check(task,task['reference_fragment'],row['result'],work/'checks'/str(index),current)
        value=row['result']
        if row.get('accepted') is not True or value['sany']!=1 or not (value['proof']==1 if label=='reference' else intended_negative(task,value)):
            raise ValueError('Actual positive/intended-negative control result required')
    return current


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--prompts',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True);parser.add_argument('--worker',action='store_true');a=parser.parse_args()
    if a.worker:print(json.dumps(controls(a.prompts,a.output)))
    else:
        a.output=a.output.resolve();a.output.mkdir(parents=True,exist_ok=False)
        command=[sys.executable,str(Path(__file__).resolve()),'--worker','--prompts',str(a.prompts.resolve()),
                 '--output',str(a.output/'controls')]
        process=run_owned(command,ROOT,SECONDS);dump(a.output/'process.json',process)
        rc,_,_,timeout=as_runner_tuple(process)
        if rc!=0 or timeout:raise RuntimeError('Owned control batch incomplete; raw partial rows preserved')
        print((a.output/'controls/summary.json').read_text())


if __name__=='__main__':main()
