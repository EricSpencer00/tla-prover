"""Discovery-only exact Lemma3 with independently proved prerequisites inlined."""
import argparse
import json
from pathlib import Path
import re
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_sumsequence_controls as base
from tools import proof_sumsequence_lemma2a as prior
from harness import runner
from harness.proof_full_fragment_check import certify_fragment,validate_fragment
from harness.proof_owned_process import run_owned,as_runner_tuple
from harness.proof_ladder_check import _audit_tlaps


def task():
    discovered=base.discover()['tasks']
    front=discovered[0]
    lemma=discovered[2]
    previous=prior.task()
    context=('---- MODULE SumSequence ----\nEXTENDS Integers, Sequences, TLAPS\n'+base.FRONT+'\n'
        +front['statement']+front['reference_fragment']+'\n'
        +previous['statement']+'OBVIOUS\n\n')
    statement=lemma['statement']
    result=dict(prefix=context+statement,reference_fragment=lemma['reference_fragment'],
        suffix='\n====\n',statement=statement,theorem_name='Lemma3',
        negative_prefix=context+re.sub(r'==[\s\S]*','== FALSE\n',statement,count=1),
        prerequisites=['FrontDef with original proof','Lemma2a with independently checked OBVIOUS'],
        source_sha256=base.SOURCE_SHA)
    for key in ('prefix','negative_prefix'):
        validate_fragment(result[key],result['reference_fragment'],result['suffix'],'Lemma3')
    return result


def identity():
    return dict(base=prior.identity(),sources={str(path):base.digest(path.read_bytes()) for path in
        (Path(__file__),ROOT/'harness/proof_ladder_check.py')})


def controls(output,*,execute=run_owned,identify=base.runtime_identity,clock=time.monotonic):
    output=Path(output).resolve();output.mkdir(parents=True,exist_ok=False)
    start=clock();spec=task();before=identity();runtime=identify()
    base.write(output/'config.json',dict(task=spec,identity=before,runtime=runtime,
        max_checks=2,timeout_per_check=30,total_seconds=90,
        hypothesis='Exact Lemma3 reference closes using only actual proved FrontDef and Lemma2a prerequisites',
        stop='Two controls, no retry, no contract relaxation',training_authorized=False))
    rows=[];records={};original=runner.run_cmd

    def guarded(cmd,cwd,timeout):
        work=Path(cwd).resolve()
        if (not work.is_relative_to(output/'checks') or work in records or timeout!=30
            or len(records)>=2 or clock()-start>59 or identity()!=before
            or '--strict' not in cmd or '--nofp' not in cmd):
            raise ValueError('Check scope/identity/budget violated')
        process=execute(cmd,work,timeout)
        if process['command']!=list(cmd) or process['cwd']!=str(work):
            raise ValueError('Owned command identity mismatch')
        records[work]=process;base.write(work/'process.json',process)
        return as_runner_tuple(process)

    try:
        runner.run_cmd=guarded
        for label in ('reference','false_conclusion'):
            if clock()-start>59:break
            prefix=spec['prefix' if label=='reference' else 'negative_prefix']
            result=certify_fragment(prefix,spec['reference_fragment'],spec['suffix'],
                theorem_name='Lemma3',work_root=output/'checks'/label,timeout=30)
            complete=False
            if 'returncode' in result:
                work=Path(result['workdir']).resolve();process=records[work];tup=as_runner_tuple(process)
                _audit_tlaps(result,prefix,spec['reference_fragment'],spec['suffix'],'Lemma3',{})
                if (tuple(result[k] for k in ('returncode','output','seconds','timed_out'))!=tup
                    or result['command']!=process['command']
                    or json.loads((work/'process.json').read_text())!=process):
                    raise ValueError('Raw process audit mismatch')
                complete=process['execution_complete'] and not tup[3]
            accepted=bool(complete and (result['certified'] if label=='reference'
                                       else base.intended_false_failure(result)))
            row=dict(control=label,accepted=accepted,result=result);rows.append(row)
            base.write(output/f'row-{len(rows)}.json',row)
        after=identity();runtime_after=identify();stable=before==after and runtime==runtime_after
        elapsed=clock()-start
        base.write(output/'summary.json',dict(requested_controls=2,attempted_controls=len(rows),
            accepted_controls=sum(r['accepted'] for r in rows),identity_stable=stable,
            identity_after=after,runtime_after=runtime_after,within_budget=elapsed<=90,
            elapsed_seconds=elapsed,controls_admitted=stable and elapsed<=90 and len(rows)==2
            and all(r['accepted'] for r in rows),training_authorized=False))
        if not stable:raise ValueError('Identity drift')
    except BaseException as exc:
        base.write(output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),controls_admitted=False))
        raise
    finally:
        runner.run_cmd=original


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    controls(parser.parse_args().output)
