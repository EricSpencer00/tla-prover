"""Bounded discovery-only Lemma2a proof alternatives, with unchanged assumptions."""
import argparse
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_sumsequence_controls as base
from harness import runner
from harness.proof_full_fragment_check import certify_fragment, validate_fragment
from harness.proof_owned_process import run_owned, as_runner_tuple

CANDIDATES = (
    ('obvious', 'OBVIOUS\n'),
    ('tail_definition', 'BY DEF Tail\n'),
    ('explicit_extensionality', r'''<1>1. Tail(s) \in Seq(S) /\ [i \in 1..(Len(s) - 1) |-> s[i+1]] \in Seq(S)
  OBVIOUS
<1>2. Len(Tail(s)) = Len([i \in 1..(Len(s) - 1) |-> s[i+1]])
  OBVIOUS
<1>3. \A i \in 1 .. Len(Tail(s)) : Tail(s)[i] = [j \in 1..(Len(s) - 1) |-> s[j+1]][i]
  OBVIOUS
<1>4. QED BY <1>1, <1>2, <1>3
'''))


def task():
    base.discover()  # exact source/commit and definition provenance, no imported claims
    lines = base.SOURCE.read_text().splitlines(keepends=True)
    statement = ''.join(lines[343:346])
    expected = ('LEMMA Lemma2a ==\n'
        '  ASSUME NEW S, NEW s \\in Seq(S), Len(s) > 1\n'
        '  PROVE  Tail(s) = [i \\in 1..(Len(s) - 1) |-> s[i+1]]\n')
    if statement != expected:
        raise ValueError('Exact original Lemma2a statement changed')
    context = '---- MODULE SumSequence ----\nEXTENDS Integers, Sequences, TLAPS\n'
    negative = statement[:statement.index('  PROVE')] + '  PROVE  FALSE\n'
    result = dict(prefix=context+statement, negative_prefix=context+negative,
                  suffix='\n====\n', theorem_name='Lemma2a', statement=statement)
    for _, fragment in CANDIDATES:
        for key in ('prefix', 'negative_prefix'):
            validate_fragment(result[key], fragment, result['suffix'], 'Lemma2a')
    return result


def identity():
    return dict(files=base.file_identity(), own=base.digest(Path(__file__).read_bytes()))


def controls(output, *, execute=run_owned, identify=base.runtime_identity, clock=time.monotonic):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    start = clock()
    spec = task()
    before = identity()
    runtime = identify()
    base.write(output/'config.json', dict(task=spec, candidates=CANDIDATES, identity=before,
        runtime=runtime, max_checks=6, timeout_per_check=30, total_seconds=210,
        hypothesis='The original local DEFINE can be eliminated without changing Lemma2a or adding trusted premises',
        stop='Three ordered proof alternatives and paired FALSE controls, stop at first admitted pair or budget',
        training_authorized=False))
    rows = []
    records = {}
    original = runner.run_cmd

    def guarded(cmd, cwd, timeout):
        work = Path(cwd).resolve()
        if (not work.is_relative_to(output/'checks') or work in records or timeout != 30
                or len(records)>=6 or clock()-start>179 or identity()!=before
                or '--strict' not in cmd or '--nofp' not in cmd):
            raise ValueError('Check scope/identity/budget violated')
        process = execute(cmd, work, timeout)
        if process['command']!=list(cmd) or process['cwd']!=str(work):
            raise ValueError('Owned command identity mismatch')
        records[work] = process
        base.write(work/'process.json', process)
        return as_runner_tuple(process)

    try:
        runner.run_cmd = guarded
        winner = None
        for name, fragment in CANDIDATES:
            pair=[]
            for control in ('reference','false_conclusion'):
                if clock()-start>179:
                    break
                prefix=spec['prefix' if control=='reference' else 'negative_prefix']
                result=certify_fragment(prefix,fragment,spec['suffix'],theorem_name='Lemma2a',
                    work_root=output/'checks'/name/control,timeout=30)
                complete=False
                if 'returncode' in result:
                    work=Path(result['workdir']).resolve()
                    process=records[work]
                    tup=as_runner_tuple(process)
                    if (tuple(result[k] for k in ('returncode','output','seconds','timed_out'))!=tup
                        or result['command']!=process['command']
                        or json.loads((work/'process.json').read_text())!=process
                        or json.loads((work/'result.json').read_text())!=result
                        or json.loads((work/'input.json').read_text())!=dict(prefix=prefix,fragment=fragment,
                            suffix=spec['suffix'],theorem_name='Lemma2a',contract_version=result['contract_version'])
                        or (work/'tlapm.log').read_text()!=result['output']
                        or Path(result['candidate_path']).read_bytes()!=(prefix+fragment+spec['suffix']).encode()):
                        raise ValueError('Raw result/process/candidate audit mismatch')
                    complete=process['execution_complete'] and not tup[3]
                accepted=bool(complete and (result['certified'] if control=='reference'
                                          else base.intended_false_failure(result)))
                row=dict(candidate=name,control=control,accepted=accepted,result=result)
                rows.append(row); pair.append(row)
                base.write(output/f'row-{len(rows)}.json', row)
            if len(pair)==2 and all(r['accepted'] for r in pair):
                winner=name
                break
        after=identity()
        runtime_after=identify()
        stable=before==after and runtime==runtime_after
        elapsed=clock()-start
        base.write(output/'summary.json',dict(attempted_controls=len(rows),max_checks=6,
            accepted_controls=sum(r['accepted'] for r in rows),winner=winner,
            identity_stable=stable,identity_after=after,runtime_after=runtime_after,
            within_budget=elapsed<=210,elapsed_seconds=elapsed,
            controls_admitted=bool(winner and stable and elapsed<=210),training_authorized=False))
        if not stable:
            raise ValueError('Identity drift')
    except BaseException as exc:
        base.write(output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),controls_admitted=False))
        raise
    finally:
        runner.run_cmd=original


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    controls(parser.parse_args().output)
