#!/usr/bin/env python3
"""Discovery-only SumSequence prerequisite controls; never training admission.

Run in a dedicated single-threaded process. The four discovered targets remain
accounted for even when prerequisite checks fail. No original file is modified.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness import runner
from harness.proof_full_fragment_check import certify_fragment, validate_fragment
from harness.proof_owned_process import run_owned, as_runner_tuple
from tools.proof_hierarchical_packet import runtime_identity

SOURCE = ROOT / 'tools/tlaplus-examples/specifications/LoopInvariance/SumSequence.tla'
SOURCE_SHA = 'aad92f983376e998d9bb628b7d8804ef3aff27d598e0f0be098138a2c134d296'
COMMIT = '47b0e2cc0268836b89f5ce451f38e5df5f1cf773'
FRONT_SOURCE = ROOT / 'tools/community-modules/SequencesExt.tla'
FRONT_SHA = '30bd6e158e6683a409e0a0cf9e3627aabc7002de034a5aef63922cf3e5c9dce1'
FRONT = 'Front(s) == \n  SubSeq(s, 1, Len(s)-1)\n'
SPANS = (('FrontDef',174,176,176), ('Lemma2',323,329,342),
         ('Lemma3',357,360,390), ('Lemma4',399,400,433))
SOURCES = ('tools/proof_sumsequence_controls.py', 'harness/proof_full_fragment_check.py',
           'harness/proof_fragment_check.py', 'harness/proof_owned_process.py',
           'harness/runner.py', 'tools/proof_hierarchical_packet.py')


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def file_identity():
    return {str(p): digest(p.read_bytes()) for p in
            [SOURCE, FRONT_SOURCE, *(ROOT / n for n in SOURCES)]}


def discover():
    raw = SOURCE.read_bytes()
    if digest(raw) != SOURCE_SHA or digest(FRONT_SOURCE.read_bytes()) != FRONT_SHA:
        raise ValueError('Frozen discovery source changed')
    blob = subprocess.check_output(['git', '-C', str(ROOT / 'tools/tlaplus-examples'),
        'show', COMMIT + ':specifications/LoopInvariance/SumSequence.tla'], timeout=10)
    if blob != raw:
        raise ValueError('Source differs from pinned commit')
    if ''.join(FRONT_SOURCE.read_text().splitlines(keepends=True)[229:231]) != FRONT:
        raise ValueError('Resolved Front definition changed')
    lines = raw.decode().splitlines(keepends=True)
    base = '---- MODULE SumSequence ----\nEXTENDS Integers, Sequences, TLAPS\n' + FRONT + '\n'
    front_proof = ''.join(lines[173:176])
    tasks = []
    for index, (name, begin, proof, end) in enumerate(SPANS):
        statement = ''.join(lines[begin-1:proof-1])
        fragment = ''.join(lines[proof-1:end])
        context = base + (front_proof + '\n' if name == 'Lemma2' else '')
        task = dict(id=name, statement=statement, reference_fragment=fragment,
            source_lines=[begin,proof,end], control_eligible=index < 2,
            prerequisite_status=['independent', 'requires_FrontDef_pair',
                'pending_verified_Lemma2a_and_FrontDef',
                'pending_verified_Lemma1_Lemma2_and_induction_trust'][index])
        if index < 2:
            task.update(prefix=context + statement, suffix='\n====\n', theorem_name=name,
                        negative_prefix=context + re.sub(r'==[\s\S]*', '== FALSE\n', statement, count=1))
            validate_fragment(task['prefix'], fragment, task['suffix'], name)
            validate_fragment(task['negative_prefix'], fragment, task['suffix'], name)
        tasks.append(task)
    return dict(discovered=4, tasks=tasks, source_sha256=SOURCE_SHA, source_commit=COMMIT,
        front_source_sha256=FRONT_SHA, front_definition_sha256=digest(FRONT.encode()),
        training_authorized=False, decontamination='pending full current exclusion audit',
        scope='Prerequisite reconstruction discovery; no training admission or gate claim')


def intended_false_failure(result):
    """Recognize the sole FALSE obligation; caller also audits complete execution.

    TLAPS prints visible definitions as ASSUME entries even for a closed FALSE
    target. Accept that diagnostic sequent without accepting an unrelated failed
    goal, a second diagnostic, or a verifier infrastructure failure.
    """
    text = result.get('output', '')
    counts = re.findall(r'\[ERROR\]:\s+([0-9]+)/([1-9][0-9]*) obligations? failed\.', text)
    diagnostics = re.findall(r'\[ERROR\]: Could not prove or check:\n'
        r'((?:[ \t]+[^\n]*\n)+)', text)
    if len(diagnostics) != 1:
        return False
    body = diagnostics[0].strip()
    false_goal = body == 'FALSE' or (
        body.startswith('ASSUME ') and
        len(re.findall(r'(?m)^\s*PROVE\b', body)) == 1 and
        re.search(r'(?m)^\s*PROVE\s+FALSE\s*\Z', body) is not None)
    return (result.get('status') == 'verifier_reject' and result.get('timed_out') is False
        and result.get('certified') is False and result.get('returncode') == 10
        and len(counts) == 1 and counts[0][0] == '1' and false_goal
        and not re.search(r'parse|syntax|unknown operator|undefined|exception|cannot find|not found|'
            r'could not load|segmentation|out of memory', text, re.I))


def controls(output, *, execute=run_owned, identify=runtime_identity, clock=time.monotonic):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    started = clock()
    manifest = discover()
    before_files = file_identity()
    before_runtime = identify()
    write(output / 'config.json', dict(manifest=manifest, files=before_files, runtime=before_runtime,
        max_checks=4, timeout_per_check=30, total_seconds=150,
        hypothesis='Independent FrontDef and its closed Lemma2 extension verify without unchecked source lemmas',
        stop='At most four controls, no retries; Lemma2 requires both FrontDef controls',
        containment='Owned ancestry polling, not kernel containment; 0.5-second cleanup reserve',
        training_authorized=False))
    original = runner.run_cmd
    records = {}
    rows = []

    def guarded(cmd, cwd, timeout):
        work = Path(cwd).resolve()
        if (not work.is_relative_to(output / 'checks') or timeout != 30 or work in records
                or len(records) >= 4 or '--strict' not in cmd or '--nofp' not in cmd
                or file_identity() != before_files or clock()-started > 119):
            raise ValueError('Control scope, identity, or remaining budget violated')
        process = execute(cmd, work, timeout)
        record = dict(command=list(cmd), cwd=str(work), timeout=timeout, process=process)
        write(work / 'process.json', record)
        records[work] = record
        if process['command'] != list(cmd) or process['cwd'] != str(work):
            raise ValueError('Owned process identity mismatch')
        return as_runner_tuple(process)

    try:
        runner.run_cmd = guarded
        for task in manifest['tasks'][:2]:
            if task['id'] == 'Lemma2' and not all(r['accepted'] for r in rows):
                break
            pair = []
            for label in ('reference', 'false_conclusion'):
                if clock()-started > 119:
                    break
                prefix = task['prefix'] if label == 'reference' else task['negative_prefix']
                result = certify_fragment(prefix, task['reference_fragment'], task['suffix'],
                    theorem_name=task['id'], work_root=output / 'checks' / task['id'] / label, timeout=30)
                work = Path(result['workdir']).resolve()
                complete = False
                if 'returncode' in result:
                    record = records[work]
                    tup = as_runner_tuple(record['process'])
                    if (tuple(result[k] for k in ('returncode','output','seconds','timed_out')) != tup
                            or result['command'] != record['command']
                            or json.loads((work / 'process.json').read_text()) != record
                            or json.loads((work / 'result.json').read_text()) != result
                            or json.loads((work / 'input.json').read_text()) != dict(
                                prefix=prefix, fragment=task['reference_fragment'], suffix=task['suffix'],
                                theorem_name=task['id'], contract_version=result['contract_version'])
                            or (work / 'tlapm.log').read_text() != result['output']
                            or Path(result['candidate_path']).read_bytes() !=
                                (prefix + task['reference_fragment'] + task['suffix']).encode()):
                        raise ValueError('Raw checker/process audit mismatch')
                    complete = record['process']['execution_complete'] and not tup[3]
                accepted = bool(complete and (result['certified'] if label == 'reference'
                                             else intended_false_failure(result)))
                row = dict(id=task['id'], control=label, accepted=accepted, result=result)
                rows.append(row); pair.append(row)
                write(output / ('row-' + str(len(rows)) + '.json'), row)
            if len(pair) != 2 or not all(r['accepted'] for r in pair):
                break
        after_runtime = identify()
        after_files = file_identity()
        stable = after_files == before_files and after_runtime == before_runtime
        within_budget = clock()-started <= 150
        write(output / 'summary.json', dict(discovered=4, requested_controls=4,
            attempted_controls=len(rows), accepted_controls=sum(r['accepted'] for r in rows),
            completed_pair_ids=[name for name in ('FrontDef','Lemma2')
                if len([r for r in rows if r['id']==name and r['accepted']]) == 2],
            identity_stable=stable, files_after=after_files, runtime_after=after_runtime, within_budget=within_budget,
            controls_admitted=stable and within_budget and len(rows)==4 and all(r['accepted'] for r in rows),
            pending=['Lemma3 prerequisite closure','Lemma4 prerequisite closure','full decontamination'],
            training_authorized=False, elapsed_seconds=clock()-started))
        if not stable:
            raise ValueError('Control identity drift')
    except BaseException as exc:
        write(output / 'failure.json', dict(error=type(exc).__name__+': '+str(exc),
            controls_admitted=False, training_authorized=False))
        raise
    finally:
        runner.run_cmd = original


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    controls(parser.parse_args().output)


if __name__ == '__main__':
    main()
