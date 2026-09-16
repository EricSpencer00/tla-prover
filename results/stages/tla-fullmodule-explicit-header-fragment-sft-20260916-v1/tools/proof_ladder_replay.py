#!/usr/bin/env python3
"""Versioned SANY/TLAPS replay of the same 28 frozen model outputs; no training."""
import argparse
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_fresh_replay as original
from tools import proof_ladder_controls as controls
from harness import proof_ladder_check as ladder
from tools.proof_outcome_audit import classify_outcome
from tools.proof_cuda_eval import dump, digest, sha

CONTROLS = ROOT/'results/runs/proof-ladder-controls-20260906-v1'
CONTROL_ROWS_SHA = '485f8b5b679dbb44ae755d2df549e54f93bee154ae9433497670f2e0c940173a'
BUDGET = dict(requested_tasks_per_arm=14, arms=2, requested_checks=28, seconds=1000, timeout=30)
SOURCES = ('tools/proof_ladder_replay.py', 'tools/proof_ladder_controls.py',
           'harness/proof_ladder_check.py', 'tools/proof_fresh_replay.py',
           'tools/proof_outcome_audit.py')


def audit_record(task, fragment, record, runtime):
    """Re-attest saved ladder and nested strict records without executing either checker."""
    work = Path(record['workdir'])
    saved = json.loads((work/'result.json').read_bytes())
    # Control ledgers add these three fields to an otherwise exact checker record.
    if {k: v for k, v in record.items() if k not in ('id', 'control', 'training_authorized')} != saved:
        raise ValueError('Saved ladder result mismatch')
    expected = sha((task['prefix']+fragment+task['suffix']).encode())
    if record.get('contract_version') != ladder.VERSION or record.get('sha256') != expected:
        raise ValueError('Ladder contract/candidate mismatch')
    if json.loads((work/'input.json').read_bytes()) != dict(prefix=task['prefix'], fragment=fragment,
            suffix=task['suffix'], theorem_name=task['theorem_name'], contract_version=ladder.VERSION):
        raise ValueError('Ladder immutable input mismatch')
    sany = record['sany']
    if (work/'sany.log').read_text() != sany['output']:
        raise ValueError('SANY raw log mismatch')
    if sany.get('command') is not None:
        candidate = Path(record['candidate_path'])
        deps = {Path(p).name: h for p, h in task['dependency_sha256'].items()}
        if (candidate.parent.resolve() != work.resolve() or sha(candidate.read_bytes()) != expected
                or record.get('dependency_sha256') != deps):
            raise ValueError('SANY candidate/dependencies mismatch')
        for name, h in deps.items():
            original.checked(work/name, h)
        java = str(Path(sany['java_path']).resolve())
        jar = str(Path(sany['jar_path']).resolve())
        if (runtime['files'].get(java) != sany['java_executable_sha256']
                or runtime['files'].get(jar) != sany['jar_sha256']
                or jar != str(Path(ladder.runner.TLA2TOOLS).resolve())
                or sany.get('library_path') != ladder.runner.TLA_LIBRARY
                or sany['command'] != [java, '-Djava.io.tmpdir='+str(work/'jtmp'),
                    '-DTLA-Library='+ladder.runner.TLA_LIBRARY, '-cp', ladder.runner.CLASSPATH,
                    'tla2sany.SANY', candidate.name]):
            raise ValueError('Unattested SANY executable/JAR/command')
        actual = ladder.classify_sany(sany['returncode'], sany['output'], sany['timed_out'], candidate.stem)
        # Budget can expire after command construction but before SANY runs.
        if not (sany['status'] == 'unmeasured_budget' and sany['returncode'] is None):
            if actual != sany['status']:
                raise ValueError('SANY classification mismatch')
    elif sany['status'] not in ('not_run',):
        raise ValueError('SANY status without command')
    tlaps = record.get('tlaps')
    diagnostic = None
    if tlaps is not None:
        if sany['status'] != 'pass':
            raise ValueError('TLAPS without SANY pass')
        deps = {Path(p).name: h for p, h in task['dependency_sha256'].items()}
        ladder._audit_tlaps(tlaps, task['prefix'], fragment, task['suffix'], task['theorem_name'], deps)
        diagnostic = classify_outcome(tlaps, provenance_verified=True)
        if record.get('tlaps_diagnostic') is not None and record['tlaps_diagnostic'] != diagnostic:
            raise ValueError('Strict diagnostic mismatch')
    timeout = record.get('timeout_seconds'); elapsed = record.get('seconds')
    within_deadline = (type(timeout) in (int, float) and math.isfinite(timeout) and 0 < timeout <= 30
                       and type(elapsed) in (int, float) and math.isfinite(elapsed) and 0 <= elapsed <= timeout)
    positive = (record.get('certified') is True and record.get('status') == 'pass' and within_deadline
                and sany['status'] == 'pass' and diagnostic is not None
                and diagnostic['classification'] == 'proof_success')
    if record.get('certified') is True and not positive:
        raise ValueError('Unsupported ladder certification')
    return dict(certified=positive, sany_status=sany['status'],
                tlaps_classification=None if diagnostic is None else diagnostic['classification'])


def admit_controls(directory=CONTROLS):
    directory = Path(directory)
    rows = json.loads(original.checked(directory/'rows.json', CONTROL_ROWS_SHA))
    selection = json.loads((directory/'selection.json').read_bytes())
    summary = json.loads((directory/'summary.json').read_bytes())
    config = json.loads((directory/'config.json').read_bytes())
    before = json.loads((directory/'identity_before.json').read_bytes())
    after = json.loads((directory/'identity_after.json').read_bytes())
    if (summary.get('status') != 'completed' or summary.get('controls_passed') is not True
            or summary.get('identity_stable') is not True or summary.get('accepted_pairs') != 14
            or summary.get('ledgered_controls') != 28 or summary.get('ledgered_pairs') != 14
            or config.get('contract') != ladder.VERSION or config.get('timeout') != 30
            or config.get('seconds') != 1000
            or config.get('selection_sha256') != controls.selection_digest(selection)
            or before != after or before != controls.identity(selection)):
        raise ValueError('Completed stable current ladder controls required')
    tasks = selection['tasks']
    if len(tasks) != 14 or len({t['id'] for t in tasks}) != 14 or len(rows) != 28:
        raise ValueError('Full14 control population required')
    for index, task in enumerate(tasks):
        pair = rows[index*2:index*2+2]
        for row, label in zip(pair, ('reference', 'wrong_conclusion')):
            if row['id'] != task['id'] or row['control'] != label:
                raise ValueError('Ordered exact control pairs required')
            scoped = dict(task, prefix=task['prefix'] if label == 'reference' else controls.wrong_conclusion(task))
            audit_record(scoped, task['reference_fragment'], row, before)
        if not controls.pair_passes(task, *pair):
            raise ValueError('Ladder reference/FALSE pair failed')
    return dict(runtime=before, task_ids=[t['id'] for t in tasks],
                artifacts={str(directory/p): sha((directory/p).read_bytes()) for p in
                    ('rows.json', 'selection.json', 'summary.json', 'config.json',
                     'identity_before.json', 'identity_after.json', 'outcomes.json')})


def identity(tasks):
    admitted = admit_controls()
    if [t['id'] for t in tasks] != admitted['task_ids']:
        raise ValueError('Replay/control population mismatch')
    return dict(controls=admitted, original=original.identity(tasks),
                code={p: sha((ROOT/p).read_bytes()) for p in SOURCES})


def evaluate(tasks, arms, output, *, checker=ladder.certify_fragment,
             attest=identity, audit=audit_record, clock=time.monotonic):
    output = Path(output)
    if len(tasks) != 14 or len({t['id'] for t in tasks}) != 14 or set(arms) != {'base', 'child'}:
        raise ValueError('Full paired14 population required')
    for rows in arms.values():
        if [r['id'] for r in rows] != [t['id'] for t in tasks]:
            raise ValueError('Ordered full14 extraction ledger required')
    frozen = digest(dict(tasks=tasks, arms=arms))
    started = clock(); before = attest(tasks); results = []
    dump(output/'identity_before.json', before)
    complete = False; stable = False
    def save():
        dump(output/'summary.json', dict(**BUDGET, contract=ladder.VERSION,
            status='completed' if complete else 'running', verification_complete=complete,
            identity_stable=stable, accounted_attempts=len(results), elapsed_seconds=clock()-started,
            post_hoc_replay=True, model_sampling=False, training_authorized=False,
            reward_authorized=False, parameter_updates=0,
            per_arm={arm: dict(requested_tasks=14, accounted_tasks=sum(r['arm'] == arm for r in results),
                certified_tasks=sum(r['arm'] == arm and r['certified'] for r in results) if complete else 0,
                statuses={s: sum(r['arm'] == arm and r['status'] == s for r in results)
                    for s in sorted({r['status'] for r in results if r['arm'] == arm})})
                for arm in ('base', 'child')}))
    save()
    with (output/'rows.jsonl').open('x') as stream:
        for index, task in enumerate(tasks):
            for arm in ('base', 'child'):
                extraction = arms[arm][index]; fragment = extraction.get('fragment')
                result = dict(certified=False, status='extraction_reject', sany=None, tlaps=None)
                evidence = None
                remaining = 1000-(clock()-started)
                if fragment is not None and remaining >= 1:
                    result = checker(task['prefix'], fragment, task['suffix'],
                        theorem_name=task['theorem_name'], dependencies=tuple(map(Path, task['dependencies'])),
                        work_root=output/'checks'/arm/task['id'], timeout=min(30, remaining))
                    evidence = audit(task, fragment, result, before['controls']['runtime'])
                elif fragment is not None:
                    result['status'] = 'unmeasured_budget'
                row = dict(result, id=task['id'], arm=arm, extraction=extraction,
                    replay_audit=evidence, training_authorized=False, reward_authorized=False)
                row['certified'] = bool(evidence and evidence['certified'])
                results.append(row); stream.write(json.dumps(row)+'\n'); stream.flush(); save()
    after = attest(tasks); dump(output/'identity_after.json', after)
    stable = before == after and frozen == digest(dict(tasks=tasks, arms=arms))
    complete = stable and len(results) == 28; save()
    if not stable:
        raise ValueError('Replay identity/input drift; no verified result')
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    tasks, arms = original.prepare()
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output/'extractions.json', arms)
    dump(args.output/'config.json', dict(**BUDGET, contract=ladder.VERSION,
        control_rows_sha256=CONTROL_ROWS_SHA, original_generation_sha256=original.GENERATION_SHA,
        hypothesis='Apply independently controlled SANY-first gate to exactly the same paired generated proofs',
        stop='28 accounted attempts or 1000 seconds; no repairs, retries, or changed targets',
        model_sampling=False, training_authorized=False, reward_authorized=False,
        frozen_sha256=digest(dict(tasks=tasks, arms=arms))))
    for name in SOURCES:
        dest = args.output/'code'/name; dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes((ROOT/name).read_bytes())
    try:
        evaluate(tasks, arms, args.output)
    except BaseException as exc:
        dump(args.output/'failure.json', dict(error=repr(exc), verification_complete=False))
        raise


if __name__ == '__main__':
    main()
