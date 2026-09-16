#!/usr/bin/env python3
"""Unchanged broader retention verification with explicit owned-process evidence.

Run in a dedicated, single-threaded process. This scoped adapter is not kernel
containment and is not the historical runner's execution policy. Consume results
only when owned_admission.json says admitted; the inherited summary alone does
not establish this wrapper's admission.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness import runner
from harness.proof_owned_process import run_owned, as_runner_tuple
from tools import proof_cuda_broader_eval as broader

SOURCES = tuple(sorted(set(broader.IMPLEMENTATION) | {
    'tools/proof_broader_owned_verify.py', 'harness/proof_owned_process.py',
    'harness/proof_fragment_check.py', 'harness/proof_full_fragment_check.py',
    'harness/proof_gen.py', 'harness/runner.py', 'tools/proof_hierarchical_packet.py'}))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write(path, value):
    with Path(path).open('x') as stream:
        json.dump(value, stream, indent=2)
        stream.write('\n')


def identity(a):
    paths = [a.prompts, *(a.generations / n for n in
        ('config.json', 'generations.jsonl', 'summary.json'))]
    paths += sorted(p for p in a.tokenizer_path.iterdir() if p.is_file())
    return dict(sources={n: sha(ROOT / n) for n in SOURCES},
                inputs={str(p.resolve()): sha(p) for p in paths})


def audit(output, records, expected):
    rows = [json.loads(line) for line in (output / 'rows.jsonl').read_text().splitlines()]
    summary = json.loads((output / 'summary.json').read_text())
    if [(r['id'], r['split']) for r in rows] != expected or len(rows) != 36:
        raise ValueError('Exact ordered 32 TRAIN + 4 DEV accounting required')
    if not summary.get('verification_complete') or summary.get('requested_tasks') != 36:
        raise ValueError('Inherited verification incomplete')
    used = set()
    for row in rows:
        if 'returncode' not in row:
            if row.get('certified') or 'command' in row:
                raise ValueError('Checked row missing execution result')
            continue
        work = Path(row['workdir']).resolve()
        if work in used or work not in records:
            raise ValueError('Missing or duplicate process evidence')
        used.add(work)
        record = json.loads((work / 'process.json').read_text())
        if record != records[work]:
            raise ValueError('Raw process evidence changed')
        rc, text, seconds, timed_out = as_runner_tuple(record['process'])
        if (row['command'] != record['command'] or str(work) != record['cwd'] or
                (row['returncode'], row['output'], row['seconds'], row['timed_out']) !=
                (rc, text, seconds, timed_out)):
            raise ValueError('Checked row disagrees with process evidence')
        if (work / 'tlapm.log').read_text() != text or json.loads((work / 'result.json').read_text()) != {
                k: v for k, v in row.items() if k not in {
                    'id', 'split', 'fragment', 'raw_reply_sha256', 'fragment_contract'}}:
            raise ValueError('Raw checker result disagrees with ledger')
        if row.get('certified') and (timed_out or not record['process']['execution_complete']):
            raise ValueError('Incomplete execution cannot certify a proof')
    if used != set(records):
        raise ValueError('Orphan process evidence')
    return dict(requested_tasks=36, accounted_tasks=len(rows), checked_tasks=len(used),
                certified_tasks=sum(bool(r['certified']) for r in rows))


def verify(a):
    a.output = a.output.resolve()
    a.output.mkdir(parents=True, exist_ok=False)
    before = identity(a)
    expected = [(t['id'], t['split']) for t in broader.export_tasks()[1]]
    if len(expected) != 36 or [s for _, s in expected] != ['train'] * 32 + ['development'] * 4:
        raise ValueError('Original broader population required')
    write(a.output / 'owned_config.json', dict(schema=1, identity=before,
        requested_tasks=36, timeout_per_module=30, cleanup_reserve_seconds=.5,
        execution_policy='proof_owned_process.run_owned, as_runner_tuple',
        scope='Scoped runner.run_cmd replacement in this dedicated process only; inherited runtime identity describes verifier files, not old execution policy',
        command_semantics='Unchanged TLAPS --strict --nofp and original cache/library arguments',
        timing_caveat='Cleanup reserve reduces compute window by up to 0.5 seconds within unchanged 30-second budget; compare parent and child under this same wrapper',
        containment='Best-effort ancestry polling; instantaneous unobserved reparenting is not excluded',
        acceptance='owned_admission.json admitted=true required in addition to inherited results'))
    records = {}
    original = runner.run_cmd

    def guarded(cmd, cwd, timeout):
        if identity(a) != before:
            raise RuntimeError('Owned verification identity drift')
        work = Path(cwd).resolve()
        if not work.is_relative_to(a.output / 'checks') or timeout != 30:
            raise RuntimeError('Unexpected verification scope or budget')
        if work in records or '--strict' not in cmd or '--nofp' not in cmd:
            raise RuntimeError('Repeated or non-strict verification command')
        result = run_owned(cmd, work, timeout)
        record = dict(command=list(cmd), cwd=str(work), timeout=timeout, process=result)
        write(work / 'process.json', record)
        records[work] = record
        if result['command'] != list(cmd) or result['cwd'] != str(work):
            raise RuntimeError('Process command/cwd mismatch')
        if identity(a) != before:
            raise RuntimeError('Owned verification identity drift')
        return as_runner_tuple(result)

    try:
        runner.run_cmd = guarded
        broader.verify(a)
        if identity(a) != before:
            raise RuntimeError('Owned verification identity drift')
        counts = audit(a.output, records, expected)
        write(a.output / 'owned_admission.json', dict(admitted=True, identity=before,
            **counts, rows_sha256=sha(a.output / 'rows.jsonl'),
            summary_sha256=sha(a.output / 'summary.json'),
            process_sha256={str(p / 'process.json'): sha(p / 'process.json') for p in records}))
    except BaseException as exc:
        write(a.output / 'owned_failure.json', dict(admitted=False,
            reason=type(exc).__name__ + ': ' + str(exc), checked_processes=len(records),
            inherited_results_not_admitted=True))
        raise
    finally:
        runner.run_cmd = original


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('prompts', 'generations', 'tokenizer-path', 'output'):
        parser.add_argument('--' + name, type=Path, required=True)
    verify(parser.parse_args())


if __name__ == '__main__':
    main()
