"""Owned whole-module SANY checks: syntax evidence only, never proof or intent."""
import argparse
import json
import math
from pathlib import Path
import re
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness import gen_eval, runner
from harness.proof_ladder_check import classify_sany
from harness.proof_owned_process import run_owned, as_runner_tuple
from tools.proof_cuda_train import file_sha
from tools.proof_cuda_eval import digest, sha, dump

SOURCES = ('tools/proof_fullmodule_sany_checks.py', 'harness/gen_eval.py',
           'harness/runner.py', 'harness/proof_ladder_check.py',
           'harness/proof_owned_process.py', 'tools/proof_cuda_train.py',
           'tools/proof_cuda_eval.py')
NEGATIVE_NAME = 'CodexSyntaxNegativeControl20260906'


def checked(path, expected):
    path = Path(path)
    raw = path.read_bytes()
    if sha(raw) != expected:
        raise ValueError('Immutable input changed: ' + str(path))
    return raw


def identity(tasks):
    java = shutil.which('java')
    if not java or Path(runner.CLASSPATH).resolve() != Path(runner.TLA2TOOLS).resolve():
        raise ValueError('Attested Java and single SANY jar required')
    java = str(Path(java).resolve())
    process = run_owned([java, '-version'], ROOT, 10)
    if not process.get('execution_complete') or process['returncode'] != 0:
        raise ValueError('Java runtime admission failed')
    paths = {ROOT / n for n in SOURCES} | {Path(java), Path(runner.TLA2TOOLS).resolve()}
    paths.update(p for directory in runner.TLA_LIBRARY.split(':')
                 for p in Path(directory).rglob('*.tla') if p.is_file())
    for task in tasks:
        source = task['source']
        checked(source['path'], source['sha256']); paths.add(Path(source['path']))
        for path, pin in task['dependencies'].items():
            checked(path, pin); paths.add(Path(path))
        for key in ('description', 'config', 'wrapper'):
            value = task.get(key)
            if value:
                checked(value['path'], value['sha256']); paths.add(Path(value['path']))
        for path, pin in task.get('wrapper_dependencies', {}).items():
            checked(path, pin); paths.add(Path(path))
    return dict(java=java, java_version=process['output'], classpath=runner.CLASSPATH,
                library=runner.TLA_LIBRARY, files={str(p.resolve()): file_sha(p) for p in sorted(paths)},
                tasks_sha256=digest(tasks), scope='Syntax only; no TLC, TLAPS, non-vacuity or semantic acceptance')


def negative(text):
    if NEGATIVE_NAME in text:
        raise ValueError('Negative-control name collision')
    ends = list(re.finditer(r'^={4,}[ \t]*$', text, re.M))
    if not ends:
        raise ValueError('Complete reference module terminator required')
    index = ends[-1].start()
    return text[:index] + '\n' + NEGATIVE_NAME + ' == )\n' + text[index:]


def check(task, raw_reply, output, current, *, timeout=30, execute=run_owned):
    if type(timeout) not in (int, float) or not 0 < timeout <= 30:
        raise ValueError('Fixed positive at most30-second SANY budget required')
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    module = gen_eval.extract_module(raw_reply)
    result = dict(task_sha256=digest(task), raw_reply_sha256=sha(raw_reply.encode()),
                  module=module, module_sha256=sha(module.encode()) if module is not None else None,
                  status='unmeasured_unknown', sany=None, process=None, syntax_only=True,
                  timeout_seconds=timeout)
    dump(output / 'input.json', dict(task=task, raw_reply=raw_reply))
    try:
        if module is None:
            result.update(status='model_extraction', sany=0)
            return result
        name = runner.module_name(module)
        if name != task['module_name']:
            result.update(status='model_module_name', sany=0)
            return result
        (output / (name + '.tla')).write_bytes(module.encode())
        dependencies = {}
        for source, pin in task['dependencies'].items():
            raw = checked(source, pin); dep = runner.module_name(raw.decode())
            if not dep or dep == name or dep + '.tla' in dependencies:
                raise ValueError('Dependency collision or missing module header')
            dependencies[dep + '.tla'] = pin
            (output / (dep + '.tla')).write_bytes(raw)
        tmp = output / 'jtmp'; tmp.mkdir()
        command = [current['java'], '-Djava.io.tmpdir=' + str(tmp),
                   '-DTLA-Library=' + current['library'], '-cp', current['classpath'],
                   'tla2sany.SANY', name + '.tla']
        remaining = timeout - (time.monotonic() - started)
        if remaining <= 0:
            result['status'] = 'unmeasured_budget'; return result
        process = execute(command, output, remaining)
        dump(output / 'process.json', process)
        rc, text, _, timed_out = as_runner_tuple(process)
        (output / 'sany.log').write_text(text)
        status = classify_sany(rc, text, timed_out, name)
        if not process.get('execution_complete') or not process.get('cleanup_complete') or not process.get('output_complete'):
            status = 'unmeasured_process'
        if time.monotonic() - started > timeout:
            status = 'unmeasured_budget'
        result.update(status=status, sany=1 if status == 'pass' else 0 if status == 'model_sany_reject' else None,
                      process=process, command=command, dependency_sha256=dependencies)
    except (OSError, ValueError) as exc:
        result.update(status='unmeasured_infrastructure', sany=None, error=str(exc))
    finally:
        result['seconds'] = time.monotonic() - started
        dump(output / 'result.json', result)
    return result


def audit(task, raw_reply, result, output, current):
    output = Path(output).resolve()
    if json.loads((output / 'input.json').read_bytes()) != dict(task=task, raw_reply=raw_reply):
        raise ValueError('Exact original input required')
    if json.loads((output / 'result.json').read_bytes()) != result:
        raise ValueError('Saved result differs')
    limit = result.get('timeout_seconds')
    if type(limit) not in (int, float) or not math.isfinite(limit) or not 0 < limit <= 30:
        raise ValueError('Frozen finite SANY deadline required')
    module = gen_eval.extract_module(raw_reply)
    if (result['task_sha256'] != digest(task) or result['raw_reply_sha256'] != sha(raw_reply.encode())
            or result['module'] != module or result['module_sha256'] != (sha(module.encode()) if module is not None else None)):
        raise ValueError('Exact raw extraction and task identity required')
    rejection = 'model_extraction' if module is None else 'model_module_name' if runner.module_name(module) != task['module_name'] else None
    if rejection:
        if result['status'] != rejection or result['sany'] != 0 or result['process'] is not None:
            raise ValueError('Extraction rejection differs')
        return
    checked(output / (task['module_name'] + '.tla'), result['module_sha256'])
    process = result['process']
    if process is None:
        if result['sany'] is not None or not result['status'].startswith('unmeasured_'):
            raise ValueError('Missing process cannot be measured')
        return
    expected = [current['java'], '-Djava.io.tmpdir=' + str(output / 'jtmp'),
                '-DTLA-Library=' + current['library'], '-cp', current['classpath'],
                'tla2sany.SANY', task['module_name'] + '.tla']
    if process['command'] != expected or process['cwd'] != str(output) or result['command'] != expected:
        raise ValueError('Exact owned SANY command required')
    if json.loads((output / 'process.json').read_bytes()) != process:
        raise ValueError('Saved process changed')
    for name, pin in result['dependency_sha256'].items():
        checked(output / name, pin)
    expected_deps = {runner.module_name(checked(path, pin).decode()) + '.tla': pin for path, pin in task['dependencies'].items()}
    if result['dependency_sha256'] != expected_deps:
        raise ValueError('Full frozen dependency inventory required')
    rc, text, _, timed_out = as_runner_tuple(process)
    if type(process['seconds']) not in (int, float) or not math.isfinite(process['seconds']) or process['seconds'] < 0:
        raise ValueError('Finite owned process duration required')
    if (output / 'sany.log').read_text() != text:
        raise ValueError('Raw diagnostic changed')
    status = classify_sany(rc, text, timed_out, task['module_name'])
    if not all(process.get(k) for k in ('execution_complete', 'cleanup_complete', 'output_complete')):
        status = 'unmeasured_process'
    if result['status'] == 'unmeasured_budget':
        if result['seconds'] <= result['timeout_seconds'] or result['sany'] is not None:
            raise ValueError('Budget evidence differs')
    elif result['status'] != status or result['sany'] != (1 if status == 'pass' else 0 if status == 'model_sany_reject' else None):
        raise ValueError('Raw classification differs')


def controls(tasks, output):
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    if len(tasks) != 30 or len({t['id'] for t in tasks}) != 30:
        raise ValueError('All30 immutable holdout tasks required')
    started = time.monotonic()
    before = identity(tasks); dump(output / 'identity_before.json', before)
    rows = []; dump(output / 'summary.json', dict(complete=False, requested=60, syntax_only=True))
    for task in tasks:
        source = checked(task['source']['path'], task['source']['sha256']).decode()
        for label, candidate in (('reference', source), ('syntax_negative', negative(source))):
            if time.monotonic() - started > 1830:
                raise TimeoutError('Bounded60-control batch exhausted; no admission')
            work = output / 'checks' / task['id'] / label
            value = check(task, candidate, work, before); audit(task, candidate, value, work, before)
            accepted = value['sany'] == 1 if label == 'reference' else (
                value['sany'] == 0 and value['status'] == 'model_sany_reject'
                and '***Parse Error***' in value['process']['output'])
            rows.append(dict(id=task['id'], label=label, accepted=accepted, result=value))
            dump(output / 'rows.json', rows)
    after = identity(tasks); dump(output / 'identity_after.json', after)
    elapsed = time.monotonic() - started
    summary = dict(complete=before == after and elapsed <= 1860 and len(rows) == 60 and all(r['accepted'] for r in rows),
                   requested=60, accepted=sum(r['accepted'] for r in rows), syntax_only=True,
                   elapsed_seconds=elapsed, non_vacuity_claim=False, rows_sha256=file_sha(output / 'rows.json'))
    dump(output / 'summary.json', summary)
    if not summary['complete']:
        raise ValueError('Actual60 syntax controls did not all pass; no model admission')
    return summary


def admit_controls(tasks, output):
    output = Path(output).resolve()
    current = identity(tasks)
    summary = json.loads((output / 'summary.json').read_bytes())
    rows = json.loads((output / 'rows.json').read_bytes())
    if (not summary['complete'] or summary['requested'] != 60 or summary['accepted'] != 60
            or len(tasks) != 30 or len(rows) != 60 or summary['non_vacuity_claim'] is not False
            or summary['rows_sha256'] != file_sha(output / 'rows.json')
            or not 0 < summary['elapsed_seconds'] <= 1860
            or json.loads((output / 'identity_before.json').read_bytes()) != current
            or json.loads((output / 'identity_after.json').read_bytes()) != current):
        raise ValueError('Complete current60 real controls required')
    expected = []
    for task in tasks:
        source = checked(task['source']['path'], task['source']['sha256']).decode()
        expected.extend((task, label, candidate) for label, candidate in
                        (('reference', source), ('syntax_negative', negative(source))))
    for row, (task, label, candidate) in zip(rows, expected):
        if row['id'] != task['id'] or row['label'] != label or row['accepted'] is not True:
            raise ValueError('Exact complete ordered control keys required')
        value = row['result']; audit(task, candidate, value, output / 'checks' / task['id'] / label, current)
        if not (value['sany'] == 1 if label == 'reference' else value['sany'] == 0
                and value['status'] == 'model_sany_reject' and '***Parse Error***' in value['process']['output']):
            raise ValueError('Actual reference/parse-negative evidence required')
    return current


def main():
    from tools import proof_fullmodule_holdout_packet as packet
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    a = parser.parse_args()
    tasks = packet.validate_export(json.loads(a.packet.read_bytes()))
    print(json.dumps(controls(tasks, a.output)))


if __name__ == '__main__':
    main()
