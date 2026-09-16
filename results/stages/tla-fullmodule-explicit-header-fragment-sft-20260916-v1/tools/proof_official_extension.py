#!/usr/bin/env python3
"""Frozen official theorem-extension baseline; symbolic, no model or training."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_fragment_check import _code, validate_fragment, certify_fragment
from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def build_task(entry, root):
    path = root / entry['module_file']
    raw = path.read_bytes()
    if sha(raw) != entry['sha256']:
        raise ValueError('official source hash mismatch: ' + entry['id'])
    text = raw.decode('utf-8')  # retain CRLF, unlike read_text()
    code = _code(text)
    target = list(re.finditer(r'\b(?:THEOREM|LEMMA)\s+' + re.escape(entry['theorem_name']) + r'\s*==', code))
    closing = list(re.finditer(r'(?m)^={4,}[^\S\r\n]*\r?$', code))
    if len(target) != 1 or len(closing) != 1 or target[0].end() >= closing[0].start():
        raise ValueError('unsupported target/module boundary: ' + entry['id'])
    offset = closing[0].start()
    # Split before the preceding newline: the inserted fragment starts with its
    # own newline, while removing it reconstructs the exact original bytes.
    offset -= 2 if text[:offset].endswith('\r\n') else 1
    if offset < target[0].end():
        raise ValueError('empty target statement')
    goal = code[target[0].end():offset].strip()
    if re.search(r'\b(?:PROOF|BY|OBVIOUS|OMITTED|THEOREM|LEMMA)\b|<\d+>', goal):
        raise ValueError('target is not a bare final theorem: ' + entry['id'])
    prefix, suffix = text[:offset], text[offset:]
    module = validate_fragment(prefix, '\nBY SMT', suffix, entry['theorem_name'])
    assert (prefix + suffix).encode() == raw
    return dict(id=entry['id'], official_id=entry['id'], category=entry['category'],
                source_path=str(path.resolve()), source_sha256=sha(raw),
                theorem_name=entry['theorem_name'], module_name=module,
                prefix=prefix, suffix=suffix, target_goal=goal,
                insertion_byte_offset=len(prefix.encode()), split='official_test',
                task_kind='whole_target_proof_extension', human_target_skeleton=False,
                dependencies=[], dependency_sha256={})


def source_aware_candidates(candidates, sources):
    """Avoid citing a backend operator absent from the immutable context.

    Default backend proofs need no new EXTENDS/declaration. We do not modify
    the theorem or add a trusted module just to make our generated syntax valid.
    """
    from tools.proof_source_scope import top_level_code
    code = '\n'.join(top_level_code(source) for source in sources)
    smt_visible = bool(re.search(r'(?m)^\s*SMT\s*==', code) or
                       re.search(r'(?m)^\s*EXTENDS\s+[^\n]*\bTLAPS\b', code))
    result = []
    for candidate in candidates:
        if not smt_visible:
            if candidate == 'BY SMT':
                candidate = 'OBVIOUS'
            elif candidate.startswith('BY SMT DEF '):
                candidate = 'BY DEF ' + candidate[len('BY SMT DEF '):]
            elif candidate.startswith('BY SMT, '):
                candidate = 'BY ' + candidate[len('BY SMT, '):]
        if candidate not in result:
            result.append(candidate)
    return result, smt_visible


def prepare(manifest_path, root, output, source_aware=False):
    entries = json.loads(manifest_path.read_text())
    if len(entries) != 119 or len({e['id'] for e in entries}) != 119:
        raise ValueError('official population must contain exactly 119 unique IDs')
    tasks = []
    for entry in entries:
        task = build_task(entry, root)
        paths = libraries(task['prefix'], [], TLA_LIBRARY.split(':'))
        library_texts = [p.read_text() for p in paths]
        candidates, context = proposals(task['prefix'], task['theorem_name'], task['target_goal'], [], library_texts)
        if source_aware:
            candidates, task['smt_visible'] = source_aware_candidates(candidates, [task['prefix'], *library_texts])
        task['symbolic_candidates'] = candidates
        task['retrieval'] = context
        task['library_sha256'] = {str(p.resolve()): sha(p.read_bytes()) for p in paths}
        tasks.append(task)
    output.mkdir(parents=True, exist_ok=False)
    payload = dict(tasks=tasks, requested_tasks=119,
                   official_manifest_sha256=sha(manifest_path.read_bytes()),
                   official_manifest_path=str(manifest_path.resolve()),
                   task_kind='whole_target_proof_extension', reference_fragments_used=False,
                   legacy_retrieval_index_used=False, training=False,
                   source_aware_backends=source_aware,
                   method='symbolic visible-statement/definition retrieval; no model',
                   source_reconstruction='(prefix + suffix).encode(utf-8) equals original raw bytes')
    dump(output / 'manifest.json', payload)
    (output / 'builder.py').write_bytes(Path(__file__).read_bytes())
    return payload


def summarize(tasks, rows, statuses):
    passed = {r['task'] for r in rows if r['certified']}
    attempted = {r['task'] for r in rows}
    return dict(requested_tasks=len(tasks), attempted_tasks=len(attempted),
                certified_tasks=len(passed), attempts=len(rows),
                unattempted_tasks=len(tasks)-len(attempted),
                by_category={category: dict(requested=sum(t['category']==category for t in tasks),
                    certified=sum(t['category']==category and t['id'] in passed for t in tasks))
                    for category in sorted({t['category'] for t in tasks})},
                task_statuses=statuses, model_updates=0, model_used=False,
                scope='official theorem extension, not human-skeleton repair or learned transfer')


def evaluate(manifest_path, output, attempts=4, timeout=5, seconds=900, checker=certify_fragment):
    manifest = json.loads(manifest_path.read_text())
    tasks = manifest['tasks']
    if len(tasks) != 119 or len({t['id'] for t in tasks}) != 119:
        raise ValueError('official population must remain 119')
    if sha(Path(manifest['official_manifest_path']).read_bytes()) != manifest['official_manifest_sha256']:
        raise ValueError('official manifest changed')
    official = {e['id']:e for e in json.loads(Path(manifest['official_manifest_path']).read_text())}
    if set(official) != {t['id'] for t in tasks}:
        raise ValueError('official ID population mismatch')
    for task in tasks:
        entry = official[task['id']]
        if (task['theorem_name'] != entry['theorem_name'] or
                task['category'] != entry['category'] or task['source_sha256'] != entry['sha256'] or
                task['split'] != 'official_test' or task['task_kind'] != 'whole_target_proof_extension'):
            raise ValueError('official task identity mismatch')
        if sha((task['prefix']+task['suffix']).encode()) != task['source_sha256']:
            raise ValueError('frozen source reconstruction mismatch')
        if sha(Path(task['source_path']).read_bytes()) != task['source_sha256']:
            raise ValueError('official source changed')
        for path, expected in task['library_sha256'].items():
            if sha(Path(path).read_bytes()) != expected:
                raise ValueError('retrieved library changed')
    output.mkdir(parents=True, exist_ok=False)
    (output/'manifest.json').write_bytes(manifest_path.read_bytes())
    (output/'evaluator.py').write_bytes(Path(__file__).read_bytes())
    config = dict(manifest_sha256=sha(manifest_path.read_bytes()), attempts_per_task=attempts,
                  timeout_per_check=timeout, seconds=seconds,
                  hypothesis='Visible premise search can discharge some official bare theorem targets',
                  stop='Fixed candidates and wall budget; no task removed',
                  method=manifest['method'], reference_fragments_used=False,
                  source_aware_backends=manifest.get('source_aware_backends', False),
                  legacy_retrieval_index_used=False, training=False)
    config['implementation_sha256'] = {str(path.relative_to(ROOT)):sha(path.read_bytes())
        for path in [Path(__file__).resolve(), ROOT/'harness/proof_fragment_check.py',
                     ROOT/'harness/runner.py', ROOT/'tools/proof_fact_search.py',
                     ROOT/'tools/proof_premise_search.py', ROOT/'tools/proof_source_scope.py']}
    config['historical_contamination_flags'] = {
        '2_TCommit': 'Historical corpus195 proof-trace overlap; this arm does not use that index. Retained in /119.'}
    dump(output/'config.json', config)
    statuses = {t['id']:'unattempted_budget' for t in tasks}
    rows = []
    start = time.monotonic()
    with (output/'rows.jsonl').open('x') as stream:
        # Round-robin makes a bounded run cover every target before second tries.
        for attempt in range(attempts):
            for task in tasks:
                if statuses[task['id']] == 'certified':
                    continue
                if attempt >= len(task['symbolic_candidates']):
                    continue
                if time.monotonic()-start > seconds-timeout:
                    break
                fragment = '\n'+task['symbolic_candidates'][attempt]
                row = checker(task['prefix'], fragment, task['suffix'],
                              theorem_name=task['theorem_name'],
                              work_root=output/'checks'/task['id']/str(attempt), timeout=timeout)
                row.update(task=task['id'], category=task['category'], attempt=attempt,
                           fragment=fragment, source_sha256=task['source_sha256'])
                rows.append(row)
                stream.write(json.dumps(row)+'\n'); stream.flush()
                statuses[task['id']] = 'certified' if row['certified'] else row['status']
                dump(output/'summary.json', dict(**summarize(tasks, rows, statuses),
                                                elapsed_seconds=time.monotonic()-start, **config))
                print(json.dumps({k:row[k] for k in ('task','attempt','certified','status')}), flush=True)
            else:
                continue
            break
    result = dict(**summarize(tasks, rows, statuses), elapsed_seconds=time.monotonic()-start, **config)
    dump(output/'summary.json', result)
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest='mode', required=True)
    a = sub.add_parser('prepare')
    a.add_argument('--manifest', type=Path, default=ROOT/'corpus/lmgpa/manifest.json')
    a.add_argument('--root', type=Path, default=Path('/Users/eric/GitHub/lmgpa'))
    a.add_argument('--output', type=Path, required=True)
    a.add_argument('--source-aware-backends', action='store_true')
    b = sub.add_parser('symbolic')
    b.add_argument('--manifest', type=Path, required=True)
    b.add_argument('--output', type=Path, required=True)
    b.add_argument('--attempts', type=int, default=4)
    b.add_argument('--timeout', type=int, default=5)
    b.add_argument('--seconds', type=int, default=900)
    args = p.parse_args()
    if args.mode == 'prepare':
        result = prepare(args.manifest, args.root, args.output, args.source_aware_backends)
        print(json.dumps(dict(prepared=len(result['tasks']), reference_fragments_used=False)))
    else:
        if not (1 <= args.attempts <= 4 and 1 <= args.timeout <= 5 and 0 < args.seconds <= 900):
            p.error('maximum budget: 4 candidates/task, 5 seconds/check, 900 seconds total')
        print(json.dumps(evaluate(args.manifest, args.output, args.attempts, args.timeout, args.seconds)))


if __name__ == '__main__':
    main()
