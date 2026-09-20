#!/usr/bin/env python3
"""Bounded symbolic premise-search baseline, explicitly NOT model generation."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys
import time

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))
from harness.proof_fragment_check import certify_fragment, _code
from tools.proof_source_scope import top_level_code


def candidates(prefix, dependency_texts=()):
    # Only declarations visible in the immutable source prefix. Never inspect
    # reference_fragment or the held-out official benchmark/retrieval answers.
    names = []
    for index, source in enumerate([prefix, *dependency_texts]):
        declarations = re.finditer(
            r'^[ \t]*(?P<local>LOCAL\s+)?(?P<name>[A-Za-z_]\w*)\s*(?:\([^\n]*?\))?\s*==',
            top_level_code(source), re.M)
        names.extend(m['name'] for m in declarations if not (index and m['local']))
    names = list(dict.fromkeys(names))
    # Deterministic enumeration, not model sampling: avoid spending verifier
    # budget twice on the same search candidate.
    proposed = ['BY SMT']
    if names:
        proposed += ['BY SMT DEF ' + ', '.join(names), 'BY DEF ' + ', '.join(names)]
    yield from proposed
    seen = set(proposed)
    for size in range(1, min(3, len(names))+1):
        for group in itertools.combinations(names, size):
            fragment = 'BY SMT DEF ' + ', '.join(group)
            if fragment not in seen:
                seen.add(fragment)
                yield fragment


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--attempts', type=int, default=16)
    p.add_argument('--timeout', type=int, default=10)
    p.add_argument('--seconds', type=int, default=600)
    a = p.parse_args()
    assert 1 <= a.attempts <= 64 and 1 <= a.timeout <= 60 and a.seconds > 0
    a.output = a.output.resolve()
    a.output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads(a.manifest.read_text())
    (a.output/'manifest.json').write_bytes(a.manifest.read_bytes())
    (a.output/'search.py').write_text(Path(__file__).read_text())
    config = dict(method='symbolic visible-definition search + TLAPS; no model, no training',
                  manifest_sha256=hashlib.sha256(a.manifest.read_bytes()).hexdigest(),
                  attempts_per_task=a.attempts, verifier_timeout=a.timeout,
                  seconds=a.seconds, reference_fragment_used=False,
                  context='local source prefix and explicit immutable task dependencies',
                  scope='development human proof-skeleton repair, not full proof generation')
    (a.output/'config.json').write_text(json.dumps(config, indent=2))
    started = time.monotonic()
    rows = []
    with (a.output/'rows.jsonl').open('x') as stream:
        for task in manifest['tasks']:
            dependencies = [Path(x) for x in task.get('dependencies', [])]
            texts = [dep.read_text() for dep in dependencies]
            for attempt, fragment in enumerate(itertools.islice(candidates(task['prefix'], texts), a.attempts)):
                if time.monotonic()-started > a.seconds-a.timeout:
                    break
                row = certify_fragment(task['prefix'], fragment, task['suffix'],
                        theorem_name=task['theorem_name'], work_root=a.output/'checks'/task['id']/str(attempt),
                        dependencies=tuple(Path(x) for x in task.get('dependencies', [])), timeout=a.timeout)
                row.update(task=task['id'], attempt=attempt, fragment=fragment)
                rows.append(row)
                stream.write(json.dumps(row)+'\n')
                stream.flush()
                print(json.dumps({k:row[k] for k in ['task','attempt','fragment','certified','status','total']}), flush=True)
                if row['certified']:
                    break
    summary = dict(tasks=len(manifest['tasks']), attempted_tasks=len({r['task'] for r in rows}),
                   certified_tasks=len({r['task'] for r in rows if r['certified']}),
                   attempts=len(rows), elapsed_seconds=time.monotonic()-started, **config)
    (a.output/'summary.json').write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
