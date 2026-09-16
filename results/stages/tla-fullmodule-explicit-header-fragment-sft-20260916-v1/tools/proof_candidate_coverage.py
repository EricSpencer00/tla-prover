#!/usr/bin/env python3
"""TRAIN-only finite candidate solvability; no model, sampling, or optimizer."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_candidate_rl import freeze_train
from tools.proof_official_extension import source_aware_candidates
from tools.proof_premise_search import candidates as definition_candidates
from tools.proof_source_scope import top_level_code
from tools.proof_step_candidates import step_candidates


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def augment(task, limit=8):
    """Reserve up to six slots for source-derived step proposals; no answers."""
    sources = [task['prefix']] + [Path(p).read_text() for p in task['context']['library_sha256']]
    _, smt = source_aware_candidates(['BY SMT'], sources)
    visible = ['SMT'] if smt else []
    if any(re.search(r'(?m)^\s*PTL\s*==', top_level_code(s)) for s in sources):
        visible.append('PTL')
    defs = next((c[len('BY SMT DEF '):].split(', ') for c in definition_candidates(task['prefix'])
                 if c.startswith('BY SMT DEF ')), [])
    steps, metadata = step_candidates(task['prefix'], task['theorem_name'],
        visible_backends=visible, visible_definitions=defs, limit=6)
    base = task['candidates']
    mixture = list(dict.fromkeys(base[:2]+steps+base[2:]))[:limit] if steps else base[:limit]
    return mixture, dict(**metadata, proposed_steps=steps,
                         mixture='two original choices, up to six step choices, original fallback')


def prepare(manifest_bytes, use_steps=False):
    tasks = freeze_train(manifest_bytes, 8)
    if use_steps:
        for task in tasks:
            task['candidates'], task['step_context'] = augment(task)
    return tasks


def evaluate(tasks, output, seconds=600, timeout=5, checker=None):
    from harness.proof_fragment_check import certify_fragment
    checker = checker or certify_fragment
    started = time.monotonic()
    rows, passed = [], set()
    def save():
        result = dict(requested_train_tasks=len(tasks), attempted_train_tasks=len({r['task'] for r in rows}),
                      certified_train_tasks=len(passed), checker_attempts=len(rows),
                      elapsed_seconds=time.monotonic()-started, parameter_updates=0,
                      reference_fragment_used=False, method='TRAIN candidate solvability, not learned performance')
        dump(output/'summary.json', result)
        return result
    with (output/'checks.jsonl').open('x') as stream:
        for index in range(8):
            for task in tasks:
                if task['id'] in passed or index >= len(task['candidates']):
                    continue
                if time.monotonic()-started > seconds-timeout:
                    return save()
                fragment = task['candidates'][index]
                row = checker(task['prefix'], fragment, task['suffix'], theorem_name=task['theorem_name'],
                    dependencies=tuple(map(Path, task.get('dependencies', []))),
                    work_root=output/'checks'/task['id']/str(index), timeout=timeout)
                row.update(task=task['id'], candidate_index=index, fragment=fragment)
                rows.append(row)
                if row['certified']:
                    passed.add(task['id'])
                stream.write(json.dumps(row)+'\n'); stream.flush()
                save()
    return save()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--steps', action='store_true')
    p.add_argument('--prepare-only', action='store_true')
    p.add_argument('--seconds', type=int, default=600)
    p.add_argument('--timeout', type=int, default=5)
    a = p.parse_args()
    if not 1 <= a.seconds <= 600 or not 1 <= a.timeout <= 5:
        p.error('Maximum600 seconds,5 seconds/check')
    tasks = prepare(a.manifest.read_bytes(), a.steps)
    a.output.mkdir(parents=True, exist_ok=False)
    dump(a.output/'frozen.json', tasks)
    dump(a.output/'config.json', dict(manifest_sha256=sha(a.manifest.read_bytes()),
        args={k:str(v) if isinstance(v, Path) else v for k,v in vars(a).items()},
        frozen_sha256=sha((a.output/'frozen.json').read_bytes()),
        hypothesis='Visible completed step references improve TRAIN candidate solvability before more RL',
        measurement='All TRAIN tasks, eight deterministic candidates maximum, strict full-module TLAPS',
        stop='round-robin eight choices, first proof per task, declared total/checker time limits',
        reference_fragment_used=False, model_used=False, parameter_updates=0,
        implementation_sha256={str(f.relative_to(ROOT)):sha(f.read_bytes()) for f in [
            Path(__file__).resolve(), ROOT/'tools/proof_step_candidates.py', ROOT/'tools/proof_source_scope.py',
            ROOT/'tools/proof_candidate_rl.py', ROOT/'tools/proof_fact_search.py', ROOT/'tools/proof_premise_search.py',
            ROOT/'tools/proof_official_extension.py', ROOT/'tools/proof_retrieved_context.py',
            ROOT/'tools/proof_sequence_train.py', ROOT/'harness/proof_fragment_check.py', ROOT/'harness/runner.py']}))
    if not a.prepare_only:
        print(json.dumps(evaluate(tasks, a.output, a.seconds, a.timeout)))


if __name__ == '__main__':
    main()
