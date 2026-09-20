#!/usr/bin/env python3
"""Freeze source-family-separated proof repair tasks; no model or training.

Selection controls precede freeze and are recorded, never silently dropped.
The official evaluation sources are read only to exclude lexical overlap.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_dev_manifest import build_manifest, freeze_fragment_boundaries
from harness.corpora import normalize_tla, shingle_set, jaccard
from harness.proof_fragment_check import certify_fragment, _code

SELECTION = [
    ('crdt-type-step', 'TypeCorrect', 8, 13, 12, 12),
    ('crdt-safety-step', 'Safe', 16, 21, 20, 20),
    ('crdt-sum-type-proof', 'SumType', 44, 51, 47, 51),
    ('crdt-sum-zero-proof', 'SumIsZero', 53, 62, 56, 62),
]

def sha(data):
    return hashlib.sha256(data).hexdigest()

def goal_text(text):
    """Named goal through first proof line, including multiline ASSUME/PROVE."""
    return re.split(r'(?m)^\s*(?:BY\b|PROOF\b|<\d+>|OBVIOUS\b)', _code(text), maxsplit=1)[0].strip()

def named_goals(text):
    code = _code(text)
    starts = list(re.finditer(r'(?m)^\s*(?:THEOREM|LEMMA)\s+[A-Za-z_]\w*\s*==', code))
    return [goal_text(code[m.start():starts[i+1].start() if i+1<len(starts) else len(code)]) for i,m in enumerate(starts)]

def comparison(content, pool):
    query = shingle_set(normalize_tla(content))
    score, name = max((jaccard(query, other), name) for name, other in pool)
    return {'max_jaccard': score, 'nearest': name}

def validate_split(tasks):
    train = {t['source_family'] for t in tasks if t['split'] == 'train'}
    dev = {t['source_family'] for t in tasks if t['split'] == 'development'}
    if not train or not dev or train & dev:
        raise ValueError('train/development must have disjoint nonempty source families')
    if len({t['id'] for t in tasks}) != len(tasks):
        raise ValueError('duplicate task id')

def construct(lmgpa_root, holdout_root):
    old = build_manifest(lmgpa_root, holdout_root)
    tasks = old['tasks']
    for task in tasks:
        task.update(split='train', source_family='tlaplus/Examples:LearnProofs',
                    previous_usage='six development tasks promoted to training; no longer clean evaluation')
    sources = [(entry['id'], Path(entry['path']).read_text()) for entry in old['official_sources']]
    pool = [(name, shingle_set(normalize_tla(text))) for name, text in sources]
    goals = [(name, shingle_set(normalize_tla(goal))) for name, text in sources
             for goal in named_goals(text)]
    majority = ROOT / 'tools/tlaplus-examples/specifications/Majority/MajorityProof.tla'
    old['excluded'].append(dict(id='MajorityProof-family', reason='official near duplicate; rejected before controls',
                               decontamination=comparison(majority.read_text(), pool)))
    folder = ROOT / 'tools/tlaplus-examples/specifications/FiniteMonotonic'
    path = folder / 'CRDT_proof.tla'
    source = path.read_text()
    lines = source.splitlines(keepends=True)
    dependency = folder / 'CRDT.tla'
    for ident, theorem, begin, end, lo, hi in SELECTION:
        prefix, fragment, suffix = freeze_fragment_boundaries(
            ''.join(lines[:lo-1]), ''.join(lines[lo-1:hi]),
            ''.join(lines[hi:end]) + '\n=============================================================================\n')
        assembled = prefix + fragment + suffix
        goal = goal_text(''.join(lines[begin-1:end]))
        checks = {label: comparison(text, pool) for label, text in
                  [('source', source), ('assembled', assembled),
                   ('target_goal', goal), ('dependency', dependency.read_text())]}
        checks['named_goal'] = comparison(goal, goals)
        task = dict(id=ident, module_name='CRDT_proof', theorem_name=theorem,
                    prefix=prefix, suffix=suffix, reference_fragment=fragment,
                    dependencies=[str(dependency)], dependency_sha256={str(dependency):sha(dependency.read_bytes())},
                    source_path=str(path), source_sha256=sha(path.read_bytes()),
                    source_family='tlaplus/Examples:FiniteMonotonic', split='development',
                    source_commit=tasks[0]['source_commit'], source_repository=tasks[0]['source_repository'],
                    source_dirty=subprocess.check_output(['git', '-C', str(ROOT/'tools/tlaplus-examples'), 'status', '--porcelain', '--', str(path)], text=True).strip(),
                    assembled_sha256=sha(assembled.encode()), source_theorem_lines=[begin,end],
                    source_fragment_lines=[lo,hi], target_goal=goal,
                    decontamination=checks, task_contract='Immutable theorem and surrounding human proofs; one multi-token proof fragment or complete case proof replaced.')
        if any(v['max_jaccard'] >= .65 for v in checks.values()):
            old['excluded'].append(dict(id=ident, reason='official near-duplicate selection exclusion', decontamination=checks))
        else:
            tasks.append(task)
    train = [t for t in tasks if t['split']=='train']
    train_pool = [(t['id'], shingle_set(normalize_tla(Path(t['source_path']).read_text()))) for t in train]
    assembled_pool = [(t['id'], shingle_set(normalize_tla(t['prefix']+t['reference_fragment']+t['suffix']))) for t in train]
    train_goal_pool = [(t['id'], shingle_set(normalize_tla(goal))) for t in train for goal in named_goals(t['prefix']+t['reference_fragment']+t['suffix'])]
    for task in tasks:
        if task['split'] == 'development':
            task['train_cross_similarity'] = {label: comparison(text, candidates) for label, text, candidates in
                    [('source', Path(task['source_path']).read_text(), train_pool),
                     ('assembled', task['prefix']+task['reference_fragment']+task['suffix'], assembled_pool),
                     ('target_goal', task['target_goal'], train_goal_pool)]}
            if any(x['max_jaccard'] >= .65 for x in task['train_cross_similarity'].values()):
                raise ValueError('development/train near duplicate')
    old.update(schema_version=3, kind='source_family_separated_human_proof_repair',
               split_contract='LearnProofs previously measured development becomes train; FiniteMonotonic module/dependencies are development only. Public pretraining absence unknown.',
               not_generalization=True, scope='Development transfer from human skeletons; not official G2 benchmark or whole-proof generation',
               tasks=tasks)
    return old

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--lmgpa-root', type=Path, default=Path('/Users/eric/GitHub/lmgpa'))
    p.add_argument('--holdout-root', type=Path, default=Path('/Users/eric/GitHub/tla_benchmark/data/tla_files'))
    p.add_argument('--timeout', type=int, default=45)
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=False)
    manifest = construct(a.lmgpa_root, a.holdout_root)
    (a.output/'selection.json').write_text(json.dumps(manifest, indent=2)+'\n')
    validate_split(manifest['tasks'])
    (a.output/'generator.py').write_bytes(Path(__file__).read_bytes())
    controls = []
    for task in manifest['tasks']:
        for label, fragment, expected in [('reference', task['reference_fragment'], True), ('omitted', 'OMITTED', False)]:
            result = certify_fragment(task['prefix'], fragment, task['suffix'], theorem_name=task['theorem_name'],
                     dependencies=tuple(map(Path, task['dependencies'])), work_root=a.output/'controls'/task['id']/label, timeout=a.timeout)
            controls.append(dict(id=task['id'], control=label, expected=expected, **result))
            (a.output/'reference_controls.json').write_text(json.dumps(controls, indent=2)+'\n')
            print(json.dumps({'id': task['id'], 'control': label, 'certified': result['certified'], 'status': result['status']}), flush=True)
    valid = all(row['certified'] == row['expected'] for row in controls)
    (a.output/'summary.json').write_text(json.dumps(dict(all_controls_correct=valid,
        tasks=len(manifest['tasks']), train=sum(t['split']=='train' for t in manifest['tasks']),
        development=sum(t['split']=='development' for t in manifest['tasks']), frozen=valid), indent=2)+'\n')
    if not valid:
        raise SystemExit('Control failure; selection retained but no frozen manifest emitted')
    (a.output/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')

if __name__ == '__main__':
    main()
