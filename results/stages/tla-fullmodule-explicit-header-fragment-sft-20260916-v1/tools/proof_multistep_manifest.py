#!/usr/bin/env python3
"""Freeze verified, source-separated hierarchical proof training repairs.

Selection is fixed before controls. Rejected selections remain in the ledger.
No model is called, no evaluation answers are promoted into training.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_family_manifest import construct as base_construct, comparison, named_goals, goal_text, sha, validate_split
from tools.proof_dev_manifest import freeze_fragment_boundaries
from harness.corpora import normalize_tla, shingle_set
from harness.proof_fragment_check import certify_fragment, validate_fragment

# id, source, theorem, declaration/end, hole bounds, dependencies.
SELECTION = [
    ('even-intro', 'sums_even/sums_even.tla', 'T1', 14, 31, 15, 19, []),
    ('even-case-tail', 'sums_even/sums_even.tla', 'T1', 14, 31, 21, 23, []),
    ('odd-case-tail', 'sums_even/sums_even.tla', 'T1', 14, 31, 28, 31, []),
    ('clock-full', 'SpecifyingSystems/HourClock/HourClock_proof.tla', 'HCini_Invariant', 7, 12, 8, 12, ['HourClock.tla']),
    ('clock-preservation', 'SpecifyingSystems/HourClock/HourClock_proof.tla', 'HCini_Invariant', 7, 12, 10, 12, ['HourClock.tla']),
    ('simple-full', 'TeachingConcurrency/Simple.tla', 'Correctness', 126, 157, 127, 157, []),
    ('simple-preservation', 'TeachingConcurrency/Simple.tla', 'Correctness', 126, 157, 131, 153, []),
    ('simple-case-a', 'TeachingConcurrency/Simple.tla', 'Correctness', 126, 157, 135, 138, []),
    ('simple-case-b', 'TeachingConcurrency/Simple.tla', 'Correctness', 126, 157, 139, 149, []),
    ('simple-preservation-tail', 'TeachingConcurrency/Simple.tla', 'Correctness', 126, 157, 150, 153, []),
    ('simple-conclusion', 'TeachingConcurrency/Simple.tla', 'Correctness', 126, 157, 154, 157, []),
    ('simple-short-full', 'TeachingConcurrency/Simple.tla', 'Correctness2', 163, 171, 164, 171, []),
    ('simple-short-preservation', 'TeachingConcurrency/Simple.tla', 'Correctness2', 163, 171, 167, 171, []),
]

def mask_comments(text):
    """Remove only comments, preserving length/newlines and all string bytes."""
    out = list(text)
    i, depth = 0, 0
    while i < len(text):
        if text.startswith('(*', i):
            depth += 1
            out[i:i+2] = '  '
            i += 2
        elif depth and text.startswith('*)', i):
            depth -= 1
            out[i:i+2] = '  '
            i += 2
        elif depth:
            if text[i] != '\n':
                out[i] = ' '
            i += 1
        elif text.startswith('\\*', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out[i:end] = ' ' * (end-i)
            i = end
        elif text[i] == '"':
            i += 1
            while i < len(text) and text[i] != '"':
                if text[i] == '\n':
                    raise ValueError('unterminated string')
                i += 2 if text[i] == '\\' else 1
            if i >= len(text):
                raise ValueError('unterminated string')
            i += 1
        elif text.startswith('*)', i):
            raise ValueError('unmatched comment terminator')
        else:
            i += 1
    if depth:
        raise ValueError('unclosed comment')
    return ''.join(out)

def construct(lmgpa_root, holdout_root):
    manifest = base_construct(lmgpa_root, holdout_root)
    official = [(x['id'], Path(x['path']).read_text()) for x in manifest['official_sources']]
    pool = [(i, shingle_set(normalize_tla(t))) for i,t in official]
    goals = [(i, shingle_set(normalize_tla(g))) for i,t in official for g in named_goals(t)]
    dev = [t for t in manifest['tasks'] if t['split']=='development']
    dev_text = [(t['id'], Path(t['source_path']).read_text()) for t in dev]
    dev_text += [(str(p), Path(p).read_text()) for t in dev for p in t['dependencies']]
    dev_pool = [(i, shingle_set(normalize_tla(t))) for i,t in dev_text]
    dev_goals = [(i, shingle_set(normalize_tla(g))) for i,t in dev_text for g in named_goals(t)]
    examples = ROOT/'tools/tlaplus-examples'
    for ident, relative, theorem, begin, end, lo, hi, deps in SELECTION:
        path = examples/'specifications'/relative
        text = path.read_text()
        lines = text.splitlines(keepends=True)
        if not re.search(rf'THEOREM\s+{theorem}\s*==', lines[begin-1]):
            raise ValueError(f'source span mismatch: {ident}')
        original = ''.join(lines[lo-1:hi])
        fragment = mask_comments(original)
        prefix, fragment, suffix = freeze_fragment_boundaries(''.join(lines[:lo-1]), fragment,
                         ''.join(lines[hi:end])+'\n=============================================================================\n')
        assembled = prefix+fragment+suffix
        dependencies = [path.parent/p for p in deps]
        goal = goal_text(''.join(lines[begin-1:end]))
        contents = [('source',text),('assembled',assembled),('target_goal',goal)]
        contents += [('dependency:'+p.name,p.read_text()) for p in dependencies]
        checks = {label:comparison(t,pool) for label,t in contents}
        checks['named_goal'] = comparison(goal,goals)
        cross = {label:comparison(t,dev_pool) for label,t in contents}
        cross['named_goal'] = comparison(goal,dev_goals)
        reason = None
        # This upstream dependency states the very goal without a proof. Do
        # not train against a context with a ready-made unproved shortcut.
        if relative == 'SpecifyingSystems/HourClock/HourClock_proof.tla':
            reason = 'dependency HourClock.tla contains unproved target theorem; excluded before controls'
        elif any(x['max_jaccard'] >= .65 for x in checks.values()):
            reason = 'official near duplicate; excluded before controls'
        elif any(x['max_jaccard'] >= .65 for x in cross.values()):
            reason = 'development near duplicate; excluded before controls'
        try:
            validate_fragment(prefix,fragment,suffix,theorem)
        except ValueError as exc:
            reason = reason or 'unsupported strict contract: '+str(exc)
        if reason:
            manifest['excluded'].append(dict(id=ident, reason=reason, decontamination=checks, development_similarity=cross))
            continue
        task = dict(id=ident,module_name=re.search(r'MODULE\s+(\w+)',text).group(1), theorem_name=theorem,
             prefix=prefix, suffix=suffix, reference_fragment=fragment, source_path=str(path),source_sha256=sha(path.read_bytes()),
             source_family='tlaplus/Examples:'+relative.split('/')[0],split='train',
             source_commit=manifest['tasks'][0]['source_commit'],source_repository=manifest['tasks'][0]['source_repository'],
             source_dirty=subprocess.check_output(['git','-C',str(examples),'status','--porcelain','--',str(path)],text=True).strip(),
             source_theorem_lines=[begin,end],source_fragment_lines=[lo,hi],
             dependencies=list(map(str,dependencies)),dependency_sha256={str(p):sha(p.read_bytes()) for p in dependencies},
             assembled_sha256=sha(assembled.encode()),target_goal=goal,decontamination=checks,development_similarity=cross,
             original_fragment_sha256=sha(original.encode()),transformation='Lexically mask comments only in target fragment; preserve string bytes, theorem and immutable skeleton. Outer whitespace moved into scaffold.',
             task_contract='Human hierarchical proof repair/extension; immutable final theorem and surrounding proof. Public pretraining absence unknown.')
        manifest['tasks'].append(task)
    validate_split(manifest['tasks'])
    manifest.update(schema_version=4,kind='multifamily_hierarchical_proof_repair',
       split_contract='LearnProofs, sums_even, TeachingConcurrency training; unchanged FiniteMonotonic CRDT development. HourClock selected but excluded. Official119/30 exclusion only.',
       development_context_sources=[dict(id=i,sha256=sha(t.encode())) for i,t in dev_text])
    return manifest

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',required=True,type=Path)
    p.add_argument('--lmgpa-root',type=Path,default=Path('/Users/eric/GitHub/lmgpa'))
    p.add_argument('--holdout-root',type=Path,default=Path('/Users/eric/GitHub/tla_benchmark/data/tla_files'))
    p.add_argument('--timeout',type=int,default=15)
    a=p.parse_args()
    a.output.mkdir(parents=True,exist_ok=False)
    manifest=construct(a.lmgpa_root,a.holdout_root)
    (a.output/'generator.py').write_bytes(Path(__file__).read_bytes())
    (a.output/'selection.json').write_text(json.dumps(manifest,indent=2)+'\n')
    controls=[]
    admitted=[]
    for task in manifest['tasks']:
        passed=True
        for label,fragment,expected in [('reference',task['reference_fragment'],True),('omitted','OMITTED',False)]:
            result=certify_fragment(task['prefix'],fragment,task['suffix'],theorem_name=task['theorem_name'],
                dependencies=tuple(map(Path,task['dependencies'])),work_root=a.output/'controls'/task['id']/label,timeout=a.timeout)
            controls.append(dict(id=task['id'],control=label,expected=expected,**result))
            (a.output/'controls.json').write_text(json.dumps(controls,indent=2)+'\n')
            print(json.dumps(dict(id=task['id'],control=label,status=result['status'])),flush=True)
            passed &= result['certified']==expected
        if passed:
            admitted.append(task)
        else:
            manifest['excluded'].append(dict(id=task['id'],reason='reference/omission control failed; not admitted',source_sha256=task['source_sha256']))
            if task['split']=='development' or task['id'] not in {x[0] for x in SELECTION}:
                raise SystemExit('Existing task control failed; no frozen manifest')
    manifest['tasks']=admitted
    train=[t for t in admitted if t['split']=='train']
    valid=len(train)>=12 and len({t['source_family'] for t in train})>=3
    (a.output/'summary.json').write_text(json.dumps(dict(train=len(train),development=len(admitted)-len(train),
             families=sorted({t['source_family'] for t in train}),excluded=len(manifest['excluded']),frozen=valid),indent=2)+'\n')
    if not valid:
        raise SystemExit('Insufficient verified breadth; selection retained, no frozen manifest')
    (a.output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')

if __name__=='__main__':
    main()
