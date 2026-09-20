#!/usr/bin/env python3
"""Expand TRAIN human skeletons into exact single-line proof-leaf repairs."""
import argparse
import copy
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_fragment_check import _code, certify_fragment, validate_fragment
from harness.corpora import normalize_tla, shingle_set
from tools.proof_family_manifest import comparison, named_goals, sha, validate_split
from tools.proof_sequence_train import training_tasks


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def leaf_spans(text, target):
    """Conservative complete-line leaves; keep labels/statements/comments fixed."""
    code = _code(text)
    declarations = list(re.finditer(r'(?m)^\s*(?:THEOREM|LEMMA)\s+'+re.escape(target)+r'\s*==', code))
    if len(declarations) != 1:
        raise ValueError('Exactly one named target declaration required')
    begin = declarations[0].end()
    if re.search(r'(?m)^\s*(?:THEOREM|LEMMA)\b', code[begin:]):
        raise ValueError('Target must be final theorem')
    selected, rejected = [], []
    for match in re.finditer(r'(?m)^([^\n]*)$', code):
        if match.start() < begin:
            continue
        line = match[1]
        leaves = list(re.finditer(r'\bBY\b', line))
        if not leaves:
            leaves = list(re.finditer(r'\bDEFS\b', line))
        if not leaves:
            continue
        leaf = leaves[0]
        offset = match.start()+leaf.start()
        reason = None
        before = line[:leaf.start()].strip()
        if before and not re.match(r'^<\d+>', before):
            reason = 'not a standalone or hierarchical inline leaf'
        elif len(leaves) > 1:
            reason = 'multiple leaf keywords on line'
        elif line.rstrip().endswith(','):
            reason = 'multiline trailing-comma leaf unsupported'
        following = code[match.end():].lstrip()
        if following and not re.match(r'(?:<\d+>|={4,}|BY\b|OBVIOUS\b)', following):
            reason = reason or 'continuation or unsupported next proof line'
        end = match.start()+len(line.rstrip())
        fragment = text[offset:end]
        try:
            _code(fragment, reject_comments=True)
        except ValueError:
            reason = reason or 'embedded comment in leaf unsupported'
        record = dict(start=offset, end=end, line=text.count('\n', 0, offset)+1,
                      inline=bool(before), fragment=fragment)
        if reason:
            rejected.append(dict(**record, reason=reason))
        else:
            selected.append(record)
    return selected, rejected


def expand(parent):
    parents = training_tasks(parent)
    if len(parents) != 17:
        raise ValueError('Expected original 17 training parents')
    development = [copy.deepcopy(t) for t in parent['tasks'] if t['split']=='development']
    if len(development) != 4:
        raise ValueError('Expected unchanged four-task development population')
    tasks, diagnostics = {}, []
    for source in parents:
        restored = source['prefix']+source['reference_fragment']+source['suffix']
        if sha(restored.encode()) != source['assembled_sha256']:
            raise ValueError('Restored parent hash mismatch: '+source['id'])
        spans, skipped = leaf_spans(restored, source['theorem_name'])
        diagnostics.extend(dict(parent=source['id'], **row) for row in skipped)
        for span in spans:
            prefix, fragment, suffix = restored[:span['start']], span['fragment'], restored[span['end']:]
            assert prefix+fragment+suffix == restored
            try:
                validate_fragment(prefix, fragment, suffix, source['theorem_name'])
            except ValueError as exc:
                diagnostics.append(dict(parent=source['id'], **span, reason='strict contract: '+str(exc)))
                continue
            hole_hash = sha(json.dumps([prefix, suffix], ensure_ascii=False).encode())
            provenance = dict(parent_id=source['id'], parent_assembled_sha256=source['assembled_sha256'],
                              restored_leaf_offsets=[span['start'], span['end']], restored_leaf_line=span['line'])
            if hole_hash in tasks:
                existing = tasks[hole_hash]
                if (existing['source_family'], existing['reference_fragment'], existing['dependencies']) != (
                        source['source_family'], fragment, source.get('dependencies', [])):
                    raise ValueError('Conflicting duplicate hole provenance')
                existing['parents'].append(provenance)
                continue
            task = {k:copy.deepcopy(source[k]) for k in (
                'module_name', 'theorem_name', 'source_path', 'source_sha256', 'source_family',
                'source_commit', 'source_repository', 'dependencies', 'dependency_sha256') if k in source}
            task.update(id='leaf-'+hole_hash[:20], prefix=prefix, suffix=suffix, reference_fragment=fragment,
                        split='train', assembled_sha256=source['assembled_sha256'], hole_sha256=hole_hash,
                        parents=[provenance], inline_leaf=span['inline'],
                        target_goal=source.get('target_goal') or named_goals(restored)[-1],
                        task_contract='One complete single-line BY/DEFS leaf; all statements and other human proof steps immutable',
                        transformation='Move one exact leaf substring into response; no source rewriting')
            tasks[hole_hash] = task
    validate_split(list(tasks.values())+development)
    return list(tasks.values()), development, diagnostics


def audit(tasks, development, official):
    sources = []
    for entry in official:
        path = Path(entry['path'])
        if sha(path.read_bytes()) != entry['sha256']:
            raise ValueError('Official exclusion source changed: '+str(path))
        sources.append((entry['id'], path.read_text()))
    dev_paths = dict.fromkeys([t['source_path'] for t in development]+
                              [p for t in development for p in t.get('dependencies', [])])
    dev_texts = [(p, Path(p).read_text()) for p in dev_paths]
    pool = [(name, shingle_set(normalize_tla(text))) for name,text in sources]
    goals = [(name, shingle_set(normalize_tla(g))) for name,text in sources for g in named_goals(text)]
    dev_pool = [(name, shingle_set(normalize_tla(text))) for name,text in dev_texts]
    dev_goals = [(name, shingle_set(normalize_tla(g))) for name,text in dev_texts for g in named_goals(text)]
    cache, accepted, rejected = {}, [], []
    for task in tasks:
        key = (task['assembled_sha256'], task['source_sha256'], task['target_goal'])
        if key not in cache:
            source_path = Path(task['source_path'])
            if sha(source_path.read_bytes()) != task['source_sha256']:
                raise ValueError('Training source changed')
            contents = [('source', source_path.read_text()),
                        ('assembled', task['prefix']+task['reference_fragment']+task['suffix']),
                        ('target_goal', task['target_goal'])]
            for name in task.get('dependencies', []):
                data = Path(name).read_bytes()
                if sha(data) != task['dependency_sha256'][name]:
                    raise ValueError('Training dependency changed')
                contents.append(('dependency:'+name, data.decode()))
            checks = {label:comparison(text, pool) for label,text in contents}
            cross = {label:comparison(text, dev_pool) for label,text in contents}
            checks['named_goal'] = comparison(task['target_goal'], goals)
            cross['named_goal'] = comparison(task['target_goal'], dev_goals)
            cache[key] = checks, cross
        task['decontamination'], task['development_similarity'] = cache[key]
        if any(v['max_jaccard'] >= .65 for collection in cache[key] for v in collection.values()):
            rejected.append(dict(id=task['id'], reason='official/development near duplicate',
                                 decontamination=task['decontamination'], development_similarity=task['development_similarity']))
        else:
            accepted.append(task)
    return accepted, rejected


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--seconds', type=int, default=180)
    p.add_argument('--timeout', type=int, default=12)
    a = p.parse_args()
    if not 1 <= a.seconds <= 180 or not 1 <= a.timeout <= 15:
        p.error('Maximum control budgets: 180 seconds total, 15 seconds each')
    parent_bytes = a.manifest.read_bytes()
    parent = json.loads(parent_bytes)
    selected, dev, diagnostics = expand(parent)
    selected, excluded = audit(selected, dev, parent['official_sources'])
    a.output.mkdir(parents=True, exist_ok=False)
    (a.output/'builder.py').write_bytes(Path(__file__).read_bytes())
    dump(a.output/'selection.json', selected)
    dump(a.output/'diagnostics.json', dict(unsupported=diagnostics, decontamination_excluded=excluded))
    started = time.monotonic()
    reference_cache, controls, admitted = {}, [], []
    for task in selected:
        key = (task['assembled_sha256'], task['theorem_name'], tuple(task.get('dependencies', [])))
        if key not in reference_cache:
            if time.monotonic()-started > a.seconds-a.timeout:
                excluded.append(dict(id=task['id'], reason='reference control budget unmeasured'))
                continue
            result = certify_fragment(task['prefix'], task['reference_fragment'], task['suffix'],
                theorem_name=task['theorem_name'], dependencies=tuple(map(Path,task.get('dependencies', []))),
                work_root=a.output/'controls'/task['id']/'reference', timeout=a.timeout)
            reference_cache[key] = (task['id'], result)
        representative, reference = reference_cache[key]
        row = dict(id=task['id'], reference_reused_from=representative,
                   assembled_sha256=task['assembled_sha256'], reference=reference)
        # Same restored bytes/theorem/dependencies reuse one positive module run;
        # each distinct hole independently exercises admission rejection.
        if time.monotonic()-started > a.seconds-1:
            excluded.append(dict(id=task['id'], reason='negative control budget unmeasured'))
            continue
        negative = certify_fragment(task['prefix'], 'OMITTED', task['suffix'], theorem_name=task['theorem_name'],
            dependencies=tuple(map(Path,task.get('dependencies', []))),
            work_root=a.output/'controls'/task['id']/'omitted', timeout=1)
        row['omitted'] = negative
        valid = reference['certified'] and not negative['certified'] and negative['status']=='contract_reject'
        row['admitted'] = valid
        controls.append(row)
        if valid:
            admitted.append(task)
        else:
            excluded.append(dict(id=task['id'], reason='positive/negative control failed',
                                 reference_status=reference['status'], negative_status=negative['status']))
        dump(a.output/'controls.json', controls)
        print(json.dumps(dict(id=task['id'], admitted=valid, reference_reused_from=representative)), flush=True)
    manifest = dict(schema_version=5, kind='exact_human_proof_leaf_expansion', tasks=admitted+dev,
        parent_manifest_sha256=sha(parent_bytes), official_sources=parent['official_sources'],
        excluded=parent.get('excluded', [])+excluded, unsupported=diagnostics,
        split_contract='Leaf repairs from original 17 TRAIN parents only; same four CRDT DEVELOPMENT tasks unchanged',
        scope='Task-shape expansion within existing sources/families, not independent new theorem or family evidence',
        decontamination_contract='Official119/30 and cross-split source/assembled/named-goal lexical Jaccard <0.65; not semantic equivalence',
        reference_control_contract='Exact restored bytes reuse positive checker result; every hole separately rejects OMITTED')
    if admitted:
        validate_split(manifest['tasks'])
        dump(a.output/'manifest.json', manifest)
    dump(a.output/'diagnostics.json', dict(unsupported=diagnostics, exclusions=excluded))
    summary = dict(selected_leaves=len(selected), admitted_train=len(admitted), development=len(dev),
        parent_training_tasks=17, distinct_source_files=len({t['source_path'] for t in admitted}),
        source_families=sorted({t['source_family'] for t in admitted}),
        distinct_parent_modules_checked=len(reference_cache),
        positive_controls=sum(r['certified'] for _,r in reference_cache.values()),
        negative_controls=len(controls), unsupported_occurrences=len(diagnostics), exclusions=len(excluded),
        development_unchanged=dev==[t for t in parent['tasks'] if t['split']=='development'],
        control_seconds=time.monotonic()-started, frozen=bool(admitted))
    dump(a.output/'summary.json', summary)
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
