#!/usr/bin/env python3
"""Read-only protected-population audit; reports overlap, never authorizes training."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_breadth_manifest as breadth
from tools import proof_sumsequence_controls as discovery

BASE = ROOT / 'results/runs/proof-breadth-controls-20260905-v1/manifest.json'
BASE_SHA = '23d15fba5fcb08e8d8436d02deb727a34976bc220e8d66ec7bc333728949627e'
FRESH = ROOT / 'results/runs/proof-fresh14-controls-20260905-v1/manifest.json'
FRESH_SHA = '02d7ffcdc291fb33716bc332ea878d400cb4affe8d324494c9203549dd55bb0f'
THRESHOLD = .65
CODE = ('tools/proof_sumsequence_exclusions.py','tools/proof_sumsequence_controls.py',
        'tools/proof_breadth_manifest.py','tools/proof_original18.py',
        'tools/proof_source_scope.py','tools/proof_family_manifest.py','harness/corpora.py')


def checked(path, expected):
    raw = Path(path).read_bytes()
    if breadth.sha(raw) != expected:
        raise ValueError('Protected input hash mismatch: ' + str(path))
    return raw


def overlap(result):
    return bool(result['exact_normalized']) or result['max_jaccard'] >= THRESHOLD


def population():
    parent = json.loads(checked(BASE, BASE_SHA))
    fresh = json.loads(checked(FRESH, FRESH_SHA))
    if len(parent['official_sources']) != 149 or len(fresh['tasks']) != 14:
        raise ValueError('Exact official149 and fresh14 populations required')
    sources, goals, provenance, dev = breadth.exclusions(parent)
    if provenance != parent['exclusion_sha256'] or len(dev) != 4:
        raise ValueError('Protected provenance differs from pinned baseline')
    paths = {str(BASE): BASE_SHA, str(FRESH): FRESH_SHA}
    paths.update({p:h for p,h in provenance.items() if Path(p).is_file()})
    for task in dev:
        assembly = task['prefix'] + task['reference_fragment'] + task['suffix']
        if task.get('assembled_sha256') and breadth.sha(assembly.encode()) != task['assembled_sha256']:
            raise ValueError('DEV assembly changed')
        sources.append(('DEV-assembled:' + task['id'], assembly))
        goals.extend(('DEV-assembled:' + task['id'] + ':' + n,b) for n,b in breadth.goal_bodies(assembly))
    for task in fresh['tasks']:
        if task['split'] != 'fresh_evaluation' or task['source_commit'] != discovery.COMMIT:
            raise ValueError('Fresh population provenance changed')
        for path, expected in [(task['source_path'], task['source_sha256']),
                               *task['dependency_sha256'].items()]:
            raw = checked(path, expected).decode()
            if path in paths and paths[path] != expected:
                raise ValueError('Inconsistent protected source hashes')
            paths[path] = expected
            sources.append(('FRESH-source:' + task['id'] + ':' + path, raw))
            goals.extend(('FRESH-source:' + task['id'] + ':' + n,b) for n,b in breadth.goal_bodies(raw))
        if set(task['dependencies']) != set(task['dependency_sha256']):
            raise ValueError('Fresh dependency inventory mismatch')
        assembly = task['prefix'] + task['reference_fragment'] + task['suffix']
        if breadth.sha(assembly.encode()) != task['assembled_sha256']:
            raise ValueError('Fresh assembly changed')
        sources.append(('FRESH-assembled:' + task['id'], assembly))
        goals.extend(('FRESH-assembled:' + task['id'] + ':' + n,b) for n,b in breadth.goal_bodies(assembly))
        goals.append(('FRESH-target:' + task['id'], task['target_goal']))
    return sources, goals, paths, provenance


def audit(output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    before = {n:breadth.sha((ROOT/n).read_bytes()) for n in CODE}
    candidate = discovery.discover()
    sources, goals, paths, provenance = population()
    checks = {}
    def compare(label, text, pool):
        result = breadth.compare(text, pool)
        checks[label] = dict(result, queried_sha256=breadth.sha(text.encode()),
                            protected_pool=pool is goals and 'goals' or 'sources',
                            overlap_exclusion=overlap(result))
    compare('original_source', discovery.SOURCE.read_text(), sources)
    compare('Front_definition_source', discovery.FRONT_SOURCE.read_text(), sources)
    compare('Front_definition', discovery.FRONT, sources)
    for task in candidate['tasks']:
        bodies = breadth.goal_bodies(task['statement'])
        if len(bodies)!=1 or bodies[0][0]!=task['id']:
            raise ValueError('Discovery target goal extraction mismatch')
        compare(task['id'] + ':target_goal', bodies[0][1], goals)
        if task['control_eligible']:
            assembly=task['prefix']+task['reference_fragment']+task['suffix']
            compare(task['id'] + ':sanitized_assembly', assembly, sources)
            compare(task['id'] + ':reference_fragment', task['reference_fragment'], sources)
            # No target/predecessor omission: FrontDef is audited again when
            # retained as a human-proved prerequisite in the Lemma2 context.
            for name, body in breadth.goal_bodies(task['prefix']):
                compare(task['id'] + ':context_goal:' + name, body, goals)
    first = candidate['tasks'][0]
    compare('Lemma2:prerequisite_FrontDef_statement_and_proof',
            first['statement'] + first['reference_fragment'], sources)
    paths.update({str(discovery.SOURCE):discovery.SOURCE_SHA,
                  str(discovery.FRONT_SOURCE):discovery.FRONT_SHA})
    for p,h in paths.items():
        checked(p,h)
    after = {n:breadth.sha((ROOT/n).read_bytes()) for n in CODE}
    if before != after:
        raise ValueError('Audit implementation changed')
    report = dict(schema=1, discovered=4, threshold=THRESHOLD,
        source_entries=len(sources), goal_entries=len(goals), official_sources=149,
        development_tasks=4, fresh_evaluation_tasks=14, original18_and_references=True,
        sources_before=before, sources_after=after, input_sha256=paths,
        protected_provenance=provenance, checks=checks,
        overlap_keys=[k for k,v in checks.items() if v['overlap_exclusion']],
        lexical_exclusion_clear=not any(v['overlap_exclusion'] for v in checks.values()),
        training_authorized=False,
        scope='Exact-normalized and lexical Jaccard audit only; not semantic equivalence, proof admission, or unknown-pretraining absence')
    discovery.write(output/'report.json', report)
    return report


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    audit(parser.parse_args().output)
