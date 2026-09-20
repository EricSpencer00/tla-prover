#!/usr/bin/env python3
"""Freeze statement-only retrieval context for model proof repair.

No proof bodies, successful search candidates, or reference answers are emitted.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals
from tools.proof_family_manifest import named_goals


def retrieve(task, limit=8, library_roots=None):
    if not 1 <= limit <= 16:
        raise ValueError('statement limit must be 1..16')
    deps = [Path(p) for p in task.get('dependencies', [])]
    for path in deps:
        expected = task.get('dependency_sha256', {}).get(str(path))
        if expected is None or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError('dependency requires a matching frozen hash')
    texts = [p.read_text() for p in deps]
    paths = libraries(task['prefix'], texts, library_roots or TLA_LIBRARY.split(':'))
    goal = task.get('target_goal')
    if not goal:
        declarations = named_goals(task['prefix'])
        if not declarations:
            raise ValueError('target statement missing')
        goal = declarations[-1]
    # proposals() also supports a symbolic baseline; intentionally discard that
    # return value. Model input contains statements only, never its BY answers.
    _, context = proposals(task['prefix'], task['theorem_name'], goal, texts,
                           [path.read_text() for path in paths])
    return dict(visible_facts=context['visible_facts'],
                imported_facts=context['ranked_imported_facts'][:limit],
                library_sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                selection='lexical statements + one-hop visible bridge; no proof bodies or successful candidates',
                reference_fragment_used=False)


def render(context):
    facts = context['visible_facts'] + context['imported_facts']
    return ('\n\nVisible proved statements and assumptions (cite names as facts, '
            'not as definitions; select only those useful to the goal):\n' +
            '\n'.join(f"{f['name']} == {f['statement']}" for f in facts))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--split', choices=['train', 'development'], default='development')
    a = p.parse_args()
    a.output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads(a.manifest.read_text())
    rows = {t['id']:retrieve(t) for t in manifest['tasks'] if t['split'] == a.split}
    if not rows:
        raise ValueError('empty requested split')
    (a.output/'contexts.json').write_text(json.dumps(rows, indent=2)+'\n')
    (a.output/'config.json').write_text(json.dumps(dict(
        manifest_sha256=hashlib.sha256(a.manifest.read_bytes()).hexdigest(), split=a.split,
        tasks=len(rows), tool_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()), indent=2)+'\n')
    (a.output/'builder.py').write_bytes(Path(__file__).read_bytes())
    print(json.dumps(dict(tasks=len(rows), reference_fragment_used=False)))


if __name__ == '__main__':
    main()
