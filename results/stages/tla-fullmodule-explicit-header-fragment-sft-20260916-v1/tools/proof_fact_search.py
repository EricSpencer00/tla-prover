#!/usr/bin/env python3
"""Bounded symbolic fact retrieval from visible statements, never proof answers."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_fragment_check import _code, certify_fragment
from harness.runner import TLA_LIBRARY
from tools.proof_premise_search import candidates as definition_candidates
from tools.proof_source_scope import top_level_code, named_declarations


def statements(source, target=None, *, exported=False):
    """Restricted top-level declaration index; proof bodies never enter ranking."""
    code = top_level_code(source)
    matches = named_declarations(source)
    result = []
    for i, match in enumerate(matches):
        if match.name == target:
            break  # target and later declarations cannot be cited
        if exported and match.local:
            continue
        body = code[match.body_start:matches[i+1].start if i+1 < len(matches) else len(code)]
        body = re.split(r'(?m)^\s*(?:BY\b|PROOF\b|OBVIOUS\b|<\d+>|----|====|VARIABLES?\b|CONSTANTS?\b|EXTENDS\b|THEOREM\b|LEMMA\b|AXIOM\b)|^[A-Za-z_]\w*\s*(?:\([^\n]*\))?\s*==', body)[0]
        result.append({'name': match.name, 'statement': body.strip()})
    return result


def tokens(source):
    words = re.findall(r'[A-Za-z_]\w*|\d+|<=>|=>', source)
    ignored = {'ASSUME', 'PROVE', 'NEW', 'DOMAIN', 'THEOREM', 'LEMMA', 'in'}
    return {w for w in words if w not in ignored and (len(w) > 1 or w.isdigit())}


def libraries(prefix, dependency_texts, roots):
    """Resolve only explicitly EXTENDS-imported modules, not arbitrary corpus files."""
    modules = []
    for text in [prefix, *dependency_texts]:
        for match in re.finditer(r'(?m)^\s*EXTENDS\s+([A-Za-z_]\w*(?:\s*,\s*[A-Za-z_]\w*)*)', top_level_code(text)):
            modules.extend(re.findall(r'[A-Za-z_]\w*', match[1]))
    paths = []
    for name in dict.fromkeys(modules):
        for root in roots:
            path = Path(root) / (name + '.tla')
            if path.is_file():
                paths.append(path)
                break
    return paths


def proposals(prefix, target, goal, dependency_texts, library_texts):
    local = statements(prefix, target) + [fact for source in dependency_texts
                                        for fact in statements(source, target, exported=True)]
    query = tokens(goal)
    # One-hop statement expansion retrieves the bridge's library operator without
    # looking at the proof used to establish that bridge.
    relevant = [f for f in local if query & tokens(f['statement'])]
    expanded = query | set().union(*(tokens(f['statement']) for f in relevant))
    imported = [f for source in library_texts for f in statements(source, exported=True)]
    def score(fact):
        ts = tokens(fact['statement'])
        return (4 * len(query & ts) + len(expanded & ts)) / (len(ts) + 4) ** .5
    ranked = sorted(imported, key=lambda f: (-score(f), f['name']))
    local_names = list(dict.fromkeys(f['name'] for f in relevant))
    base = list(itertools.islice(definition_candidates(prefix, dependency_texts), 3))
    proposed = list(base)
    for count in (1, 2, 4, 8):
        names = list(dict.fromkeys(local_names + [f['name'] for f in ranked[:count]]))
        if names:
            for backend in ('SMT, ', ''):
                proposed.append('BY ' + backend + ', '.join(names))
    # Single ranked facts avoid irrelevant premise expansion swamping a backend.
    for fact in ranked[:10]:
        names = list(dict.fromkeys(local_names + [fact['name']]))
        proposed.extend(['BY SMT, ' + ', '.join(names), 'BY ' + ', '.join(names)])
    return list(dict.fromkeys(proposed)), {'visible_facts': local, 'ranked_imported_facts': ranked}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--attempts', type=int, default=32)
    parser.add_argument('--timeout', type=int, default=10)
    parser.add_argument('--seconds', type=int, default=300)
    args = parser.parse_args()
    if not (1 <= args.attempts <= 32 and 1 <= args.timeout <= 10 and 0 < args.seconds <= 300):
        parser.error('maximum budgets: 32 attempts/task, 10 seconds/check, 300 total')
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads(args.manifest.read_text())
    tasks = [t for t in manifest['tasks'] if t['split'] == 'development']
    config = dict(method='symbolic visible-statement lexical retrieval; no model or training',
                  hypothesis='Explicit imported theorem facts bridge goals that DEF-only search cannot prove',
                  measurement='strict uncached TLAPS certified repairs per development task; stop on first pass/task',
                  stop='declared attempt and wall limits; every task retained in denominator',
                  attempts_per_task=args.attempts, timeout=args.timeout, seconds=args.seconds,
                  manifest_sha256=hashlib.sha256(args.manifest.read_bytes()).hexdigest(),
                  reference_fragment_used=False, official_benchmark_used=False)
    (args.output/'config.json').write_text(json.dumps(config, indent=2))
    (args.output/'search.py').write_bytes(Path(__file__).read_bytes())
    rows, contexts = [], {}
    started = time.monotonic()
    with (args.output/'rows.jsonl').open('x') as stream:
        for task in tasks:
            dependencies = list(map(Path, task.get('dependencies', [])))
            for dep in dependencies:
                if hashlib.sha256(dep.read_bytes()).hexdigest() != task['dependency_sha256'][str(dep)]:
                    raise ValueError('dependency hash changed')
            dep_texts = [p.read_text() for p in dependencies]
            paths = libraries(task['prefix'], dep_texts, TLA_LIBRARY.split(':'))
            fragments, context = proposals(task['prefix'], task['theorem_name'], task['target_goal'], dep_texts, [p.read_text() for p in paths])
            context['library_sha256'] = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
            context['proposals'] = fragments[:args.attempts]
            contexts[task['id']] = context
            (args.output/'retrieval.json').write_text(json.dumps(contexts, indent=2))
            for attempt, fragment in enumerate(fragments[:args.attempts]):
                if time.monotonic() - started > args.seconds - args.timeout:
                    break
                row = certify_fragment(task['prefix'], fragment, task['suffix'], theorem_name=task['theorem_name'],
                    dependencies=tuple(dependencies), work_root=args.output/'checks'/task['id']/str(attempt), timeout=args.timeout)
                row.update(task=task['id'], attempt=attempt, fragment=fragment)
                rows.append(row)
                stream.write(json.dumps(row)+'\n')
                stream.flush()
                print(json.dumps({k: row[k] for k in ('task','attempt','fragment','certified','status')}), flush=True)
                if row['certified']:
                    break
    summary = dict(tasks=len(tasks), attempted_tasks=len({r['task'] for r in rows}),
                   certified_tasks=len({r['task'] for r in rows if r['certified']}), attempts=len(rows),
                   elapsed_seconds=time.monotonic()-started, **config)
    (args.output/'summary.json').write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
