"""Read-only tuned120B SANY audit; JSON to stdout, optional isolated replays.

python3 -B tools/sany_diagnostic.py --replay 2
No generation, TLC, ledger edits, or model calls. Replay scratch is temporary.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.staircase import HOLDOUT


def dedup(rows):
    """gate_check keep-first semantics, including api_error replacement."""
    seen = {}
    for row in rows:
        key = (str(row.get('spec')), str(row.get('sample')))
        if key not in seen or (seen[key].get('verdict') == 'api_error'
                               and row.get('verdict') != 'api_error'):
            seen[key] = row
    return list(seen.values())


def sany_section(text):
    return re.split(r'^===== (?!SANY)', text, maxsplit=1, flags=re.M)[0]


PATTERNS = {
    'parse': r'Could not parse module|Parse Error|Lexical error',
    'unknown_operator': r'Unknown operator:',
    'duplicate': r'Multiple declarations or definitions|Multiply-defined|duplicates the one at|already defined|already declared',
    'missing_module': r'Cannot find source file|cannot find source file|Could not find module',
    'level': r'Level error|level error|has both temporal formula and action|exceeds maximum level|must be a state formula|Action-level bound|Temporal formula used',
    'arity': r'wrong number of arguments|Wrong number of arguments|requires \d+ arguments|arity',
    'nonconstant_bound': r'non-constant|nonconstant',
    'unsupported_expression': r'Unsupported expression type',
    'unresolved_symbol': r'Could not find declaration or definition|Couldn.t resolve (?:prefix|infix|postfix) operator',
    'undefined_at': r'@ used where its meaning is not defined',
    'precedence': r'Precedence conflict',
}


def classify(text):
    tags = [k for k, pat in PATTERNS.items() if re.search(pat, text)]
    return tags or ['other_or_unavailable']


def artifact(run, row, field):
    raw = row.get(field)
    if not raw:
        return None
    path = Path(raw)
    local = run / ('logs' if field == 'log_path' else 'candidates') / path.name
    for p in (local, path if path.is_absolute() else run / path):
        if p.is_file():
            return p
    return None


def replay(run, row, lint=False):
    from harness.runner import build_module_index, check_sany, local_deps, module_name
    from tools.lint_repair_probe import lint as apply_lint
    path = artifact(run, row, 'candidate_path')
    if path is None:
        return {'error': 'candidate unavailable'}
    source = path.read_text()
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if row.get('candidate_sha256') and digest != row['candidate_sha256']:
        return {'error': 'candidate hash mismatch', 'actual_sha256': digest}
    config = json.loads((run / 'config.json').read_text())
    corpus = Path(config.get('corpus', '/Users/eric/GitHub/tla_benchmark/data'))
    if not (corpus / 'tla_files').is_dir():
        return {'error': 'corpus unavailable', 'corpus': str(corpus)}
    _, index = build_module_index(corpus)
    mod = module_name(source)
    if not mod:
        return {'error': 'no module header'}
    variants = [('original', source)]
    fixed, edits = apply_lint(source) if lint else (source, {})
    if edits:
        variants.append(('lint', fixed))
    result = {'candidate_sha256': digest, 'edits': edits}
    for label, text in variants:
        with tempfile.TemporaryDirectory(prefix='sany-diagnostic-') as tmp:
            wd = Path(tmp)
            (wd / f'{mod}.tla').write_text(text)
            seen = {mod}
            frontier = local_deps(text, index)
            while frontier:
                name = frontier.pop()
                if name in seen:
                    continue
                seen.add(name)
                patch = ROOT / 'corpus/configs/patches' / index[name].name
                dep = (patch if patch.exists() else index[name]).read_text()
                (wd / f'{name}.tla').write_text(dep)
                frontier |= local_deps(dep, index) - seen
            status, log, _ = check_sany(wd / f'{mod}.tla', wd, 30)
            result[label] = {'status': status, 'classes': classify(log) if status != 'pass' else [], 'log': log}
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--runs-dir', type=Path, default=ROOT / 'results/runs')
    ap.add_argument('--replay', type=int, default=0, help='examples per failure class, including lint comparison')
    ap.add_argument('--case', action='append', default=[], metavar='RUN:SPEC:SAMPLE',
                    help='also replay an exact saved row, including passing controls')
    args = ap.parse_args()
    report = {'runs': {}, 'examples': {}, 'replays': [], 'notes': [
        'A/L only for generation coverage; B reported separately.',
        'Class counts overlap. Unknown operator counts count each symbol once per row.',
        'First is greedy for A, c0r0 for L; API retries follow gate dedup.',
        'Each ledger is read once; hashes identify the exact bytes, including active-run snapshots.',
    ]}
    union = set()
    groups = defaultdict(list)
    cases = {}
    for run in sorted(args.runs_dir.iterdir()):
        ledger = run / 'rows.jsonl'
        if not ledger.is_file() or run.name.startswith(('QUARANTINE', 'smoke', 'drytest', 'ABORTED')):
            continue
        if 'w4dgm-120b' not in run.name:
            continue
        blob = ledger.read_bytes()
        rows = []
        malformed = []
        for n, line in enumerate(blob.splitlines(), 1):
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError:
                malformed.append(n)
        unique = dedup(rows)
        scored = [r for r in unique if str(r.get('spec')) in HOLDOUT
                  and str(r.get('sample')) != 'corruption']
        counts, symbols = Counter(), Counter()
        spec_classes = defaultdict(Counter)
        spec_symbols = defaultdict(Counter)
        signatures = Counter()
        by_spec = defaultdict(list)
        missing_logs = 0
        for row in scored:
            spec = str(row['spec'])
            cases[f'{run.name}:{spec}:{row["sample"]}'] = (run, row)
            by_spec[spec].append(row)
            if row.get('sany') in (None, 'pass'):
                continue
            path = artifact(run, row, 'log_path')
            log = sany_section(path.read_text(errors='replace')) if path else ''
            missing_logs += path is None
            tags = classify(log)
            counts.update(tags)
            spec_classes[spec].update(tags)
            unknown = set(re.findall(r"Unknown operator: [`']([^'`]+)['`]", log))
            symbols.update(sorted(unknown))
            spec_symbols[spec].update(sorted(unknown))
            messages = set()
            for block in re.split(r'\n\s*\n', log):
                block = block.strip()
                if not block or block.startswith(('=', '*', 'line ', 'Parsing file', 'Semantic processing', 'Semantic errors', 'Fatal errors', 'tla2sany.', 'In module', 'Unknown location', 'Residual stack', 'File does not exist')) or 'SANY2 Version' in block:
                    continue
                messages.add(re.sub(r'\s+', ' ', block))
            signatures.update(sorted(messages))
            for tag in tags:
                groups[tag].append((run, row))
                report['examples'].setdefault(tag, {
                    'run': run.name, 'spec': spec, 'sample': row['sample'],
                    'log_path': str(path.relative_to(ROOT)) if path and ROOT in path.parents else str(path),
                    'sany_log': log,
                })
        covered = {s for s, rs in by_spec.items() if any(r.get('sany') == 'pass' for r in rs)}
        first = [r for r in scored if str(r.get('sample')) in ('greedy', 'c0r0')]
        frames = sorted({str(r.get('framing')) for r in scored})
        if set(frames) <= {'A', 'L'}:
            union |= covered
        report['runs'][run.name] = {
            'sha256': hashlib.sha256(blob).hexdigest(), 'bytes': len(blob),
            'raw_rows': len(rows), 'duplicate_rows': len(rows) - len(unique),
            'malformed_lines': malformed, 'framing': frames, 'scored_rows': len(scored),
            'sany_status': dict(Counter(str(r.get('sany')) for r in scored)),
            'verdicts': dict(Counter(str(r.get('verdict')) for r in scored)),
            'first_pass': sum(r.get('sany') == 'pass' for r in first), 'first_observed': len(first),
            'covered': len(covered), 'missing': sorted(set(HOLDOUT) - covered, key=int),
            'unobserved': sorted(set(HOLDOUT) - set(by_spec), key=int),
            'failure_classes': dict(counts), 'unknown_operators': dict(symbols.most_common()),
            'message_blocks': dict(signatures.most_common()),
            'phases': {phase: {'rows': len(rs), 'sany_pass': sum(r.get('sany') == 'pass' for r in rs)}
                       for phase, rs in ((phase, [r for r in scored if
                           ('repair' if r.get('framing') == 'B' or (r.get('framing') == 'L' and r.get('round', 0) > 0) else 'generation') == phase])
                           for phase in ('generation', 'repair'))},
            'missing_failure_logs': missing_logs,
            'per_spec': {s: {'rows': len(rs), 'sany_pass': sum(r.get('sany') == 'pass' for r in rs),
                            'first_pass': any(r.get('sany') == 'pass' and str(r.get('sample')) in ('greedy', 'c0r0') for r in rs),
                            'failure_classes': dict(spec_classes[s]), 'unknown_operators': dict(spec_symbols[s].most_common())}
                         for s, rs in by_spec.items()},
        }
    report['generation_union'] = {'covered': len(union), 'missing': sorted(set(HOLDOUT) - union, key=int)}
    for case in args.case:
        if case not in cases:
            ap.error(f'row not found: {case}')
        run, row = cases[case]
        report['replays'].append({'case': case, 'result': replay(run, row, lint=True)})
    seen = set()
    for tag, entries in sorted(groups.items()):
        for run, row in entries[:max(0, args.replay)]:
            key = (run.name, str(row['spec']), str(row['sample']))
            if key in seen:
                continue
            seen.add(key)
            report['replays'].append({'class': tag, 'run': run.name, 'spec': row['spec'],
                                      'sample': row['sample'], 'result': replay(run, row, lint=True)})
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
