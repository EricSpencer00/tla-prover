"""Test parser-derived grouping normalization, not learned-model performance.

Only conjunction/disjunction list notation changes. Every other syntax node
must survive re-parsing, modulo parentheses and Boolean associativity. This is
not a general semantic equivalence checker and does not certify TLC or TLAPS.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.protected_checkpoint_preflight import PACKET_SHA, file_sha
from tools.protected_paired_sany_score import JAR_SHA, dump
from tools.protected_syntax_inventory import export, leaves, walk

JUNCTIONS = {'N_ConjList': '/\\', 'N_DisjList': '\\/'}


def junction(op, parts):
    flattened = []
    for part in parts:
        if part[0] == 'junction' and part[1] == op:
            flattened.extend(part[2])
        else:
            flattened.append(part)
    return flattened[0] if len(flattened) == 1 else ('junction', op, tuple(flattened))


def canonical(node):
    kind, children = node['kind'], node['children']
    if kind == 'N_ParenExpr':
        if len(children) != 3 or children[0]['image'] != '(' or children[2]['image'] != ')':
            raise ValueError('Unexpected parenthesized syntax')
        return canonical(children[1])
    if kind in JUNCTIONS:
        if not children or any(len(c['children']) != 2 for c in children):
            raise ValueError('Unexpected junction syntax')
        return junction(JUNCTIONS[kind], [canonical(c['children'][1]) for c in children])
    if kind == 'N_InfixExpr' and len(children) == 3:
        op = leaves(children[1])
        if op in ('/\\', '\\/'):
            return junction(op, [canonical(children[0]), canonical(children[2])])
    # Named operator leaves also carry semantically important images. Never
    # equate '=' with '#' merely because both have kind N_InfixOp.
    return (kind, node['image'] if not children else '', tuple(canonical(c) for c in children))


def digest(tree):
    return hashlib.sha256(json.dumps(canonical(tree), separators=(',', ':')).encode()).hexdigest()


def normalize(text, tree):
    # SANY columns need explicit Unicode/tab handling. Until implemented, these
    # are retained as unsupported, not silently dropped or mis-indexed.
    if not text.isascii() or '\t' in text or '\r' in text:
        raise ValueError('Unsupported column encoding')
    if '\\*' in text or '(*' in text:
        raise ValueError('Comment-preserving junction layout not implemented')
    lines = text.splitlines(keepends=True)
    starts, total = [], 0
    for line in lines:
        starts.append(total)
        total += len(line)

    def span(node):
        start, end = node['start'], node['end']
        lo, hi = starts[start[0] - 1] + start[1] - 1, starts[end[0] - 1] + end[1]
        if not 0 <= lo < hi <= len(text):
            raise ValueError('Invalid SANY source span')
        return lo, hi

    def contains(node):
        return node['kind'] in JUNCTIONS or any(contains(c) for c in node['children'])

    def rewrite(node):
        lo, hi = span(node)
        if node['kind'] in JUNCTIONS:
            operands = []
            for child in node['children']:
                if len(child['children']) != 2 or child['children'][0]['image'] != JUNCTIONS[node['kind']]:
                    raise ValueError('Unexpected junction item')
                operands.append('(' + rewrite(child['children'][1]) + ')')
            return '(' + (' ' + JUNCTIONS[node['kind']] + ' ').join(operands) + ')'
        edits = []
        for child in node['children']:
            if contains(child):
                start, end = span(child)
                if not lo <= start < end <= hi:
                    raise ValueError('Child escapes parent source span')
                edits.append((start, end, rewrite(child)))
        edits.sort()
        if any(a[1] > b[0] for a, b in zip(edits, edits[1:])):
            raise ValueError('Overlapping syntax source spans')
        result, cursor = [], lo
        for start, end, replacement in edits:
            result += [text[cursor:start], replacement]
            cursor = end
        return ''.join(result) + text[cursor:hi]

    lo, hi = span(tree)
    return text[:lo] + rewrite(tree) + text[hi:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if file_sha(args.packet) != PACKET_SHA or file_sha(ROOT / 'tools/tla2tools.jar') != JAR_SHA:
        raise ValueError('Frozen identity mismatch')
    source_summary = json.loads((args.inventory / 'summary.json').read_text())
    if not source_summary['controls_ok'] or not source_summary['source_hashes_match']:
        raise ValueError('Inventory controls invalid')
    if source_summary['java_source_sha256'] != file_sha(ROOT / 'tools/ProverSyntaxTree.java'):
        raise ValueError('Java helper drift')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    classes, jar = args.inventory.resolve() / 'classes', ROOT / 'tools/tla2tools.jar'
    rows = [r for r in json.loads(args.packet.read_bytes())['rows'] if r['response'].startswith('---- MODULE')]
    prior = json.loads((args.inventory / 'rows.json').read_text())
    if len(prior) != len(rows) or any(p['id'] != r['id'] for p, r in zip(prior, rows)):
        raise ValueError('Inventory row set differs')
    results = []
    started = time.monotonic()
    for index, (row, original) in enumerate(zip(rows, prior)):
        if time.monotonic() - started > 180:
            raise TimeoutError('Three-minute round-trip bound; partial ledger retained')
        path = args.inventory / 'references' / str(index) / 'tree.json'
        if original['status'] != 'pass' or original['source_sha256'] != row['response_sha256'] or file_sha(path) != original['tree_sha256']:
            raise ValueError('Original tree provenance mismatch')
        tree = json.loads(path.read_text())
        result = dict(id=row['id'], index=index, original_sha256=row['response_sha256'],
                      junction_lists=sum(n['kind'] in JUNCTIONS for n in walk(tree)))
        try:
            normalized = normalize(row['response'], tree)
            checked = export(normalized, output / 'references' / str(index), classes, jar)
            result.update(checked, changed=normalized != row['response'])
            if checked['status'] == 'pass':
                reparsed = json.loads((output / 'references' / str(index) / 'tree.json').read_text())
                result['original_structure_sha256'] = digest(tree)
                result['normalized_structure_sha256'] = digest(reparsed)
                result['same_structure'] = digest(tree) == digest(reparsed)
                result['remaining_junction_lists'] = sum(n['kind'] in JUNCTIONS for n in walk(reparsed))
        except (ValueError, IndexError) as exc:
            result.update(status='unsupported', reason=str(exc))
        results.append(result)
        dump(output / 'rows.json', results)
    # An intentional AND-to-OR change must remain syntactically legal while
    # producing a different normalized structure. It is not a model output.
    control = '---- MODULE Control ----\nCONSTANTS p, q\nF == p /\\ q\n====\n'
    a = export(control, output / 'control_original', classes, jar)
    b = export(control.replace('/\\', '\\/'), output / 'control_changed', classes, jar)
    mismatch = (a['status'] == b['status'] == 'pass' and
                digest(json.loads((output / 'control_original/tree.json').read_text())) !=
                digest(json.loads((output / 'control_changed/tree.json').read_text())))
    summary = dict(packet_sha256=PACKET_SHA, jar_sha256=JAR_SHA,
                   source_sha256=file_sha(__file__), inventory_summary_sha256=file_sha(args.inventory / 'summary.json'),
                   requested=len(rows), observed=len(results), counts=dict(Counter(r['status'] for r in results)),
                   changed=sum(r.get('changed', False) for r in results),
                   same_structure=sum(r.get('same_structure', False) for r in results),
                   removed_all_lists=sum(r.get('remaining_junction_lists') == 0 for r in results),
                   negative_structure_control_ok=mismatch,
                   model_improvement_claim=False, tlc_claim=False, tlaps_claim=False, gate_claim=False,
                   scope='Reference-format round-trip; same concrete syntax modulo parentheses and associative Boolean notation only')
    dump(output / 'summary.json', summary)
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
