"""Separate canonical-output language diagnostic; never full TLA+ coverage.

Raw list spellings are intentionally excluded. All required reference forms
must have verified structure-preserving equivalents accepted by the grammar.
No references are inserted into model prompts and no model is run here.
"""
import argparse
from importlib.metadata import version
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.grammar_falsereject import make_checker
from tools.protected_checkpoint_preflight import PACKET_SHA, file_sha
from tools.protected_paired_sany_score import dump, module_name
from tools.protected_precedence_probe import prototype


def canonical_grammar(source):
    grammar = prototype(source, nested_lists=False)
    if grammar.count('expr ::= junct_list | logical_expr') != 1:
        raise ValueError('Unexpected prototype expression rule')
    return ('# CANONICAL OUTPUT ONLY: Boolean list spellings intentionally excluded.\n'
            '# Not a drop-in full TLA+ grammar. Validate equivalent reference forms.\n'
            + grammar.replace('expr ::= junct_list | logical_expr', 'expr ::= logical_expr'))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--packet', type=Path, required=True)
    p.add_argument('--roundtrip', type=Path, required=True)
    p.add_argument('--records', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    args = p.parse_args()
    if file_sha(args.packet) != PACKET_SHA:
        raise ValueError('Frozen packet mismatch')
    rows = [r for r in json.loads(args.packet.read_bytes())['rows'] if r['response'].startswith('---- MODULE')]
    verified = json.loads((args.roundtrip / 'rows.json').read_text())
    receipt = json.loads((args.roundtrip / 'summary.json').read_text())
    if (receipt['same_structure'] != len(rows) or receipt['observed'] != len(rows)
            or not receipt['negative_structure_control_ok'] or len(verified) != len(rows)):
        raise ValueError('Incomplete structural round-trip evidence')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    grammar = canonical_grammar((ROOT / 'harness/grammars/tla_module_v1.ebnf').read_text())
    grammar_path = output / 'canonical.ebnf'
    grammar_path.write_text(grammar)
    accepts = make_checker(grammar)
    results = []
    for index, (r, v) in enumerate(zip(rows, verified)):
        path = args.roundtrip / 'references' / str(index) / (module_name(r['response']) + '.tla')
        if (v['id'] != r['id'] or v['original_sha256'] != r['response_sha256']
                or v['status'] != 'pass' or not v['same_structure'] or file_sha(path) != v['source_sha256']):
            raise ValueError('Canonical reference provenance mismatch')
        results.append(dict(id=r['id'], original_sha256=r['response_sha256'],
            canonical_sha256=v['source_sha256'], raw_spelling_accepted=accepts(r['response']),
            equivalent_form_accepted=accepts(path.read_text()),
            structure_preservation_verified=True))
    failures = []
    for path in sorted(args.records.glob('row-*.json')):
        record = json.loads(path.read_text())
        failures.append(dict(file=path.name, source_sha256=file_sha(path),
                             accepted=accepts(record['raw_reply'])))
    dump(output / 'rows.json', results)
    dump(output / 'saved_failure_coverage.json', failures)
    summary = dict(packet_sha256=PACKET_SHA, grammar_sha256=file_sha(grammar_path),
        source_sha256=file_sha(__file__), roundtrip_summary_sha256=file_sha(args.roundtrip / 'summary.json'),
        xgrammar_version=version('xgrammar'), requested=len(rows), observed=len(results),
        equivalent_forms_accepted=sum(r['equivalent_form_accepted'] for r in results),
        raw_spellings_rejected=sum(not r['raw_spelling_accepted'] for r in results),
        saved_failure_records=len(failures), saved_failures_rejected=sum(not r['accepted'] for r in failures),
        full_tla_syntax_coverage=False, exact_remote_runtime_verified=False,
        gate_claim=False, model_improvement_claim=False,
        scope='Canonical-output subset with verified equivalents, not unchanged raw-spelling compatibility')
    dump(output / 'summary.json', summary)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
