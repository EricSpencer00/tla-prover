"""Score six fixed-prompt lineage candidates without changing the SANY oracle."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import protected_checkpoint_preflight as preflight
from tools.protected_checkpoint_paired_generation import sha
from tools.protected_paired_sany_score import JAR_SHA, dump, module_name, score

PHASES = ('base', 'parent', 'child')
ROWS = (47, 107)


def validate_records(records, selected):
    expected = {(phase, row) for phase in PHASES for row in ROWS}
    by_key = {(r['phase'], r['row']): r for r in records}
    if len(by_key) != len(records) or not set(by_key).issubset(expected):
        raise ValueError('Duplicate or unexpected lineage candidate')
    for (_, row), record in by_key.items():
        item, encoding = selected[row]
        ids = encoding['input_ids'][:encoding['prompt_tokens']]
        if (sha(record['raw_reply']) != record['raw_reply_sha256'] or
                sha(item['prompt']) != record['base_prompt_sha256'] or
                record['actual_prompt_token_ids'] != ids or
                record['actual_prompt_token_count'] != len(ids) or
                record['actual_prompt_tokens_match_frozen'] is not True):
            raise ValueError('Raw output or actual frozen prompt identity differs')
        mode = record['resolved_decode']
        if (record['generation_seed'] != 20261011 + row * 10 or
                mode['effective_num_beams'] != 1 or mode['effective_do_sample'] is not False or
                mode['effective_mode'] != 'greedy_search' or
                not 0 < len(record['output_token_ids']) <= 1024):
            raise ValueError('Frozen generation contract differs')
    return by_key


def score_candidate(record, output, java, jar):
    text = record['raw_reply']
    try:
        module_name(text)
    except ValueError:
        output.mkdir(parents=True, exist_ok=False)
        (output / 'raw.txt').write_bytes(text.encode())
        result = dict(status='model_contract_reject', candidate_sha256=sha(text),
                      reason='Missing canonical module header; no extraction or repair',
                      sany_invoked=False)
        dump(output / 'result.json', result)
        return result
    return score(text, output, java, jar)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--records', type=Path, required=True)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if preflight.file_sha(args.packet) != preflight.PACKET_SHA:
        raise ValueError('Frozen packet mismatch')
    selected = preflight.protected_rows(json.loads(args.packet.read_bytes()))
    records = [json.loads(p.read_bytes()) for p in sorted(args.records.glob('row-*.json'))]
    by_key = validate_records(records, selected)
    receipt_path = args.records / 'receipt.json'
    receipt = json.loads(receipt_path.read_bytes()) if receipt_path.exists() else None
    if receipt is not None:
        expected = [(phase, row) for phase in PHASES for row in ROWS]
        if (receipt.get('complete') is not True or
                [(r['phase'], r['row']) for r in receipt['records']] != expected or
                any(by_key.get((r['phase'], r['row'])) != r for r in receipt['records'])):
            raise ValueError('Complete receipt differs from six raw records')
    jar = ROOT / 'tools/tla2tools.jar'
    java = shutil.which('java')
    if java is None or preflight.file_sha(jar) != JAR_SHA:
        raise ValueError('Pinned SANY runtime unavailable')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / 'identity.json', dict(packet_sha256=preflight.PACKET_SHA,
         jar_sha256=JAR_SHA, scorer_sha256=preflight.file_sha(__file__),
         classifier_sha256=preflight.file_sha(ROOT / 'harness/proof_ladder_check.py'),
         process_runner_sha256=preflight.file_sha(ROOT / 'harness/proof_owned_process.py'),
         receipt_sha256=preflight.file_sha(receipt_path) if receipt else None,
         raw_record_sha256={p.name: preflight.file_sha(p) for p in args.records.glob('row-*.json')}))
    controls = []
    for row, (item, _) in selected.items():
        reference = item['response']
        if sha(reference) != item['response_sha256']:
            raise ValueError('Control digest mismatch')
        negative = re.sub(r'(?m)^={4,}\s*$', 'SyntaxNegativeControl == )\n====', reference)
        if negative == reference:
            raise ValueError('Negative control injection failed')
        for label, text in [('reference', reference), ('negative', negative)]:
            result = score(text, output / 'controls' / f'{row}-{label}', java, jar)
            controls.append(dict(row=row, label=label, **result))
    dump(output / 'controls.json', controls)
    controls_ok = all(r['status'] == ('pass' if r['label'] == 'reference' else
                                    'model_sany_reject') for r in controls)
    outcomes = []
    for phase in PHASES:
        for row in ROWS:
            record = by_key.get((phase, row))
            result = (score_candidate(record, output / 'candidates' / f'{row}-{phase}', java, jar)
                      if record else dict(status='unmeasured_missing'))
            outcomes.append(dict(phase=phase, row=row, **result))
    dump(output / 'rows.json', outcomes)
    summary = dict(controls_ok=controls_ok, requested=6, observed=len(records),
        generation_receipt_complete=bool(receipt),
        counts={phase: dict(Counter(r['status'] for r in outcomes if r['phase'] == phase))
                for phase in PHASES},
        input_transform='none; no extraction, repair or reference conditioning',
        scope='two TRAIN-row checkpoint lineage diagnostic; not unseen quality gate',
        gate_claim=False, model_improvement_claim=False)
    dump(output / 'summary.json', summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == '__main__':
    main()
