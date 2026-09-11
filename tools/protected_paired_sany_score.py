"""Score every saved paired candidate verbatim, with actual SANY controls.

This is a protected diagnostic, not the full frozen acceptance denominator.
Reference text is used solely as a checker control after generation is complete.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_ladder_check import classify_sany
from harness.proof_owned_process import run_owned
from tools import protected_checkpoint_preflight as preflight
from tools.protected_checkpoint_paired_generation import plan, sha

JAR_SHA = '936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88'


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def module_name(text):
    match = re.match(r'-{4,} MODULE ([A-Za-z0-9_]+) -{4,}\r?\n', text)
    if not match:
        raise ValueError('Missing canonical module header')
    return match.group(1)


def score(text, output, java, jar):
    output.mkdir(parents=True, exist_ok=False)
    name = module_name(text)
    candidate = output / (name + '.tla')
    candidate.write_bytes(text.encode())
    command = [java, '-cp', str(jar), 'tla2sany.SANY', candidate.name]
    process = run_owned(command, output, 30)
    status = classify_sany(process['returncode'], process['output'], process['timed_out'], name)
    if not all(process.get(k) for k in ('execution_complete', 'cleanup_complete', 'output_complete')):
        status = 'unmeasured_process'
    assert preflight.file_sha(candidate) == sha(text)
    (output / 'sany.log').write_text(process['output'])
    dump(output / 'process.json', process)
    result = dict(status=status, candidate_sha256=sha(text), module_name=name,
                  returncode=process['returncode'], log=str(output / 'sany.log'))
    dump(output / 'result.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, required=True)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if preflight.file_sha(args.packet) != preflight.PACKET_SHA:
        raise ValueError('Frozen packet mismatch')
    receipt = json.loads(args.receipt.read_bytes())
    if not receipt.get('complete') or not receipt.get('restored_tensors_exact'):
        raise ValueError('Complete restored-checkpoint receipt required')
    records = receipt['records']
    if [(r['row'], r['arm'], r['generation']) for r in records] != plan():
        raise ValueError('Exactly the frozen eight ordered candidates required')
    selected = preflight.protected_rows(json.loads(args.packet.read_bytes()))
    for record in records:
        if sha(record['raw_reply']) != record['raw_reply_sha256']:
            raise ValueError('Candidate digest mismatch')
        if record['base_prompt_sha256'] != sha(selected[record['row']][0]['prompt']):
            raise ValueError('Prompt digest mismatch')
        filename = f"row-{record['row']}-{record['arm']}-{record['generation']}.json"
        if json.loads((args.receipt.parent / filename).read_bytes()) != record:
            raise ValueError('Individual raw record differs from receipt')
    jar = ROOT / 'tools/tla2tools.jar'
    if preflight.file_sha(jar) != JAR_SHA:
        raise ValueError('SANY jar mismatch')
    java = shutil.which('java')
    if java is None:
        raise ValueError('Java unavailable')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    dump(output / 'identity.json', dict(receipt_sha256=preflight.file_sha(args.receipt),
         packet_sha256=preflight.PACKET_SHA, jar_sha256=JAR_SHA,
         scorer_sha256=preflight.file_sha(__file__),
         classifier_sha256=preflight.file_sha(ROOT / 'harness/proof_ladder_check.py'),
         process_runner_sha256=preflight.file_sha(ROOT / 'harness/proof_owned_process.py'),
         java=java, java_version=run_owned([java, '-version'], ROOT, 10)))
    controls = []
    for row, (item, _) in selected.items():
        reference = item['response']
        if sha(reference) != item['response_sha256']:
            raise ValueError('Reference control digest mismatch')
        # Retain the same canonical name but inject an unmistakable parser error.
        negative = re.sub(r'(?m)^={4,}\s*$', 'SyntaxNegativeControl == )\n====', reference)
        assert negative != reference
        for label, text in [('reference', reference), ('negative', negative)]:
            result = score(text, output / 'controls' / f'{row}-{label}', java, jar)
            controls.append(dict(row=row, label=label, **result))
    dump(output / 'controls.json', controls)
    controls_ok = all(c['status'] == ('pass' if c['label'] == 'reference'
                                    else 'model_sany_reject') for c in controls)
    results = []
    for record in records:
        key = f"{record['row']}-{record['arm']}-{record['generation']}"
        result = score(record['raw_reply'], output / 'candidates' / key, java, jar)
        results.append(dict(row=record['row'], arm=record['arm'], generation=record['generation'],
                            independent_sample=False, **result))
    dump(output / 'rows.json', results)
    counts = {arm: dict(Counter(r['status'] for r in results if r['arm'] == arm))
              for arm in ('existing_decoder', 'grammar_enforced')}
    summary = dict(complete=controls_ok and all(r['status'] in ('pass', 'model_sany_reject') for r in results),
                   controls_ok=controls_ok, requested=8, observed=len(results), counts=counts,
                   input_transform='none; raw UTF-8 bytes written under canonical module name',
                   paired_unique_rows=2, independent_repeats=False,
                   scope='protected diagnostic; rows are labeled train in the frozen packet',
                   gate_claim=False, model_improvement_claim=False)
    dump(output / 'summary.json', summary)
    print(json.dumps(summary, sort_keys=True))


if __name__ == '__main__':
    main()
