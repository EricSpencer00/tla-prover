"""Check expression-grammar coverage against all whole-module packet references.

Reference controls are never placed into generation inputs. Every eligible
module is ledgered even when SANY or the grammar rejects it.
"""
import argparse
from importlib.metadata import version
import json
from pathlib import Path
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.grammar_falsereject import make_checker
from tools.protected_checkpoint_preflight import PACKET_SHA, file_sha
from tools.protected_paired_sany_score import JAR_SHA, dump, score


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert file_sha(args.packet) == PACKET_SHA
    jar = ROOT / 'tools/tla2tools.jar'
    assert file_sha(jar) == JAR_SHA
    all_rows = json.loads(args.packet.read_bytes())['rows']
    rows = [r for r in all_rows if r['response'].startswith('---- MODULE')]
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    grammar = ROOT / 'harness/grammars/tla_module_v1.ebnf'
    accepts = make_checker(grammar.read_text())
    results = []
    started = time.monotonic()
    for index, row in enumerate(rows):
        if time.monotonic() - started > 180:
            raise TimeoutError('CPU coverage diagnostic exceeds three-minute bound; retain partial ledger')
        result = score(row['response'], output / 'checks' / str(index), shutil.which('java'), jar)
        accepted = accepts(row['response'])
        results.append(dict(id=row['id'], response_sha256=row['response_sha256'],
                            sany=result['status'], grammar_accepts=accepted,
                            false_reject=result['status'] == 'pass' and not accepted))
        dump(output / 'rows.json', results)
    summary = dict(packet_sha256=PACKET_SHA, jar_sha256=JAR_SHA,
                   grammar_sha256=file_sha(grammar), xgrammar_version=version('xgrammar'),
                   scorer_sha256=file_sha(__file__), requested=len(rows), observed=len(results),
                   sany_pass=sum(r['sany'] == 'pass' for r in results),
                   sany_reject=sum(r['sany'] == 'model_sany_reject' for r in results),
                   sany_unknown=sum(r['sany'].startswith('unmeasured') for r in results),
                   false_rejects=sum(r['false_reject'] for r in results),
                   complete=len(results) == len(rows),
                   scope='CPU syntax coverage over existing training packet references; no generation or held-out claim',
                   gate_claim=False)
    dump(output / 'summary.json', summary)
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
