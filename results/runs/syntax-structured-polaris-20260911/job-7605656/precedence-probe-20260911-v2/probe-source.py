"""CPU-only falsification of two Boolean-precedence grammar simplifications.

These are experimental grammars, not complete TLA+ precedence implementations.
Never use a failed variant for model decoding. Score every reference and preserve
raw model failures separately from hand-written syntax controls.
"""
import argparse
import hashlib
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

SOURCE_SHA = '2bcc86946f0a858628f455a3d0648c7117e2b780743e1f25dff82cebd0fb4d67'


def prototype(source, nested_lists):
    """Split Boolean chains; test whether permissive list recursion defeats it."""
    if hashlib.sha256(source.encode()).hexdigest() != SOURCE_SHA:
        raise ValueError('Prototype requires the audited v1 source')
    start = source.index('expr ::= junct_list | infix_chain')
    end = source.index('postfixed ::= ', start)
    child = 'expr' if nested_lists else 'logical_expr'
    replacement = r'''
expr ::= junct_list | logical_expr
junct_list ::= and_list | or_list
and_list ::= ("/\\" _ CHILD _)+
or_list ::= ("\\/" _ CHILD _)+
logical_expr ::= nonlogical (_ and_op _ nonlogical)* (_ low_op _ expr)?
               | nonlogical (_ or_op _ nonlogical)+ (_ low_op _ expr)?
and_op ::= "/\\" | "\\land"
or_op ::= "\\/" | "\\lor"
low_op ::= "=>" | "<=>" | "\\equiv" | "~>" | "-+->"
nonlogical ::= prefixed (_ nonlogical_op _ prefixed)*
prefixed ::= prefix_op _ prefixed | postfixed
'''.replace('CHILD', child)
    result = source[:start] + replacement + source[end:]
    # Bare operator names are allowed in higher-order positions in v1, but
    # allowing them as arbitrary primaries can circumvent a Boolean split.
    # Removing that shortcut may reject valid higher-order code: measure it.
    result = result.replace('          | op_name\n', '')
    start = source.index('infix_op ::= ')
    end = source.index('\n# whitespace', start)
    all_ops = source[start:end]
    higher = all_ops.replace('infix_op ::= ', 'nonlogical_op ::= ', 1)
    higher = higher.replace('"=>" | "<=>" | "\\\\equiv" | "~>" | "-+->"\n'
                            '           | "/\\\\" | "\\\\land" | "\\\\/" | "\\\\lor"\n'
                            '           | ', '', 1)
    higher = higher.replace('           | "-+->" | ', '           | ')
    if higher == all_ops.replace('infix_op ::= ', 'nonlogical_op ::= ', 1):
        raise ValueError('Boolean operator split did not apply')
    result += '\n' + higher + '\n'
    # Do not copy v1's compatibility claim onto a stricter diagnostic grammar.
    result = result[result.index('root ::= '):]
    return ('# EXPERIMENTAL CPU discriminator; NOT production-ready.\n'
            '# Only a Boolean split; other precedences remain permissive.\n'
            '# Source: tla_module_v1.ebnf, SHA256 ' + SOURCE_SHA + '\n' + result)


def controls():
    # These are syntax controls only; never model outputs or training labels.
    examples = [
        ('and_chain', 'TRUE /\\ FALSE /\\ TRUE', True),
        ('or_chain', 'TRUE \\/ FALSE \\/ TRUE', True),
        ('parenthesized_mix', 'TRUE /\\ (FALSE \\/ TRUE)', True),
        ('and_list', '/\\ TRUE\n     /\\ FALSE', True),
        ('or_list', '\\/ TRUE\n     \\/ FALSE', True),
        ('nested_lists', '/\\ TRUE\n     /\\ \\/ FALSE\n        \\/ TRUE', True),
        ('implication', 'TRUE => FALSE /\\ TRUE', True),
        ('quantifier', '\\A x \\in {1, 2} : x = 1 \\/ x = 2', True),
        ('mixed_inline', 'TRUE /\\ FALSE \\/ TRUE', False),
        ('mixed_alias', 'TRUE \\land FALSE \\lor TRUE', False),
        # A one-bullet conjunction can contain an infix disjunction. Actual
        # SANY accepted this in v1; preserve it as a positive control.
        ('single_bullet_infix', '/\\ TRUE\n     \\/ FALSE', True),
        ('conflicting_lists', '/\\ TRUE\n     /\\ FALSE\n     \\/ TRUE', False),
        ('conflicting_lists_reverse', '\\/ TRUE\n     \\/ FALSE\n     /\\ TRUE', False),
        ('missing_conjunct', '/\\ TRUE\n     FALSE', False),
    ]
    return [dict(id=name, expected_pass=valid, producer='handwritten_syntax_control',
                 text='---- MODULE Probe ----\nF == ' + expr + '\n====\n')
            for name, expr, valid in examples]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--records', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if file_sha(args.packet) != PACKET_SHA:
        raise ValueError('Frozen packet mismatch')
    jar = ROOT / 'tools/tla2tools.jar'
    if file_sha(jar) != JAR_SHA:
        raise ValueError('Checker mismatch')
    source_path = ROOT / 'harness/grammars/tla_module_v1.ebnf'
    source = source_path.read_text()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    grammars = dict(v1=source,
                    recursive_lists=prototype(source, True),
                    restricted_lists=prototype(source, False))
    checkers = {}
    for name, grammar in grammars.items():
        (output / (name + '.ebnf')).write_text(grammar)
        checkers[name] = make_checker(grammar)
    items = controls()
    items += [dict(id=r['id'], text=r['response'], producer='frozen_training_reference',
                   expected_pass=True)
              for r in json.loads(args.packet.read_bytes())['rows']
              if r['response'].startswith('---- MODULE')]
    for path in sorted(args.records.glob('row-*.json')):
        record = json.loads(path.read_bytes())
        if hashlib.sha256(record['raw_reply'].encode()).hexdigest() != record['raw_reply_sha256']:
            raise ValueError('Raw candidate mismatch')
        items.append(dict(id=path.name, text=record['raw_reply'],
                          producer='saved_model_candidate', expected_pass=False,
                          source_path=str(path.resolve()), source_sha256=file_sha(path)))
    results = []
    started = time.monotonic()
    for index, item in enumerate(items):
        if time.monotonic() - started > 180:
            raise TimeoutError('Three-minute CPU budget; partial rows retained')
        scored = score(item['text'], output / 'checks' / str(index), shutil.which('java'), jar)
        accepted = {name: checker(item['text']) for name, checker in checkers.items()}
        results.append(dict(item, sany=scored['status'], sha256=scored['candidate_sha256'],
                            accepts=accepted))
        dump(output / 'rows.json', results)
    summary = dict(
        packet_sha256=PACKET_SHA, jar_sha256=JAR_SHA, source_sha256=SOURCE_SHA,
        probe_sha256=file_sha(__file__), xgrammar_version=version('xgrammar'),
        grammar_sha256={name: file_sha(output / (name + '.ebnf')) for name in grammars},
        requested=len(items), observed=len(results),
        controls_ok=all((r['sany'] == 'pass') == r['expected_pass'] and
                        r['sany'] in ('pass', 'model_sany_reject') for r in results),
        counts={name: {
            producer: dict(requested=sum(r['producer'] == producer for r in results),
                false_rejects=sum(r['producer'] == producer and r['sany'] == 'pass' and
                                  not r['accepts'][name] for r in results),
                invalid_accepted=sum(r['producer'] == producer and r['sany'] == 'model_sany_reject'
                                     and r['accepts'][name] for r in results),
                sany_unknown=sum(r['producer'] == producer and
                                 r['sany'] not in ('pass', 'model_sany_reject') for r in results))
            for producer in ('handwritten_syntax_control', 'frozen_training_reference',
                             'saved_model_candidate')} for name in grammars},
        mask_performance_measured=False, gate_claim=False, model_improvement_claim=False,
        scope='CPU grammar falsification only; all references are existing training data')
    dump(output / 'summary.json', summary)
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
