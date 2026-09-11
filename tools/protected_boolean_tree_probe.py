"""Bounded representation diagnostic, not a full TLA+ language or model result.

Check an explicit Boolean tree renderer against an independent truth-table
oracle using real SANY and TLC. No raw TLA+ fragments or reference answers are
accepted by the renderer. The negative control deliberately swaps AND for OR.
"""
import argparse
import itertools
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_owned_process import run_owned
from tools.protected_checkpoint_preflight import file_sha
from tools.protected_paired_sany_score import JAR_SHA, dump, score

OPS = {'and': '/\\', 'or': '\\/', 'implies': '=>'}


def render(tree):
    if type(tree) is bool:
        return 'TRUE' if tree else 'FALSE'
    if type(tree) is str and tree in ('p', 'q', 'r'):
        return tree
    if type(tree) not in (list, tuple) or not tree:
        raise ValueError('Not a supported Boolean tree')
    if tree[0] == 'not' and len(tree) == 2:
        return '(~' + render(tree[1]) + ')'
    if type(tree[0]) is str and tree[0] in OPS and len(tree) == 3:
        return '(' + render(tree[1]) + ' ' + OPS[tree[0]] + ' ' + render(tree[2]) + ')'
    raise ValueError('Unsupported operator or arity')


def evaluate(tree, environment):
    """Independent Python Boolean oracle, never parses the emitted TLA+."""
    if type(tree) is bool:
        return tree
    if type(tree) is str:
        return environment[tree]
    if tree[0] == 'not':
        return not evaluate(tree[1], environment)
    left, right = evaluate(tree[1], environment), evaluate(tree[2], environment)
    if tree[0] == 'and':
        return left and right
    if tree[0] == 'or':
        return left or right
    if tree[0] == 'implies':
        return (not left) or right
    raise ValueError('Unknown oracle operation')


def cases():
    leaves = ['p', 'q', 'r', True, False]
    return (leaves + [('not', a) for a in leaves]
            + [(op, a, b) for op in OPS for a in leaves for b in leaves]
            + [(op, (inner, 'p', 'q'), 'r') for op in OPS for inner in OPS]
            + [(op, 'p', (inner, 'q', 'r')) for op in OPS for inner in OPS])


def module(trees, negative=False):
    lines = ['---- MODULE BooleanTreeProbe ----', 'VARIABLE tick']
    invariants = []
    for index, tree in enumerate(trees):
        expression = render(tree)
        if negative:
            expression = expression.replace('/\\', '\\/')
        lines.append(f'E{index}(p, q, r) == {expression}')
        # Exhaustive truth-table DNF is structurally different from render().
        terms = []
        for values in itertools.product((False, True), repeat=3):
            env = dict(zip(('p', 'q', 'r'), values))
            if evaluate(tree, env):
                terms.append('(' + ' /\\ '.join(name if env[name] else '~' + name
                                               for name in ('p', 'q', 'r')) + ')')
        oracle = '(' + ' \\/ '.join(terms) + ')' if terms else 'FALSE'
        invariants.append(f'  /\\ (\\A p, q, r \\in BOOLEAN : E{index}(p, q, r) = {oracle})')
    # Depend on the real state so TLC checks an invariant instead of rejecting
    # the negative control as a constant-FALSE configuration before exploration.
    lines += ['Init == tick = FALSE', "Next == tick' = ~tick", 'Correct ==',
              '  /\\ tick \\in BOOLEAN']
    return '\n'.join(lines + invariants + ['====', ''])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    jar = ROOT / 'tools/tla2tools.jar'
    if file_sha(jar) != JAR_SHA:
        raise ValueError('Checker mismatch')
    trees = cases()
    dump(output / 'trees.json', trees)
    results = {}
    for label, negative in [('positive', False), ('negative_and_to_or', True)]:
        work = output / label
        sany = score(module(trees, negative), work, shutil.which('java'), jar)
        (work / 'BooleanTreeProbe.cfg').write_text('INIT Init\nNEXT Next\nINVARIANT Correct\n')
        command = [shutil.which('java'), '-cp', str(jar), 'tlc2.TLC', '-workers', '1',
                   '-config', 'BooleanTreeProbe.cfg', 'BooleanTreeProbe']
        process = run_owned(command, work, 30)
        dump(work / 'tlc-process.json', process)
        (work / 'tlc.log').write_text(process['output'])
        completed = all(process.get(key) for key in
                        ('execution_complete', 'cleanup_complete', 'output_complete'))
        tlc_pass = (completed and process['returncode'] == 0 and
                    'Model checking completed. No error has been found.' in process['output']
                    and '2 distinct states found' in process['output'])
        rejected = (completed and process['returncode'] != 0 and
                    'Invariant Correct is violated' in process['output'])
        results[label] = dict(sany=sany['status'], tlc_pass=tlc_pass,
                              invariant_violation=rejected, process_complete=completed)
    summary = dict(trees=len(trees), valuations_per_tree=8, jar_sha256=JAR_SHA,
                   source_sha256=file_sha(__file__), results=results,
                   controls_ok=all(r['sany'] == 'pass' for r in results.values()) and
                       results['positive']['tlc_pass'] and
                       results['negative_and_to_or']['invariant_violation'],
                   model_improvement_claim=False, full_module_coverage=False,
                   gate_claim=False, mask_performance_measured=False,
                   scope='Hand-written Boolean representation diagnostic only; no model run')
    dump(output / 'summary.json', summary)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
