"""Inventory real SANY root syntax on every frozen whole-module reference."""
import argparse
from collections import Counter
import json
from pathlib import Path
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_owned_process import run_owned
from tools.protected_checkpoint_preflight import PACKET_SHA, file_sha
from tools.protected_paired_sany_score import JAR_SHA, dump, module_name


def walk(node):
    yield node
    for child in node['children']:
        yield from walk(child)


def leaves(node):
    if not node['children']:
        return node['image'] if node['kind'] == 'token' else ''
    return ''.join(leaves(c) for c in node['children'])


def inventory(tree):
    counts, operators = Counter(), Counter()
    for node in walk(tree):
        if node['kind'] != 'token':
            counts[node['kind']] += 1
        if node['kind'] in ('N_InfixExpr', 'N_PrefixExpr', 'N_PostfixExpr'):
            index = 0 if node['kind'] == 'N_PrefixExpr' else 1
            if len(node['children']) > index:
                operators[leaves(node['children'][index])] += 1
    return dict(counts), dict(operators)


def complete(process):
    return all(process.get(k) for k in ('execution_complete', 'cleanup_complete', 'output_complete'))


def export(text, output, classes, jar):
    output.mkdir(parents=True, exist_ok=False)
    module = output / (module_name(text) + '.tla')
    module.write_text(text)
    command = [shutil.which('java'), '-cp', str(classes) + ':' + str(jar),
               'ProverSyntaxTree', module.name, 'tree.json']
    process = run_owned(command, output, 30)
    dump(output / 'process.json', process)
    (output / 'sany.log').write_text(process['output'])
    tree_path = output / 'tree.json'
    success = (complete(process) and process['returncode'] == 0 and tree_path.is_file()
               and 'PROVER_TREE_COMPLETE' in process['output'])
    rejected = complete(process) and process['returncode'] == 2 and 'PROVER_TREE_REJECTED' in process['output']
    result = dict(status='pass' if success else 'sany_reject' if rejected else 'unmeasured_export',
                  source_sha256=file_sha(module), tree_sha256=file_sha(tree_path) if success else None)
    if success:
        result['syntax_nodes'], result['operators'] = inventory(json.loads(tree_path.read_text()))
    dump(output / 'result.json', result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    jar = ROOT / 'tools/tla2tools.jar'
    if file_sha(args.packet) != PACKET_SHA or file_sha(jar) != JAR_SHA:
        raise ValueError('Frozen input/checker mismatch')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    classes = output / 'classes'
    classes.mkdir()
    java_source = ROOT / 'tools/ProverSyntaxTree.java'
    compile_result = run_owned([shutil.which('javac'), '-cp', str(jar), '-d', str(classes),
                                str(java_source)], output, 30)
    dump(output / 'compile.json', compile_result)
    if not complete(compile_result) or compile_result['returncode']:
        raise RuntimeError('Java helper did not compile')
    control_texts = {
        'positive': '---- MODULE Control ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\n====\n',
        'negative_parse': '---- MODULE Control ----\nF == )\n====\n',
        'negative_semantic': '---- MODULE Control ----\nF == undeclared\n====\n',
    }
    controls = {name: export(text, output / name, classes, jar) for name, text in control_texts.items()}
    dump(output / 'controls.json', controls)
    rows = [r for r in json.loads(args.packet.read_bytes())['rows'] if r['response'].startswith('---- MODULE')]
    results = []
    started = time.monotonic()
    for i, row in enumerate(rows):
        if time.monotonic() - started > 180:
            raise TimeoutError('Three-minute inventory bound; partial rows preserved')
        result = export(row['response'], output / 'references' / str(i), classes, jar)
        results.append(dict(id=row['id'], index=i, expected_source_sha256=row['response_sha256'], **result))
        dump(output / 'rows.json', results)
    occurrences, modules, operators = Counter(), Counter(), Counter()
    for row in results:
        occurrences.update(row.get('syntax_nodes', {}))
        modules.update(row.get('syntax_nodes', {}).keys())
        operators.update(row.get('operators', {}))
    summary = dict(packet_sha256=PACKET_SHA, jar_sha256=JAR_SHA,
                   java_source_sha256=file_sha(java_source), source_sha256=file_sha(__file__),
                   requested=len(rows), observed=len(results),
                   passed=sum(r['status'] == 'pass' for r in results),
                   unknown=sum(r['status'].startswith('unmeasured') for r in results),
                   rejected=sum(r['status'] == 'sany_reject' for r in results),
                   controls_ok=controls['positive']['status'] == 'pass' and
                       all(controls[k]['status'] == 'sany_reject' for k in ('negative_parse', 'negative_semantic')),
                   source_hashes_match=all(r['source_sha256'] == r['expected_source_sha256'] for r in results),
                   syntax_node_occurrences=dict(occurrences), modules_with_node=dict(modules),
                   operators=dict(operators), full_module_renderer_coverage=False,
                   model_improvement_claim=False, gate_claim=False,
                   scope='Root syntax inventory only; no imported library trees or generated model output')
    dump(output / 'summary.json', summary)
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == '__main__':
    main()
