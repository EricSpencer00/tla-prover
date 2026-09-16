"""CPU-only admission probe for structure-first full-module generation.

This diagnostic tests a representation change after whole-response SFT and
identifier weighting failed to move the protected SANY result.  Each clean
W4 reference is split losslessly into a module header, declarations,
top-level operator blocks, and footer.  The probe never loads a model,
touches CUDA, trains, or reads protected response text.  It records exact
part boundaries and independently rechecks every non-protected reference
with the pinned SANY parser.

The output is an admission artifact, not a model result.  A later training
worker may use this representation only if this probe establishes a strict
non-model reduction in the longest sequential generation span while keeping
exact reconstruction and parser controls intact.
"""

import argparse
import hashlib
import json
import re
import statistics
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

PACKET = ROOT / 'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json'
PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
W4_ROWS = tuple(range(42, 169))
VALID = (59, 60, 61, 62, 63, 64)
PROTECTED = (47, 107)
TRAIN = tuple(i for i in W4_ROWS if i not in VALID and i not in PROTECTED)
REFERENCE_ROWS = TRAIN + VALID
SANY_JAR_SHA = '936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88'

# Only column-zero definitions are operators in this diagnostic.  Indented
# LET bindings and expressions containing ``==`` must remain inside the
# enclosing operator block.
MODULE_RE = re.compile(r'^-+ MODULE ([A-Za-z][A-Za-z0-9_]*) -+$')
OPERATOR_RE = re.compile(
    r'^(?P<name>[A-Za-z_][A-Za-z0-9_]*)(?:\s*\([^=\n]*\))?\s*==(?:\s.*)?$')
FOOTER_RE = re.compile(r'^={4,}\s*$')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def _line_content(line):
    return line.rstrip('\r\n')


def _line_starts(lines):
    starts = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += len(line)
    return starts


def _part(text, kind, part_id, start, end, *, operator_name=None,
          line_start=None, line_end=None):
    value = text[start:end]
    return dict(
        id=part_id,
        kind=kind,
        operator_name=operator_name,
        start_char=start,
        end_char=end,
        char_count=len(value),
        byte_count=len(value.encode()),
        line_start=line_start,
        line_end=line_end,
        text_sha256=sha(value.encode()),
    )


def decompose(text):
    """Return a lossless structural partition of one complete TLA+ module."""
    if not isinstance(text, str) or not text:
        raise ValueError('non-empty module text required')
    lines = text.splitlines(keepends=True)
    if not lines:
        raise ValueError('module must contain lines')
    starts = _line_starts(lines)

    headers = [i for i, line in enumerate(lines)
               if MODULE_RE.fullmatch(_line_content(line))]
    if len(headers) != 1:
        raise ValueError('exactly one canonical module header required')
    header_line = headers[0]

    footers = [i for i, line in enumerate(lines)
               if FOOTER_RE.fullmatch(_line_content(line))]
    if len(footers) != 1:
        raise ValueError('exactly one module footer required')
    footer_line = footers[0]
    if footer_line <= header_line:
        raise ValueError('footer must follow module header')
    if any(_line_content(line).strip() for line in lines[footer_line + 1:]):
        raise ValueError('module footer must be the final non-whitespace line')

    operator_lines = []
    for index in range(header_line + 1, footer_line):
        match = OPERATOR_RE.fullmatch(_line_content(lines[index]))
        if match:
            operator_lines.append((index, match.group('name')))
    if not operator_lines:
        raise ValueError('at least one top-level operator definition required')

    header_end = starts[header_line] + len(lines[header_line])
    footer_start = starts[footer_line]
    parts = [_part(text, 'header', 'header', 0, header_end,
                   line_start=0, line_end=header_line + 1)]

    first_operator_line = operator_lines[0][0]
    declaration_start = header_end
    declaration_end = starts[first_operator_line]
    parts.append(_part(text, 'declarations', 'declarations', declaration_start,
                       declaration_end, line_start=header_line + 1,
                       line_end=first_operator_line))

    for position, (line, name) in enumerate(operator_lines):
        start = starts[line]
        next_line = (operator_lines[position + 1][0]
                     if position + 1 < len(operator_lines) else footer_line)
        end = starts[next_line]
        parts.append(_part(text, 'operator', f'operator-{position:03d}-{name}',
                           start, end, operator_name=name,
                           line_start=line, line_end=next_line))

    parts.append(_part(text, 'footer', 'footer', footer_start, len(text),
                       line_start=footer_line, line_end=len(lines)))
    reconstructed = ''.join(text[p['start_char']:p['end_char']] for p in parts)
    if reconstructed != text:
        raise AssertionError('structural partition is not lossless')
    if (parts[0]['start_char'] != 0 or parts[-1]['end_char'] != len(text) or
            any(left['end_char'] != right['start_char']
                for left, right in zip(parts, parts[1:]))):
        raise AssertionError('structural partition has a gap or overlap')

    operator_parts = [p for p in parts if p['kind'] == 'operator']
    full_chars = len(text)
    largest_operator_chars = max(p['char_count'] for p in operator_parts)
    if largest_operator_chars >= full_chars:
        raise ValueError('operator horizon did not shrink below whole module')
    return dict(
        module_name=MODULE_RE.fullmatch(_line_content(lines[header_line])).group(1),
        header_line=header_line,
        footer_line=footer_line,
        operator_count=len(operator_parts),
        parts=parts,
        full_char_count=full_chars,
        full_byte_count=len(text.encode()),
        largest_operator_char_count=largest_operator_chars,
        sequential_horizon_reduction_chars=full_chars - largest_operator_chars,
        sequential_horizon_ratio=largest_operator_chars / full_chars,
        reconstruction_exact=True,
        reconstructed_sha256=sha(reconstructed.encode()),
    )


def _load_packet(path):
    raw = Path(path).read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError('exact immutable full-module packet required')
    packet = json.loads(raw)
    rows = packet.get('rows')
    encodings = packet.get('encodings')
    if not isinstance(rows, list) or not isinstance(encodings, list):
        raise ValueError('packet rows and encodings are required')
    if len(rows) != 169 or len(encodings) != 169:
        raise ValueError('complete 169-row packet required')
    if set(TRAIN) & set(VALID) or set(TRAIN) & set(PROTECTED):
        raise ValueError('row partitions overlap')

    for row in REFERENCE_ROWS:
        value, encoding = rows[row], encodings[row]
        if (value.get('split') != 'train' or not value.get('id', '').startswith('w4-fullmodule:') or
                encoding.get('id') != value.get('id') or
                sha(value.get('prompt', '').encode()) != value.get('prompt_sha256') or
                sha(value.get('response', '').encode()) != value.get('response_sha256') or
                value.get('source_sha256') != value.get('response_sha256') or
                encoding.get('prompt_sha256') != value.get('prompt_sha256') or
                encoding.get('response_sha256') != value.get('response_sha256')):
            raise ValueError(f'row {row} immutable identity mismatch')

    # Metadata-only holdout check.  Deliberately do not access the protected
    # response field: their bytes remain outside the probe's decomposition,
    # controls, and output inventory.
    protected_metadata = []
    for row in PROTECTED:
        value = rows[row]
        if (value.get('split') != 'train' or not value.get('id', '').startswith('w4-fullmodule:') or
                not re.fullmatch(r'[0-9a-f]{64}', value.get('response_sha256', ''))):
            raise ValueError(f'protected row {row} metadata changed')
        protected_metadata.append(dict(
            row=row,
            id=value['id'],
            prompt_sha256=value['prompt_sha256'],
            response_sha256=value['response_sha256'],
            source_sha256=value['source_sha256'],
        ))
    return packet, rows, protected_metadata


def _source_pins():
    return {
        'tools/proof_fullmodule_structure_first_probe.py': file_sha(
            ROOT / 'tools/proof_fullmodule_structure_first_probe.py'),
        'tools/proof_fullmodule_sany_feedback_correction_train.py': file_sha(
            ROOT / 'tools/proof_fullmodule_sany_feedback_correction_train.py'),
    }


def run(args):
    from tools import proof_fullmodule_sany_feedback_correction_train as sany
    packet, rows, protected_metadata = _load_packet(args.packet)
    if file_sha(args.jar) != SANY_JAR_SHA:
        raise ValueError('pinned SANY jar mismatch')
    output = Path(args.output)
    output.mkdir(parents=True, exist_ok=False)

    structures = []
    controls = []
    for row in REFERENCE_ROWS:
        value = rows[row]
        structure = decompose(value['response'])
        structures.append(dict(
            row=row,
            id=value['id'],
            prompt_sha256=value['prompt_sha256'],
            response_sha256=value['response_sha256'],
            module_name=structure['module_name'],
            operator_count=structure['operator_count'],
            full_char_count=structure['full_char_count'],
            full_byte_count=structure['full_byte_count'],
            largest_operator_char_count=structure['largest_operator_char_count'],
            sequential_horizon_reduction_chars=structure['sequential_horizon_reduction_chars'],
            sequential_horizon_ratio=structure['sequential_horizon_ratio'],
            reconstruction_exact=structure['reconstruction_exact'],
            reconstructed_sha256=structure['reconstructed_sha256'],
            parts=structure['parts'],
            train=row in TRAIN,
            validation=row in VALID,
            anchor=row in tuple(i for i in range(42, 59) if i != 47),
        ))
        result = sany.sany_check(
            value['response'], output / f'controls/{row}', args.java, args.jar)
        if result.get('passed') is not True:
            raise ValueError(f'reference SANY control failed for row {row}: {result}')
        controls.append(dict(
            row=row,
            id=value['id'],
            status=result['status'],
            passed=result['passed'],
            result_sha256=file_sha(output / f'controls/{row}/result.json'),
        ))

    full_chars = [x['full_char_count'] for x in structures]
    largest = [x['largest_operator_char_count'] for x in structures]
    ratios = [x['sequential_horizon_ratio'] for x in structures]
    all_exact = all(x['reconstruction_exact'] for x in structures)
    strict_reduction = all(x['largest_operator_char_count'] < x['full_char_count']
                           for x in structures)
    result = dict(
        schema=1,
        kind='fullmodule_structure_first_cpu_admission_v1',
        packet_sha256=PACKET_SHA,
        packet_path=str(Path(args.packet)),
        sany_jar_sha256=SANY_JAR_SHA,
        source_sha256=_source_pins(),
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        reference_rows=list(REFERENCE_ROWS),
        reference_count=len(REFERENCE_ROWS),
        train_reference_count=len(TRAIN),
        validation_reference_count=len(VALID),
        protected_holdout_metadata=protected_metadata,
        structures=structures,
        sany_controls=controls,
        controls_ok=(len(controls) == len(REFERENCE_ROWS) and
                     all(x['passed'] is True for x in controls)),
        all_reconstructions_exact=all_exact,
        all_strict_sequential_horizon_reductions=strict_reduction,
        longest_full_response_chars=max(full_chars),
        longest_operator_block_chars=max(largest),
        median_full_response_chars=statistics.median(full_chars),
        median_operator_block_chars=statistics.median(largest),
        median_sequential_horizon_ratio=statistics.median(ratios),
        max_sequential_horizon_ratio=max(ratios),
        representation_admitted=(all_exact and strict_reduction and
                                  len(controls) == len(REFERENCE_ROWS) and
                                  all(x['passed'] is True for x in controls)),
        measurable_non_model_advantage=(
            'strict per-reference reduction from whole-module character horizon '
            'to the largest sequential operator block; this is a representation '
            'diagnostic and not a quality or model-improvement claim'),
        model_weights_loaded=False,
        cuda_touched=False,
        optimizer_updates=0,
        training_authorized=False,
        gpu_request_authorized=False,
        generated_feedback_loaded=False,
        replay_negatives_loaded=False,
        protected_response_text_used=False,
        protected_targets_never_train=True,
        validation_targets_never_train=True,
        quality_claim=False,
        model_improvement_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(output / 'structure-first-preflight.json', result)
    print(json.dumps(dict(
        preflight='pass' if result['representation_admitted'] else 'reject',
        references=len(REFERENCE_ROWS),
        sany_controls=len(controls),
        median_horizon_ratio=result['median_sequential_horizon_ratio'],
        max_horizon_ratio=result['max_sequential_horizon_ratio'],
        output_sha256=file_sha(output / 'structure-first-preflight.json'),
        training_authorized=False,
        gpu_request_authorized=False,
    )))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=PACKET)
    parser.add_argument('--jar', type=Path, default=ROOT / 'tools/tla2tools.jar')
    parser.add_argument('--java', default='java')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    run(args)


if __name__ == '__main__':
    main()
