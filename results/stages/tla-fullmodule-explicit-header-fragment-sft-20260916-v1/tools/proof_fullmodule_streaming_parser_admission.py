"""CPU-only admission for incremental SANY-oriented module streaming."""

import argparse
import hashlib
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
HEADER = re.compile(r'^-+ MODULE ([A-Za-z_][A-Za-z0-9_]*) -+\s*$')
FOOTER = re.compile(r'^=+\s*$')


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


class ModuleStream:
    """Reject only structural violations that are observable in a prefix."""

    def __init__(self):
        self.text = ''
        self.done = False

    def _check(self):
        if '\x00' in self.text or '```' in self.text:
            raise ValueError('binary or markdown fence in module stream')
        lines = self.text.splitlines()
        if lines and not HEADER.fullmatch(lines[0]):
            raise ValueError('module stream must begin with one header')
        if sum(bool(FOOTER.fullmatch(line)) for line in lines) > 1:
            raise ValueError('duplicate module footer')
        headers = sum(bool(HEADER.fullmatch(line)) for line in lines)
        if headers > 1:
            raise ValueError('nested module header')
        footer_positions = [match.start() for match in re.finditer(
            r'(?m)^=+\s*$', self.text)]
        if footer_positions:
            suffix = self.text[footer_positions[0]:]
            if not re.fullmatch(r'=+\s*', suffix):
                raise ValueError('bytes after module footer')
            self.done = True

    def feed(self, chunk):
        if self.done:
            raise ValueError('stream already finished')
        if not isinstance(chunk, str) or not chunk:
            raise ValueError('non-empty text chunk required')
        self.text += chunk
        self._check()

    def finish(self):
        self._check()
        lines = self.text.splitlines()
        if not lines or not HEADER.fullmatch(lines[0]):
            raise ValueError('complete module header required')
        if sum(bool(FOOTER.fullmatch(line)) for line in lines) != 1:
            raise ValueError('complete module footer required')
        if not self.done:
            raise ValueError('module stream did not reach footer')
        return self.text


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--probe', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    packet = json.loads(args.packet.read_bytes())
    if file_sha(args.packet) != PACKET_SHA:
        raise ValueError('frozen packet mismatch')
    if packet.get('encodings') is None:
        raise ValueError('tokenized clean packet required')
    admission = json.loads(args.probe.read_bytes())
    if (admission.get('packet_sha256') != PACKET_SHA or
            admission.get('all_reconstructions_exact') is not True or
            admission.get('controls_ok') is not True):
        raise ValueError('frozen structure admission required')

    rows = {item['row']: item for item in admission['structures']}
    records = []
    for row in admission['reference_rows']:
        structure = rows[row]
        source = packet['rows'][row]['response']
        stream = ModuleStream()
        for part in structure['parts']:
            stream.feed(source[part['start_char']:part['end_char']])
        reconstructed = stream.finish()
        if reconstructed != source:
            raise ValueError(f'lossless stream reconstruction failed at row {row}')
        records.append(dict(
            row=row, module_name=structure['module_name'],
            part_count=len(structure['parts']),
            source_sha256=sha(source), reconstructed_sha256=sha(reconstructed),
            reconstruction_exact=True))

    controls = []
    for label, text in (
            ('early_footer', '---- MODULE Demo ----\n====\nInit == TRUE\n'),
            ('nested_header', '---- MODULE Demo ----\n---- MODULE Inner ----\n====\n'),
            ('markdown_fence', '---- MODULE Demo ----\n```\n====\n')):
        try:
            stream = ModuleStream()
            stream.feed(text)
            stream.finish()
        except ValueError as exc:
            controls.append(dict(label=label, rejected=True, reason=str(exc)))
        else:
            controls.append(dict(label=label, rejected=False))
    if not all(item['rejected'] for item in controls):
        raise ValueError('stream negative controls were accepted')

    result = dict(
        schema=1,
        kind='fullmodule_streaming_parser_cpu_admission_v1',
        packet_sha256=file_sha(args.packet),
        structure_probe_sha256=file_sha(args.probe),
        reference_count=len(records),
        all_reconstructions_exact=True,
        false_reject_controls=True,
        controls=controls,
        model_weights_loaded=False,
        cuda_touched=False,
        optimizer_updates=0,
        training_authorized=False,
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        records=records,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(dict(admission='pass', references=len(records),
                          output_sha256=file_sha(args.output)), sort_keys=True))


if __name__ == '__main__':
    main()
