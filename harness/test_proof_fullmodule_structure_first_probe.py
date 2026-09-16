"""Lightweight tests for the CPU-only structure-first decomposition."""

from tools import proof_fullmodule_structure_first_probe as probe
from tools import proof_fullmodule_streaming_sft_train as stream_worker
from tools import fullmodule_structure_first_independent_audit as audit
from tools.proof_fullmodule_streaming_parser_admission import ModuleStream


def test_decompose_is_lossless_and_ignores_indented_let_bindings():
    text = (
        '---- MODULE Demo ----\n'
        'EXTENDS Naturals\n'
        'CONSTANT K\n'
        '\n'
        'Init ==\n'
        '    LET local == 1 IN local = 1\n'
        '\n'
        'Next(x) == x + 1\n'
        '====\n'
    )
    structure = probe.decompose(text)
    assert structure['module_name'] == 'Demo'
    assert structure['operator_count'] == 2
    assert [part['operator_name'] for part in structure['parts']
            if part['kind'] == 'operator'] == ['Init', 'Next']
    assert structure['reconstruction_exact'] is True
    assert structure['reconstructed_sha256'] == probe.sha(text.encode())
    assert structure['largest_operator_char_count'] < len(text)


def test_decompose_keeps_comments_and_footer_bytes_exact():
    text = (
        '\n'
        '---------------- MODULE Demo2 ----------------\n'
        '(* declaration comment *)\n'
        '\n'
        'Spec == TRUE\n'
        '\n'
        '\\* trailing comment\n'
        '========\n'
        '\n'
    )
    structure = probe.decompose(text)
    assert structure['module_name'] == 'Demo2'
    assert structure['parts'][-1]['kind'] == 'footer'
    assert ''.join(text[p['start_char']:p['end_char']]
                   for p in structure['parts']) == text


def test_matched_stream_segments_are_lossless_and_prompt_identity_is_shared():
    response = (
        '---- MODULE Demo ----\n'
        'EXTENDS Naturals\n'
        'Init == TRUE\n'
        'Next == TRUE\n'
        '====\n'
    )
    structure = probe.decompose(response)
    segments = stream_worker.stream_segments(response, structure, count=4)
    assert len(segments) == 4
    assert ''.join(segments) == response
    for segment, prefix in enumerate(
            (''.join(segments[:i]) for i in range(len(segments)))):
        prompt = stream_worker.stream_prompt('TASK', 'Demo', segment, prefix)
        assert f'SEGMENT: {segment}\n' in prompt
        if prefix:
            assert stream_worker.sha(prefix.encode()) in prompt
            assert prompt.endswith('Continue immediately after the prefix.\n')
        else:
            assert prompt.endswith('Begin with the exact module header line.\n')


def test_independent_audit_does_not_score_rejected_partial_stream():
    raw = 'not a module'
    record = {
        'row': 47,
        'plan': {
            'raw_reply': '',
            'raw_reply_sha256': audit.sha('').lower(),
        },
        'parts': [{
            'segment': 0,
            'generation': {
                'raw_reply': raw,
                'raw_reply_sha256': audit.sha(raw),
            },
        }],
        'stream_reject': 'module stream must begin with one header',
        'assembled_sha256': None,
        'assembled_char_count': 0,
    }
    assert audit.verify_record(record, record) == ''


def test_incremental_stream_rejects_structural_corruption():
    stream = ModuleStream()
    stream.feed('---- MODULE Demo ----\n')
    stream.feed('Init == TRUE\n')
    stream.feed('====\n')
    assert stream.finish() == '---- MODULE Demo ----\nInit == TRUE\n====\n'
    for bad in (
            '---- MODULE Demo ----\n====\nInit == TRUE\n',
            '---- MODULE Demo ----\n---- MODULE Inner ----\n====\n',
            '---- MODULE Demo ----\n```\n====\n'):
        try:
            candidate = ModuleStream()
            candidate.feed(bad)
            candidate.finish()
        except ValueError:
            pass
        else:
            raise AssertionError('stream accepted structural corruption')
