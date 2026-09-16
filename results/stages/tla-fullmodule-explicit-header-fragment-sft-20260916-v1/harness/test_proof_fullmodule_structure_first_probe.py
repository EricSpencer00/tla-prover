"""Lightweight tests for the CPU-only structure-first decomposition."""

from tools import proof_fullmodule_structure_first_probe as probe


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
