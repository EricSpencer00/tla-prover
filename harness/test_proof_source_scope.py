from pathlib import Path

import pytest

from tools.proof_source_scope import named_declarations, top_level_code


def names(source, exported=False):
    return [d.name for d in named_declarations(source, exported=exported)]


def test_outer_trailer_is_not_lexed():
    source = '---- MODULE A ----\nTHEOREM Public == TRUE\n====\nTHEOREM Fake == FALSE\n(* unterminated\n'
    assert names(source) == ['Public']


def test_nested_modules_hide_facts_but_not_following_outer_facts():
    source = ('---- MODULE A ----\n---- MODULE B ----\nTHEOREM Hidden == TRUE\n'
              '---- MODULE C ----\nTHEOREM Deep == TRUE\n====\n====\n'
              'THEOREM Public == TRUE\n====\nTHEOREM Trailer == TRUE\n')
    assert names(source) == ['Public']


def test_comments_strings_and_crlf_preserve_offsets():
    source = ('---- MODULE A ----\r\n(* nested (* ==== *)\r\n'
              '---- MODULE Fake ---- *)\r\nText == "==== \\\""\r\n'
              '\\* THEOREM Hidden == TRUE\r\nTHEOREM Public == TRUE\r\n====\r\n')
    code = top_level_code(source)
    assert len(code) == len(source)
    assert [(i, c) for i, c in enumerate(code) if c in '\r\n'] == [
        (i, c) for i, c in enumerate(source) if c in '\r\n']
    declaration, = named_declarations(source)
    assert declaration.name == 'Public'
    assert source[declaration.body_start:].startswith(' TRUE')


@pytest.mark.parametrize('separator', [' ', '\n', '\n(* explanation *)\n'])
def test_local_facts_are_visible_only_in_current_module(separator):
    source = 'LOCAL' + separator + 'THEOREM Hidden == TRUE\nOBVIOUS\nTHEOREM Public == TRUE\n'
    assert names(source) == ['Hidden', 'Public']
    assert names(source, exported=True) == ['Public']
    assert named_declarations(source)[0].local


def test_headerless_and_incomplete_prefixes():
    assert names('LEMMA Earlier == TRUE\nTHEOREM Target == TRUE') == ['Earlier', 'Target']
    assert names('---- MODULE A ----\nTHEOREM Target == TRUE') == ['Target']
    assert names('THEOREM Earlier == TRUE\n---- MODULE Inner ----\nTHEOREM Hidden == TRUE') == ['Earlier']


def test_import_lines_are_scoped_without_interpreting_instance():
    source = ('---- MODULE A ----\nEXTENDS Public\nLOCAL INSTANCE Secret\n'
              '---- MODULE B ----\nEXTENDS Hidden\n====\n====\nEXTENDS Trailer\n')
    code = top_level_code(source)
    assert 'EXTENDS Public' in code and 'LOCAL INSTANCE Secret' in code
    assert 'Hidden' not in code and 'Trailer' not in code


@pytest.mark.parametrize('source', ['(* unclosed', '*)', 'Text == "unterminated\n'])
def test_malformed_live_lexical_input_rejected(source):
    with pytest.raises(ValueError):
        top_level_code(source)


def test_actual_tlaps_exports_exclude_obsolete_trailer_rules():
    path = Path(__file__).resolve().parents[1] / 'tools/tlapm/lib/tlapm/stdlib/TLAPS.tla'
    if not path.is_file():
        pytest.skip('local TLAPS installation unavailable')
    assert names(path.read_text(), exported=True) == ['SetExtensionality', 'NoSetContainsEverything']


def test_real_tlaps_accepts_live_export_and_rejects_trailer_export(tmp_path):
    from harness.proof_fragment_check import certify_fragment

    root = Path(__file__).resolve().parents[1]
    if not (root / 'tools/tlapm/bin/tlapm').is_file():
        pytest.skip('local TLAPS installation unavailable')
    prefix = '---- MODULE ScopeControl ----\nEXTENDS TLAPS\nTHEOREM Target == TRUE\n'
    positive = certify_fragment(prefix, 'BY SetExtensionality', '\n====\n',
        theorem_name='Target', work_root=tmp_path / 'positive', timeout=5)
    assert positive['certified'], positive
    negative = certify_fragment(prefix, 'BY RuleINV1', '\n====\n',
        theorem_name='Target', work_root=tmp_path / 'negative', timeout=5)
    assert not negative['certified']
    assert 'Operator "RuleINV1" not found' in negative['output']
