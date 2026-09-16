from tools import proof_fullmodule_header_contract_diagnostic as diagnostic


def test_classify_reply_distinguishes_exact_and_synthetic_headers():
    exact = '---- MODULE Demo ----\nEXTENDS Naturals\n===='
    synthetic = 'MODULE Demo\n\nSEGMENT: 0\nEXTENDS Naturals'

    exact_result = diagnostic.classify_reply(exact, 'Demo')
    synthetic_result = diagnostic.classify_reply(synthetic, 'Demo')

    assert exact_result['canonical_header_admitted'] is True
    assert exact_result['header_module_matches'] is True
    assert exact_result['synthetic_module_preamble'] is False
    assert synthetic_result['canonical_header_admitted'] is False
    assert synthetic_result['synthetic_module_preamble'] is True
    assert synthetic_result['synthetic_segment_marker'] is True


def test_module_header_accepts_reference_dash_width():
    header, module = diagnostic.module_header('-------------------------------- MODULE W4Od1m1p1t1 --------------------------------\n')
    assert module == 'W4Od1m1p1t1'
    assert header.startswith('-------------------------------- MODULE')
