import pytest

from tools.proof_syntax_patch_assembler import apply_patch, receipt


SOURCE = """---- MODULE M ----
EXTENDS Naturals

Init == x = 0
Next == x' = x
====
"""


def test_applies_one_anchored_patch_without_replacing_module_frame():
    candidate = {'op': 'replace', 'anchor': "x' = x", 'replacement': "x' = x + 1"}
    assembled = apply_patch(SOURCE, candidate)
    assert "x' = x + 1" in assembled
    assert assembled.startswith('---- MODULE M ----')
    assert assembled.count('====') == 1
    assert receipt(SOURCE, candidate)['gate_claim'] is False


@pytest.mark.parametrize('candidate, reason', [
    ({'op': 'replace', 'anchor': "x' = x", 'replacement': '---- MODULE N ----'}, 'module framing'),
    ({'op': 'replace', 'anchor': "x' = x", 'replacement': "x' = x\nx' = x"}, 'repeats'),
    ({'op': 'replace', 'anchor': 'missing', 'replacement': 'x'}, 'exactly once'),
])
def test_rejects_full_rewrites_repetition_and_unanchored_patches(candidate, reason):
    with pytest.raises(ValueError, match=reason):
        apply_patch(SOURCE, candidate)
