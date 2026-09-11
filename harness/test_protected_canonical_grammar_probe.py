from pathlib import Path

import pytest

from tools.grammar_falsereject import make_checker
from tools.protected_canonical_grammar_probe import canonical_grammar


def test_canonical_subset_requires_grouping_and_rejects_raw_lists():
    grammar = canonical_grammar(Path('harness/grammars/tla_module_v1.ebnf').read_text())
    assert 'CANONICAL OUTPUT ONLY' in grammar
    assert 'W4O' not in grammar  # No frozen reference module names baked in.
    accepts = make_checker(grammar)
    module = '---- MODULE Control ----\nF == {expr}\n====\n'
    assert accepts(module.format(expr='TRUE /\\ (FALSE \\/ TRUE)'))
    assert not accepts(module.format(expr='TRUE /\\ FALSE \\/ TRUE'))
    assert not accepts(module.format(expr='/\\ TRUE\n     /\\ FALSE'))


def test_canonical_builder_rejects_source_drift():
    with pytest.raises(ValueError, match='audited v1'):
        canonical_grammar('root ::= "anything"')
