from pathlib import Path

import pytest

from tools.protected_precedence_probe import controls, prototype


def test_prototype_requires_exact_source_and_separates_boolean_tiers():
    source = Path('harness/grammars/tla_module_v1.ebnf').read_text()
    result = prototype(source, False)
    assert 'NOT production-ready' in result
    assert 'CHILD' not in result
    assert '("/\\\\" _ logical_expr _)+' in result
    assert 'nonlogical_op ::=' in result
    assert '"\\\\land"' not in result.split('nonlogical_op ::=')[1]
    assert '          | op_name\n' not in result
    with pytest.raises(ValueError, match='audited v1'):
        prototype(source + '\n', True)


def test_controls_keep_both_positive_and_negative_nested_syntax():
    by_id = {row['id']: row for row in controls()}
    assert by_id['nested_lists']['expected_pass']
    assert by_id['single_bullet_infix']['expected_pass']
    assert not by_id['mixed_inline']['expected_pass']
    assert by_id['bullet_tail_disjunction']['expected_pass']
    assert {r['producer'] for r in by_id.values()} == {'handwritten_syntax_control'}
