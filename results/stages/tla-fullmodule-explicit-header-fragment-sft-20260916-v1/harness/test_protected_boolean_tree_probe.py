import itertools

import pytest

from tools.protected_boolean_tree_probe import cases, evaluate, module, render


def test_grouping_is_explicit_and_different_trees_stay_different():
    left = ('and', 'p', ('or', 'q', 'r'))
    right = ('or', ('and', 'p', 'q'), 'r')
    assert render(left) == '(p /\\ (q \\/ r))'
    assert render(right) == '((p /\\ q) \\/ r)'
    env = dict(p=False, q=False, r=True)
    assert evaluate(left, env) is False
    assert evaluate(right, env) is True


@pytest.mark.parametrize('tree', ['p /\\ FALSE', 'TRUE', 1, [], ['and', 'p'],
                                    ['or', 'p', 'q', 'r'], ['raw', 'FALSE']])
def test_rejects_injection_and_malformed_trees(tree):
    with pytest.raises(ValueError):
        render(tree)


def test_exhaustive_fixture_and_negative_control_are_not_identical():
    trees = cases()
    assert len(trees) == 103
    for tree in trees:
        assert render(tree)
        for values in itertools.product((False, True), repeat=3):
            assert type(evaluate(tree, dict(zip(('p', 'q', 'r'), values)))) is bool
    assert module(trees) != module(trees, negative=True)
