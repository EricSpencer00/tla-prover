import pytest
from tools import proof_sumsequence_extended_exclusions as module


def task():
    return dict(theorem_name='Lemma2a', statement='LEMMA Lemma2a == x = x\n',
        prefix='---- MODULE Test ----\nCONSTANT x\nLEMMA Lemma2a == x = x\n',
        reference_fragment='OBVIOUS\n', suffix='====\n')


def test_exact_target_overlap():
    checks = module.compare_candidates([task()], [('other', 'foo')], [('heldout', 'x = x')])
    assert checks['Lemma2a:target']['overlap_exclusion']
    assert checks['Lemma2a:context_goal:Lemma2a']['overlap_exclusion']


def test_complete_assembly_overlap():
    t = task()
    assembly = t['prefix'] + t['reference_fragment'] + t['suffix']
    checks = module.compare_candidates([t], [('heldout', assembly)], [('other', 'y < 2')])
    assert checks['Lemma2a:assembly']['overlap_exclusion']


def test_missing_prerequisite_rejected():
    t = task()
    t = {k:v.replace('Lemma2a', 'Lemma3') for k,v in t.items()}
    with pytest.raises(ValueError, match='prerequisite inventory'):
        module.compare_candidates([t], [('other', 'foo')], [('other', 'bar')])


def test_predecessor_goal_is_not_omitted():
    t = task()
    t = {k:v.replace('Lemma2a', 'Lemma3') for k,v in t.items()}
    t['prefix'] = ('---- MODULE Test ----\nCONSTANT x\n'
        'LEMMA FrontDef == x > 0\nOBVIOUS\n'
        'LEMMA Lemma2a == x < 3\nOBVIOUS\n' + t['statement'])
    checks = module.compare_candidates([t], [('other', 'foo')], [('protected', 'x < 3')])
    assert checks['Lemma3:context_goal:Lemma2a']['overlap_exclusion']


def test_wrong_target_rejected():
    t = task()
    t['statement'] = 'LEMMA Different == x = x\n'
    with pytest.raises(ValueError, match='target goal'):
        module.compare_candidates([t], [('other', 'foo')], [('other', 'bar')])
