import copy

import pytest

from tools.proof_leaf_manifest import expand, leaf_spans, sha


SOURCE = ('---- MODULE M ----\nTHEOREM Target == TRUE\n'
          '<1>1. TRUE BY SMT\n<1> QED BY <1>1\n====\n')


def parents():
    start = SOURCE.index('BY SMT')
    base = dict(split='train', prefix=SOURCE[:start], reference_fragment='BY SMT',
                suffix=SOURCE[start+len('BY SMT'):], source_family='train-family',
                source_sha256='source-sha', assembled_sha256=sha(SOURCE.encode()),
                theorem_name='Target', module_name='M', source_path='source.tla', dependencies=[])
    tasks = [dict(copy.deepcopy(base), id='parent'+str(i)) for i in range(17)]
    tasks += [dict(id='dev'+str(i), split='development', source_family='dev-family',
                   source_sha256='dev-sha', prefix='dev'+str(i), suffix='end',
                   reference_fragment='DEV SECRET') for i in range(4)]
    return {'tasks':tasks}


def test_inline_leaf_and_qed_keep_statements_and_boundaries():
    spans, rejected = leaf_spans(SOURCE, 'Target')
    assert not rejected
    assert [s['fragment'] for s in spans] == ['BY SMT', 'BY <1>1']
    assert all(s['inline'] for s in spans)
    for span in spans:
        assert SOURCE[:span['start']]+span['fragment']+SOURCE[span['end']:] == SOURCE
    assert SOURCE[:spans[1]['start']].endswith('<1> QED ')
    assert SOURCE[spans[1]['end']:].startswith('\n====')


def test_only_target_leaves_and_no_comment_string_keywords():
    text = ('---- MODULE M ----\nTHEOREM Earlier == TRUE\nBY SMT\n'
            'THEOREM Target == TRUE\n<1>1. "BY" = "BY"\n'
            '  BY SMT  \\* BY hidden\n<1> QED BY <1>1\n====\n')
    spans, _ = leaf_spans(text, 'Target')
    assert [s['fragment'] for s in spans] == ['BY SMT', 'BY <1>1']
    assert text[spans[0]['end']:].startswith('  \\* BY hidden')


def test_multiline_leaf_retained_as_unsupported_diagnostic():
    text = SOURCE.replace('BY SMT', 'BY First,\n    Second')
    spans, rejected = leaf_spans(text, 'Target')
    assert len(spans) == 1
    assert len(rejected) == 1 and 'multiline' in rejected[0]['reason']


def test_by_defs_is_one_complete_leaf_not_two_keywords():
    text = SOURCE.replace('BY SMT', 'BY DEFS Init, TypeOK')
    spans, rejected = leaf_spans(text, 'Target')
    assert not rejected
    assert spans[0]['fragment'] == 'BY DEFS Init, TypeOK'


def test_dedup_exact_holes_preserves_all_parents_and_dev_bytes():
    parent = parents()
    frozen_dev = copy.deepcopy(parent['tasks'][-4:])
    train, dev, diagnostics = expand(parent)
    assert len(train) == 2
    assert not diagnostics
    assert all(len(t['parents']) == 17 for t in train)
    assert len({t['hole_sha256'] for t in train}) == 2
    assert dev == frozen_dev == parent['tasks'][-4:]
    assert 'DEV SECRET' not in str(train)
    for task in train:
        assert task['prefix']+task['reference_fragment']+task['suffix'] == SOURCE


def test_source_family_leakage_and_changed_parent_rejected():
    parent = parents()
    parent['tasks'][-1]['source_family'] = 'train-family'
    with pytest.raises(ValueError, match='overlap'):
        expand(parent)
    parent = parents()
    parent['tasks'][0]['reference_fragment'] = 'BY Changed'
    with pytest.raises(ValueError, match='hash mismatch'):
        expand(parent)


def test_later_theorem_and_duplicate_target_rejected():
    with pytest.raises(ValueError, match='final theorem'):
        leaf_spans(SOURCE+'THEOREM Other == TRUE\nBY SMT\n', 'Target')
    with pytest.raises(ValueError, match='Exactly one'):
        leaf_spans(SOURCE+SOURCE, 'Target')
