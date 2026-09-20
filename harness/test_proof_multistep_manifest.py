from pathlib import Path
import pytest
from tools.proof_multistep_manifest import mask_comments, construct, SELECTION
from tools.proof_family_manifest import construct as old_construct
from harness.proof_fragment_check import validate_fragment


def test_comments_masked_without_changing_strings():
    source = '<1>1. x = "(* literal *) \\* literal" (* outer (* nested *) *)\n BY SMT \\* tail\n'
    result = mask_comments(source)
    assert len(result) == len(source)
    assert result.splitlines()[0].startswith('<1>1. x = "(* literal *) \\* literal"')
    assert 'nested' not in result and 'tail' not in result
    assert result.count('\n') == source.count('\n')


@pytest.mark.parametrize('text', ['(* unclosed', '*)', '"unclosed', '"bad\nstring"'])
def test_bad_lexical_structure_rejected(text):
    with pytest.raises(ValueError):
        mask_comments(text)


def test_escaped_quote_preserved():
    text = 'BY "a\\\"(*not a comment*)"'
    assert mask_comments(text) == text


def test_no_duplicate_selections():
    assert len({x[0] for x in SELECTION}) == len(SELECTION)


def test_real_selection_keeps_development_immutable_and_clean():
    root=Path('/Users/eric/GitHub/lmgpa')
    holdout=Path('/Users/eric/GitHub/tla_benchmark/data/tla_files')
    if not root.exists() or not holdout.exists():
        pytest.skip('official exclusion sources unavailable')
    old=old_construct(root,holdout)
    new=construct(root,holdout)
    assert [t for t in old['tasks'] if t['split']=='development'] == [t for t in new['tasks'] if t['split']=='development']
    old_ids={t['id'] for t in old['tasks']}
    added=[t for t in new['tasks'] if t['id'] not in old_ids]
    assert not any(t['id'].startswith('clock-') for t in added)
    assert len([t for t in new['excluded'] if 'unproved target theorem' in t.get('reason','')]) == 2
    assert len(added)>=6
    assert len({t['source_family'] for t in added})>=2
    for task in added:
        assert task['split']=='train'
        validate_fragment(task['prefix'],task['reference_fragment'],task['suffix'],task['theorem_name'])
        assert all(v['max_jaccard']<.65 for v in task['decontamination'].values())
        assert all(v['max_jaccard']<.65 for v in task['development_similarity'].values())
        lines=Path(task['source_path']).read_text().splitlines(keepends=True)
        lo,hi=task['source_fragment_lines']
        _,end=task['source_theorem_lines']
        expected=''.join(lines[:lo-1])+mask_comments(''.join(lines[lo-1:hi]))+''.join(lines[hi:end])+'\n=============================================================================\n'
        assert task['prefix']+task['reference_fragment']+task['suffix']==expected
        assert '<' in task['reference_fragment'] and '\n' in task['reference_fragment']
