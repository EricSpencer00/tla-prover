from pathlib import Path
import pytest
from tools.proof_family_manifest import validate_split, goal_text, named_goals, construct

def test_family_overlap_rejected():
    with pytest.raises(ValueError):
        validate_split([dict(id='a', source_family='x', split='train'), dict(id='b', source_family='x', split='development')])

def test_split_requires_development():
    with pytest.raises(ValueError):
        validate_split([dict(id='a', source_family='x', split='train')])

def test_duplicate_ids_rejected():
    with pytest.raises(ValueError):
        validate_split([dict(id='a', source_family='x', split='train'), dict(id='a', source_family='y', split='development')])

def test_goal_includes_multiline_statement_not_proof():
    text = 'LEMMA T ==\n ASSUME NEW x\n PROVE x = x\n BY SMT\n'
    assert goal_text(text) == 'LEMMA T ==\n ASSUME NEW x\n PROVE x = x'

def test_named_goals_ignore_comment_fake_theorem():
    text = '(* LEMMA Fake == FALSE *)\nLEMMA T == TRUE\nBY SMT\nLEMMA U == TRUE\nOBVIOUS\n'
    assert named_goals(text) == ['LEMMA T == TRUE', 'LEMMA U == TRUE']

def test_real_selection_contract():
    root = Path('/Users/eric/GitHub/lmgpa')
    holdout = Path('/Users/eric/GitHub/tla_benchmark/data/tla_files')
    if not root.exists() or not holdout.exists():
        pytest.skip('real official exclusion sources unavailable')
    manifest = construct(root, holdout)
    validate_split(manifest['tasks'])
    assert len(manifest['tasks']) == 10
    assert sum(t['split']=='development' for t in manifest['tasks']) == 4
    assert manifest['official_tasks_evaluated'] == 0
    assert manifest['excluded'][0]['id'] == 'MajorityProof-family'
    for task in manifest['tasks']:
        assert task['reference_fragment'] == task['reference_fragment'].strip()
        assert all(x['max_jaccard'] < .65 for x in task['decontamination'].values())
        if task['split']=='development':
            assert all(x['max_jaccard'] < .65 for x in task['train_cross_similarity'].values())
