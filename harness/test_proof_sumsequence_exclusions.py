import pytest
from tools import proof_sumsequence_exclusions as module


@pytest.mark.parametrize('score,exact,expected', [(.649,[],False),(.65,[],True),(.1,['same'],True)])
def test_fixed_overlap_threshold(score,exact,expected):
    assert module.overlap(dict(max_jaccard=score,exact_normalized=exact)) == expected


def test_checked_rejects_changed_input(tmp_path):
    path=tmp_path/'input'; path.write_text('actual')
    with pytest.raises(ValueError,match='hash mismatch'):
        module.checked(path,'0'*64)


def test_audit_keeps_all_targets_and_predecessor(tmp_path,monkeypatch):
    monkeypatch.setattr(module,'population',lambda: ([('x','other')],[('g','unrelated')],{},{}))
    report=module.audit(tmp_path/'report')
    for name in ('FrontDef','Lemma2','Lemma3','Lemma4'):
        assert name+':target_goal' in report['checks']
    assert 'Lemma2:context_goal:FrontDef' in report['checks']
    assert 'Lemma2:prerequisite_FrontDef_statement_and_proof' in report['checks']
    assert not report['training_authorized']
