import copy
import json
import pytest
from tools import proof_original18 as p


def fake_rows():
    return [dict(_module=name, messages=[
        dict(role='developer', content='Generate proof only'),
        dict(role='user', content='```tla\n---- MODULE '+name+' ----\nEXTENDS TLAPS\n'
             'VARIABLE x\nvars == <<x>>\nInit == x = 0\nNext == x\' = x\n'
             'TypeOK == x = 0\nSpec == Init /\\ [][Next]_vars\n'
             'THEOREM ChatTLA_TypeOKSafety == Spec => []TypeOK\n```'),
        dict(role='assistant', content='HIDDEN_REFERENCE_SENTINEL')]) for name in p.MODULES]


@pytest.fixture
def frozen(tmp_path, monkeypatch):
    raw = ('\n'.join(map(json.dumps, fake_rows()))+'\n').encode()
    monkeypatch.setattr(p, 'EVAL_SHA', p.sha(raw))
    monkeypatch.setattr(p, 'git_blob', lambda repository,path: raw)
    monkeypatch.setattr(p, 'libraries', lambda *args: [])
    output = tmp_path/'prepare'
    manifest = p.prepare(tmp_path, output, audit=False)
    return output/'manifest.json', manifest


def test_no_answer_fields_and_exact_source(frozen):
    path, manifest = frozen
    assert 'HIDDEN_REFERENCE_SENTINEL' not in path.read_text()
    assert len(manifest['tasks']) == 18
    for task in manifest['tasks']:
        assert 'reference_fragment' not in task
        assert task['assembled_unproved_sha256'] == p.sha((task['prefix']+task['suffix']).encode())
        assert task['source_sha256'] == p.sha(task['prefix'].encode())
        assert task['split'] == 'original18_test'
    assert p.validate_manifest(manifest) == manifest['tasks']


def test_multiline_assumptions_keep_literal_and_helpers():
    row = dict(module='CircuitBreaker', messages=[dict(role='developer',content='x'),
        dict(role='user',content='```tla\n---- MODULE CircuitBreaker ----\nEXTENDS TLAPS\n'
             'LEMMA Helper == TRUE\nBY SMT\n'
             'THEOREM ChatTLA_TypeOKSafety ==\nASSUME "closed" \\in States\n'
             'PROVE Spec => []TypeOK\n```')])
    task = p.build_task(row)
    assert '"closed"' in task['target_goal']
    assert 'ASSUME "closed" \\in States' in task['prefix']
    assert 'LEMMA Helper == TRUE\nBY SMT' in task['prefix']
    assert not any('ChatTLA_TypeOKSafety' in c for c in task['symbolic_candidates'])


@pytest.mark.parametrize('field,value', [('target_goal','TRUE'),('prefix','bad'),
    ('suffix','\n====\nTHEOREM Secret == TRUE'),('symbolic_candidates',['BY HiddenReference']),
    ('library_sha256',{'invented':'bad'}),('messages',[])])
def test_tampering_rejected_before_run_creation(frozen,tmp_path,field,value):
    path,manifest = frozen; changed=copy.deepcopy(manifest)
    changed['tasks'][0][field]=value
    forged=tmp_path/'forged.json'; forged.write_text(json.dumps(changed))
    with pytest.raises(ValueError,match='reconstruction'):
        p.evaluate(forged,tmp_path/'run',checker=lambda *a,**k:pytest.fail('checker called'))
    assert not (tmp_path/'run').exists()


def test_hash_and_population_rejected(monkeypatch):
    with pytest.raises(ValueError,match='hash'):
        p.public_rows(b'changed')
    raw=b'[]'; monkeypatch.setattr(p,'EVAL_SHA',p.sha(raw))
    with pytest.raises((ValueError,AttributeError),match='population|attribute'):
        p.public_rows(raw)


def test_reduced_population_rejected(frozen):
    _,manifest=frozen; manifest['tasks'].pop()
    with pytest.raises(ValueError,match='reconstruction'):
        p.validate_manifest(manifest)


def test_round_robin_denominator_and_stop_after_success(frozen,tmp_path):
    path,manifest=frozen; calls=[]
    def check(prefix,fragment,suffix,**kwargs):
        name,attempt=kwargs['work_root'].parts[-2:];calls.append((name,int(attempt)))
        passed=name==p.MODULES[0]
        return dict(certified=passed,status='certified' if passed else 'verifier_reject')
    result=p.evaluate(path,tmp_path/'run',checker=check)
    assert calls[:18]==[(n,0) for n in p.MODULES]
    assert all(name!=p.MODULES[0] for name,attempt in calls[18:])
    assert result['requested_tasks']==result['attempted_tasks']==18
    assert result['certified_tasks']==result['first_choice_certified']==1
    assert len(result['task_statuses'])==18


def test_deadline_retains_all_unattempted(frozen,tmp_path):
    path,_=frozen
    result=p.evaluate(path,tmp_path/'short',seconds=1,timeout=5,
                      checker=lambda *a,**k:pytest.fail('must not launch over deadline'))
    assert result['attempted_tasks']==0
    assert result['unattempted_tasks']==18
    assert len(result['task_statuses'])==18


@pytest.mark.parametrize('kwargs',[{'attempts':5},{'timeout':6},{'seconds':361}])
def test_budget_caps(frozen,tmp_path,kwargs):
    with pytest.raises(ValueError,match='Maximum budget'):
        p.evaluate(frozen[0],tmp_path/'bad',**kwargs)
