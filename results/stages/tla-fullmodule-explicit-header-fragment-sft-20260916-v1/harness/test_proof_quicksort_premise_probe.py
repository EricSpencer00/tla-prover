import copy
import json
from pathlib import Path
import pytest
from tools import proof_quicksort_premise_probe as module


def test_actual_train_scope_and_assumptions_preserved():
    task,negative,scope=module.prepare()
    assert task['id']==module.ID and task['split']=='train'
    assert [r['name'] for r in scope['visible_facts']]==['AutomorphismsCompose','PermsOfLemma']
    assert all('BY ' in r['exact_statement_and_proof'] for r in scope['visible_facts'])
    assert 'ASSUME NEW T, NEW s \\in Seq(T), NEW t \\in PermsOf(s), NEW u \\in PermsOf(t)' in negative['prefix']
    assert 'PROVE FALSE' in negative['prefix'] or 'PROVE  FALSE' in negative['prefix']
    assert not scope['search_variants_model_generated'] and not scope['training_authorized']
    assert all(fragment!=task['reference_fragment'].strip() for _,fragment in module.CANDIDATES)


@pytest.fixture
def probe(tmp_path):
    calls=[];audits=[]
    def check(task,fragment,path,current):
        calls.append((task,fragment,path,current))
        negative=path.name=='false_conclusion'
        return dict(sany=1,proof=0 if negative else 1,status='unproved_obligation' if negative else 'proof_success',
            proof_evidence=dict(strict=dict(status='verifier_reject',returncode=10,timed_out=False,certified=False,
                output='[ERROR]: Could not prove or check:\n           ASSUME NEW T\n           PROVE FALSE\n[ERROR]: 1/9 obligations failed.\n')) if negative else {})
    return tmp_path/'probe',calls,audits,check


def test_controls_gate_all_three_separate_search_candidates(probe):
    output,calls,audits,checker=probe
    result=module.run(output,checker=checker,auditor=lambda *a:audits.append(a),identify=lambda t:{'checker':{}})
    assert result['complete'] and result['controls_admitted'] and result['attempted_candidates']==3
    assert len(calls)==len(audits)==5 and result['verified_symbolic_proofs']==3
    assert not result['model_generated_claim'] and result['old_scores_unchanged']
    rows=json.loads((output/'rows.json').read_text())
    assert [r['kind'] for r in rows]==['reference_control','false_control']+['symbolic_premise_search']*3
    assert [r['fragment'] for r in rows[2:]]==[v for _,v in module.CANDIDATES]


@pytest.mark.parametrize('bad_kind',['reference','false_conclusion'])
def test_failed_control_blocks_search_without_dropping_requested_denominator(probe,bad_kind):
    output,calls,_,checker=probe
    def changed(task,fragment,path,current):
        result=checker(task,fragment,path,current)
        if path.name==bad_kind:result.update(sany=None,proof=None,status='unmeasured_infrastructure')
        return result
    summary=module.run(output,checker=changed,auditor=lambda *a:None,identify=lambda t:{'checker':{}})
    assert len(calls)==2 and not summary['controls_admitted'] and not summary['complete']
    assert summary['requested_candidates']==3 and summary['attempted_candidates']==0
    assert all(not r['attempted'] and r['proof'] is None for r in summary['candidates'])


def test_runtime_drift_never_claims_completion(probe):
    output,_,_,checker=probe
    values=iter([{'checker':{}},{'checker':{'changed':True}}])
    with pytest.raises(ValueError,match='identity drift'):
        module.run(output,checker=checker,auditor=lambda *a:None,identify=lambda t:next(values))
    assert not json.loads((output/'summary.json').read_text())['complete']


def test_unknown_search_results_not_relabelled_model_rejections(probe):
    output,_,_,checker=probe
    def unknown(task,fragment,path,current):
        value=checker(task,fragment,path,current)
        if path.name in dict(module.CANDIDATES):value.update(proof=None,status='unmeasured_infrastructure')
        return value
    summary=module.run(output,checker=unknown,auditor=lambda *a:None,identify=lambda t:{'checker':{}})
    assert summary['complete'] and summary['attempted_candidates']==3 and summary['verified_symbolic_proofs']==0
    assert all(r['proof'] is None for r in summary['candidates'])


def test_owned_checker_raw_audit_failure_stops(probe):
    output,_,_,checker=probe
    def reject(*args):raise ValueError('Raw process changed')
    with pytest.raises(ValueError,match='Raw process'):
        module.run(output,checker=checker,auditor=reject,identify=lambda t:{'checker':{}})
    assert json.loads((output/'failure.json').read_text())['complete'] is False
