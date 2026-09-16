import json
from pathlib import Path

import pytest

from tools import proof_hierarchical_packet as packet


@pytest.fixture
def controlled(tmp_path):
    source='---- MODULE Tiny ----\nEXTENDS Naturals, TLAPS\nTHEOREM T == 1 = 1\n'
    task=dict(id='tiny',prefix=source,reference_fragment='BY SMT',suffix='\n====\n',
              theorem_name='T',dependencies=[],dependency_sha256={})
    assembled=source+'BY SMT\n====\n'
    task['assembled_sha256']=packet.sha(assembled.encode())
    work=tmp_path/'good'; work.mkdir()
    (work/'Tiny.tla').write_text(assembled)
    log='[INFO]: All 1 obligations proved.\n'
    (work/'tlapm.log').write_text(log)
    inp={k:task[k] for k in ('prefix','suffix','theorem_name')}
    (work/'input.json').write_text(json.dumps(dict(**inp,fragment='BY SMT')))
    badwork=tmp_path/'bad'; badwork.mkdir()
    (badwork/'input.json').write_text(json.dumps(dict(**inp,fragment='OMITTED')))
    good=dict(certified=True,returncode=0,timed_out=False,sha256=task['assembled_sha256'],
              status='pass',expected=True,command=['tlapm','--strict','--nofp','Tiny.tla'],
              output=log,proved=1,total=1,candidate_path=str(work/'Tiny.tla'),workdir=str(work),
              dependency_sha256={})
    bad=dict(certified=False,expected=False,status='contract_reject',workdir=str(badwork),
             sha256=packet.sha((source+'OMITTED\n====\n').encode()))
    return task,good,bad


def test_exact_controls_without_checker(controlled):
    task,good,bad=controlled
    assert packet.check_control(task,good,bad)['proved']==1


@pytest.mark.parametrize('key,value',[
    ('returncode',11),('timed_out',True),('proved',0),('total',0),
    ('command',['tlapm','--strict','Tiny.tla']),('certified',False),
    ('dependency_sha256',{'Missing.tla':'a'*64}),('sha256','0'*64),
])
def test_rejects_invalid_positive(controlled,key,value):
    task,good,bad=controlled; good[key]=value
    with pytest.raises(ValueError):packet.check_control(task,good,bad)


@pytest.mark.parametrize('filename',['Tiny.tla','tlapm.log','input.json'])
def test_rejects_changed_control_artifact(controlled,filename):
    task,good,bad=controlled
    path=Path(good['workdir'])/filename
    path.write_text('{}' if filename=='input.json' else 'changed')
    with pytest.raises(ValueError):packet.check_control(task,good,bad)


def test_rejects_changed_omitted_input(controlled):
    task,good,bad=controlled
    (Path(bad['workdir'])/'input.json').write_text('{}')
    with pytest.raises(ValueError):packet.check_control(task,good,bad)


def test_exact_source_overlap_rejected():
    with pytest.raises(ValueError,match='overlap'):
        packet.compare_population({'train':'VARIABLE x\nInit == x = 0'},
                                  {'train':'x = x'},
                                  {'test':'VARIABLE x\nInit == x = 0'},
                                  {'test':'y = y'})


def test_exact_goal_overlap_rejected():
    with pytest.raises(ValueError,match='overlap'):
        packet.compare_population({'train':'VARIABLE x\nInit == x = 0'},
                                  {'train':'x = x'},
                                  {'test':'CONSTANT N\nNext == N > 12'},
                                  {'test':'x = x'})


def test_requires_nonempty_exclusion_goals():
    with pytest.raises(ValueError,match='Nonempty'):
        packet.compare_population({'x':'x'}, {'x':'x'}, {'y':'y'}, {})


def test_manifest_pinned_before_any_export(tmp_path):
    manifest=tmp_path/'manifest.json'; manifest.write_text('{}')
    with pytest.raises(ValueError,match='frozen17'):
        packet.prepare(manifest,tmp_path/'missing',tmp_path/'out')
    assert not (tmp_path/'out').exists()


def test_packet_real_frozen_metadata_no_checker(tmp_path):
    root=packet.ROOT/'results/runs/proof-multistep-manifest-20260905-v2'
    result=packet.prepare(root/'manifest.json',root/'controls.json',tmp_path/'prepared')
    assert len(result['rows'])==17
    assert result['task_shape']['hierarchical_spans']==11
    assert result['task_shape']['leaf_spans']==6
    assert len({r['source_family'] for r in result['rows']})==3
    assert all(r['split']=='train' for r in result['rows'])
    assert result['evaluation_responses_exported'] is False
    assert {k:len(v) for k,v in result['evidence']['populations'].items()}=={
        'original18':18,'official119':119,'official30':30,'development':4}
    assert result['evidence']['max_jaccard']<.65
    assert not json.loads((tmp_path/'prepared'/'summary.json').read_text())['checker_executed']


def test_changed_local_source_rejected(tmp_path):
    source=tmp_path/'source.tla'; source.write_text('changed')
    with pytest.raises(ValueError,match='changed'):
        packet.checked_text(source,'0'*64)


@pytest.mark.parametrize('timeout,seconds',[(31,600),(30,601),(0,600),(30,0)])
def test_fresh_budget_bounded(tmp_path,timeout,seconds):
    with pytest.raises(ValueError,match='Maximum'):
        packet.fresh_controls(tmp_path/'missing',tmp_path/'out',timeout,seconds)
    assert not (tmp_path/'out').exists()


def test_identity_requires_complete_bound_controls(tmp_path):
    controls=tmp_path/'controls.json'
    controls.write_text(json.dumps([dict(id=str(i),control=label,command=['/example/tlapm'])
        for i in range(17) for label in ('reference','omitted')]))
    path=tmp_path/'identity.json'
    identity={'tlapm_path':'/example/tlapm','binary_sha256':'abc'}
    evidence=dict(complete=True,manifest_sha256='manifest',controls_sha256=packet.file_sha(controls),
                  requested_controls=34,completed_controls=34,before=identity,after=identity)
    path.write_text(json.dumps(evidence))
    assert packet.validate_identity(path,controls,'manifest',current=identity)==evidence
    evidence['complete']=False; path.write_text(json.dumps(evidence))
    with pytest.raises(ValueError,match='Complete'):
        packet.validate_identity(path,controls,'manifest',current=identity)


def test_identity_changes_rejected(tmp_path):
    controls=tmp_path/'controls.json'; controls.write_text('[]')
    path=tmp_path/'identity.json'; identity={'tlapm_path':'/example/tlapm'}
    evidence=dict(complete=True,manifest_sha256='manifest',controls_sha256=packet.file_sha(controls),
                  requested_controls=34,completed_controls=34,before=identity,after=identity)
    path.write_text(json.dumps(evidence))
    with pytest.raises(ValueError,match='changed'):
        packet.validate_identity(path,controls,'manifest',current={'tlapm_path':'/different'})


def test_historical_not_training_ready(tmp_path):
    root=packet.ROOT/'results/runs/proof-multistep-manifest-20260905-v2'
    with pytest.raises(ValueError,match='requires fresh'):
        packet.prepare(root/'manifest.json',root/'controls.json',tmp_path/'prepared',require_training_ready=True)
    assert not (tmp_path/'prepared').exists()


def test_fresh_budget_exhaustion_has_partial_summary(tmp_path,monkeypatch):
    root=packet.ROOT/'results/runs/proof-multistep-manifest-20260905-v2'
    ticks=iter([0,601,602])
    def no_checker(*args,**kwargs):
        pytest.fail('Budget exhausted before checker call')
    with pytest.raises(TimeoutError,match='budget'):
        packet.fresh_controls(root/'manifest.json',tmp_path/'fresh',
            checker=no_checker,identity=lambda:{'stub':True},clock=lambda:next(ticks))
    result=json.loads((tmp_path/'fresh'/'summary.json').read_text())
    assert result['completed_controls']==0
    assert result['complete'] is False
    assert not (tmp_path/'fresh'/'verifier_identity.json').exists()
