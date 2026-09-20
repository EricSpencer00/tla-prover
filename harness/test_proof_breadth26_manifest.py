import copy
import json
import pytest
from tools import proof_breadth26_manifest as b


def tasks_fixture():
    text='---- MODULE M ----\nTHEOREM T == ASSUME NEW x \\in Nat PROVE x = x\nBY SMT\n'
    task=b.extract(text,'T',2,3,3)
    tasks=[dict(task,id=str(i),split='train',theorem_name='T',dependencies=[],dependency_sha256={},rejection_reasons=[])
           for i in range(26)]
    return dict(requested_train=26,tasks=tasks,training_authorized=False)


def fake_checker(prefix,fragment,suffix,**kwargs):
    provenance=dict(contract_version=b.CONTRACT_VERSION,dependency_sha256={},timed_out=False,
                    sha256=b.sha((prefix+fragment+suffix).encode()),command=['tlapm','--strict','--nofp'])
    if 'PROVE FALSE' in prefix:
        return dict(provenance,status='verifier_reject',certified=False,returncode=10,proved=0,total=0,
                    output='[ERROR]: Could not prove or check:\n ASSUME NEW x \\in Nat\n PROVE FALSE\n[ERROR]: 1/3 obligations failed.\n')
    return dict(provenance,status='pass',certified=True,returncode=0,proved=3,total=3,output='All 3 obligations proved.')


def test_all_26_exact_boundaries_and_eight_source_hashes():
    assert len(b.SELECTION)==26 and len(b.HASHES)==8
    assert b.HASHES is not b.legacy.HASHES
    for name,theorem,start,proof,end in b.SELECTION:
        _,raw=b.checked_source(name)
        task=b.extract(raw,theorem,start,proof,end)
        assert task['contract_rejection'] is None
        assert task['prefix']+task['reference_fragment']==''.join(raw.splitlines(keepends=True)[:end])


def test_preserve_assumptions_and_new_names_in_false_control():
    task=tasks_fixture()['tasks'][0];before=copy.deepcopy(task)
    mutated=b.wrong_conclusion(task)
    assert 'ASSUME NEW x \\in Nat PROVE FALSE\n' in mutated
    assert task==before and task['reference_fragment']=='BY SMT\n'


def test_plain_goal_mutated_without_source_change():
    task=b.extract('---- MODULE M ----\nTHEOREM T == TRUE\nBY SMT\n','T',2,3,3)
    assert b.wrong_conclusion(task)=='---- MODULE M ----\nTHEOREM T == FALSE\n'


def test_prove_in_comment_or_string_not_a_nested_sequent():
    text='---- MODULE M ----\nTHEOREM T == ASSUME NEW x, x = "PROVE" (* PROVE *) PROVE x = x\nBY SMT\n'
    task=b.extract(text,'T',2,3,3)
    assert 'x = "PROVE" (* PROVE *) PROVE FALSE' in b.wrong_conclusion(task)


def test_nested_sequent_fails_closed():
    text='---- MODULE M ----\nTHEOREM T == ASSUME NEW x PROVE ASSUME NEW y PROVE x = y\nBY SMT\n'
    with pytest.raises(ValueError):b.wrong_conclusion(b.extract(text,'T',2,3,3))


def test_second_assume_before_prove_fails_closed():
    text='---- MODULE M ----\nTHEOREM T == ASSUME NEW x, ASSUME NEW y PROVE x = y\nBY SMT\n'
    with pytest.raises(ValueError):b.wrong_conclusion(b.extract(text,'T',2,3,3))


def test_complete_52_controls_admit_exact26(tmp_path):
    result=b.controls(tasks_fixture(),tmp_path,checker=fake_checker,identity=lambda:{'runtime':'same'})
    assert result['training_authorized'] and result['admitted_train']==26
    assert result['ledgered_controls']==52 and result['completed_controls']==52
    manifest=json.loads((tmp_path/'manifest.json').read_text())
    assert len(manifest['tasks'])==26 and manifest['controls_sha256']==b.sha((tmp_path/'controls.json').read_bytes())


@pytest.mark.parametrize('fault',['extra_failed','missing_false','wrong_rc','parse','timeout','source_hash','dep_hash','nofp','vacuous','checker_exception'])
def test_one_bad_pair_never_emits_subset_training(tmp_path,fault):
    calls=[]
    def checker(*args,**kwargs):
        calls.append(1);r=fake_checker(*args,**kwargs)
        if len(calls)==2:
            if fault=='extra_failed':r['output']=r['output'].replace('1/3','2/3')
            elif fault=='missing_false':r['output']=r['output'].replace('PROVE FALSE','PROVE x = y')
            elif fault=='wrong_rc':r['returncode']=3
            elif fault=='parse':r['output']+='\nUnknown operator\n'
            elif fault=='timeout':r['timed_out']=True
            elif fault=='source_hash':r['sha256']='wrong'
            elif fault=='dep_hash':r['dependency_sha256']={'unknown':'h'}
            elif fault=='nofp':r['command']=['tlapm','--strict']
            elif fault=='vacuous':r.update(status='pass',certified=True,returncode=0)
            elif fault=='checker_exception':raise RuntimeError('unexpected backend failure')
        return r
    result=b.controls(tasks_fixture(),tmp_path,checker=checker,identity=lambda:{'runtime':'same'})
    assert len(calls)==52 and result['admitted_train']==25 and result['requested_train']==26
    assert not result['training_authorized'] and not (tmp_path/'manifest.json').exists()


def test_selection_rejects_still_have_all52_statuses(tmp_path):
    selection=tasks_fixture()
    for task in selection['tasks']:task['rejection_reasons']=['exclusion overlap']
    def forbidden(*args,**kwargs):raise AssertionError('checker must not run')
    result=b.controls(selection,tmp_path,checker=forbidden,identity=lambda:{})
    rows=json.loads((tmp_path/'controls.json').read_text())
    assert result['ledgered_controls']==52 and all(r['status']=='selection_reject' for r in rows)
    assert result['admitted_train']==0 and result['unadmitted_train']==26


def test_budget_exhaustion_ledgers_every_unmeasured_control(tmp_path,monkeypatch):
    ticks=iter([0]+[1801]*60);monkeypatch.setattr(b.time,'monotonic',lambda:next(ticks))
    result=b.controls(tasks_fixture(),tmp_path,checker=fake_checker,identity=lambda:{})
    rows=json.loads((tmp_path/'controls.json').read_text())
    assert len(rows)==52 and all(r['status']=='unmeasured_budget' for r in rows)
    assert result['completed_controls']==0 and result['admitted_train']==0


def test_runtime_or_source_drift_invalidates_all_admission(tmp_path):
    identities=iter([{'runtime':'before'},{'runtime':'changed'}])
    result=b.controls(tasks_fixture(),tmp_path,checker=fake_checker,identity=lambda:next(identities))
    assert not result['verifier_identity_stable'] and result['admitted_train']==0
    assert not (tmp_path/'manifest.json').exists()
    assert all(not r['admitted'] for r in json.loads((tmp_path/'outcomes.json').read_text()))


def test_source_reconstruction_exception_after_controls_invalidates_all(tmp_path):
    calls=[]
    def identity():
        calls.append(1)
        if len(calls)==2:raise ValueError('frozen source hash changed')
        return {'inputs':'original'}
    result=b.controls(tasks_fixture(),tmp_path,checker=fake_checker,identity=identity)
    assert result['ledgered_controls']==52 and result['admitted_train']==0
    assert not (tmp_path/'manifest.json').exists()
    assert 'frozen source hash changed' in json.loads((tmp_path/'verifier_after.json').read_text())['identity_error']


def test_wrong_supplied_selection_digest_rejected_before_checker(tmp_path):
    with pytest.raises(ValueError,match='Supplied selection'):
        b.controls(tasks_fixture(),tmp_path,checker=fake_checker,
                   identity=lambda:{'breadth26_selection_sha256':'wrong'})


@pytest.mark.parametrize('seconds,timeout',[(1801,30),(1800,31),(0,30),(float('nan'),30),(1800,0)])
def test_budget_limits(tmp_path,seconds,timeout):
    with pytest.raises(ValueError):b.controls(tasks_fixture(),tmp_path,seconds=seconds,timeout=timeout)


def test_changed_population_rejected(tmp_path):
    selection=tasks_fixture();selection['tasks'].pop()
    with pytest.raises(ValueError):b.controls(selection,tmp_path)


def test_source_hash_mismatch_fails_closed(monkeypatch,tmp_path):
    (tmp_path/'specifications').mkdir();(tmp_path/'specifications/x.tla').write_text('changed')
    monkeypatch.setattr(b,'EXAMPLES',tmp_path);monkeypatch.setattr(b,'HASHES',{'x.tla':'f'*64})
    with pytest.raises(ValueError,match='source hash changed'):b.checked_source('x.tla')


def test_exclusion_reject_is_ledgered_without_shrinking(monkeypatch):
    original=b.compare
    monkeypatch.setattr(b,'compare',lambda text,population:dict(max_jaccard=1.,nearest='excluded',exact_normalized=['excluded']))
    selection=b.construct()
    assert selection['requested_train']==26 and len(selection['tasks'])==30
    assert selection['rejected_train']==26 and selection['control_eligible']==0
    assert all(t['rejection_reasons'] for t in selection['tasks'] if t['split']=='train')


def test_machine_exclusion_audit_and_family_denominators():
    selection=b.construct();train=[t for t in selection['tasks'] if t['split']=='train']
    assert len(train)==26 and selection['development']==4
    assert len({t['source_family'] for t in train})==4
    assert selection['rejected_train']==0 and not selection['training_authorized']
    assert all('goal_body' in t['decontamination'] and 'assembled' in t['decontamination'] for t in train)
    assert all(t['context_overlap_disclosure'] for t in train)
    assert 'original18_reference_audit' in selection['exclusion_sha256']
