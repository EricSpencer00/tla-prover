import pytest

from tools import proof_breadth_manifest as b


def test_imports_are_scoped_and_multiline_instance_preserved():
    text=('---- MODULE M ----\nEXTENDS Naturals,\n TLAPS\n'
          'S == "INSTANCE Secret"\n(* INSTANCE Hidden *)\n'
          'I == INSTANCE Real WITH x <- 1\n'
          '---- MODULE Inner ----\nEXTENDS Nope\n====\n====\nEXTENDS Trailer\n')
    assert b.imports(text)==['Naturals','TLAPS','Real']


@pytest.mark.parametrize('declaration',['THEOREM TRUE','LEMMA X == TRUE','AXIOM TRUE','OMITTED'])
def test_dependency_rejects_named_unnamed_theorems_and_admissions(declaration):
    with pytest.raises(ValueError,match='declaration or admission'):
        b.check_dependency('---- MODULE M ----\n'+declaration+'\n====\n')


def test_dependency_does_not_count_trailer_comments_strings_or_nested_exports():
    text=('---- MODULE M ----\nX == "THEOREM TRUE"\n(* OMITTED *)\n'
          '---- MODULE Inner ----\nTHEOREM FALSE\n====\n'
          'ASSUME ParameterType == N \\in Nat\n====\nTHEOREM FALSE\n')
    assert b.check_dependency(text)==['ASSUME ParameterType == N \\in Nat']


def test_goal_bodies_ignore_labels_preserve_assume_prove_and_literals():
    text=('---- MODULE M ----\nTHEOREM First ==\n ASSUME NEW x\n'
          ' PROVE x = "BY literal"\n BY SMT\n'
          'THEOREM Second == TRUE\nOBVIOUS\n====\nTHEOREM Trailer == FALSE\n')
    assert b.goal_bodies(text)==[('First','ASSUME NEW x\n PROVE x = "BY literal"'),('Second','TRUE')]
    a=b.goal_bodies('THEOREM Original == Spec => []TypeOK\nBY PTL')[0][1]
    renamed=b.goal_bodies('THEOREM Different == Spec => []TypeOK\nBY PTL')[0][1]
    assert b.compare(a,[('other',renamed)])['exact_normalized']==['other']


def test_goal_scope_excludes_nested_trailer_and_unnamed_following_theorem():
    text=('---- MODULE M ----\n---- MODULE Inner ----\nTHEOREM Hidden == FALSE\n====\n'
          'THEOREM Visible == TRUE\nOBVIOUS\nTHEOREM TRUE\nOBVIOUS\n====\n'
          'THEOREM Trailer == FALSE\n')
    assert b.goal_bodies(text)==[('Visible','TRUE')]


def test_exact_extract_and_negative_do_not_edit_source():
    text='---- MODULE M ----\nTHEOREM T == 1 = 1\n  BY SMT\nTHEOREM Later == FALSE\nOMITTED\n====\n'
    task=b.extract(text,'T',2,3,3)
    assert task['prefix']+task['reference_fragment']==text[:text.index('THEOREM Later')]
    assert task['contract_rejection'] is None
    assert b.wrong_conclusion(task)=='---- MODULE M ----\nTHEOREM T == FALSE\n'
    assert task['target_goal']=='1 = 1'
    assert task['reference_fragment']=='  BY SMT\n'


def test_boundary_mismatch_rejected():
    text='---- MODULE M ----\nTHEOREM T == TRUE\nBY SMT\nTHEOREM U == TRUE\nBY SMT\n====\n'
    with pytest.raises(ValueError,match='another target'):
        b.extract(text,'T',2,3,5)
    with pytest.raises(ValueError,match='declaration boundary'):
        b.extract(text,'T',3,3,3)


def test_exact_source_six_boundaries_no_checker():
    assert len(b.SELECTION)==6
    rejected=[]
    for rel,theorem,begin,proof,end in b.SELECTION:
        path=b.EXAMPLES/'specifications'/rel
        raw=path.read_bytes()
        assert b.sha(raw)==b.HASHES[rel]
        task=b.extract(raw.decode(),theorem,begin,proof,end)
        assert task['prefix']+task['reference_fragment']==''.join(raw.decode().splitlines(keepends=True)[:end])
        assert len([n for n,_ in b.goal_bodies(task['prefix']) if n==theorem])==1
        if task['contract_rejection']:
            rejected.append(theorem)
    assert rejected==[]


def test_selection_rejections_never_silently_form_smaller_training_manifest(tmp_path):
    calls=[]
    tasks=[dict(id=str(i),split='train',rejection_reasons=['unsupported']) for i in range(6)]
    def forbidden(*args,**kwargs):
        calls.append(1)
        raise AssertionError('checker called')
    result=b.controls(dict(tasks=tasks),tmp_path,checker=forbidden,identity=lambda:{'runtime':'fake'})
    assert result['requested_train']==6 and result['admitted_train']==0
    assert result['unadmitted_train']==6 and not calls
    assert not (tmp_path/'manifest.json').exists()


@pytest.mark.parametrize('seconds,timeout',[(481,30),(480,31),(0,30),(480,0)])
def test_control_budget_guard(seconds,timeout,tmp_path):
    with pytest.raises(ValueError,match='maximum'):
        b.controls({'tasks':[]},tmp_path,seconds=seconds,timeout=timeout)


@pytest.mark.parametrize('bad_output,bad_rc,accepted',[
    ('Failed to prove obligation',10,True),
    ('Failed to prove obligation: unknown operator',10,False),
    ('Failed to prove obligation',11,False),
    ('Syntax error',10,False),
])
def test_controls_require_intended_failure_and_complete_six(tmp_path,monkeypatch,bad_output,bad_rc,accepted):
    monkeypatch.setattr(b,'control_identity',lambda:{'checker':'pinned'})
    text='---- MODULE M ----\nTHEOREM T == TRUE\nBY SMT\n'
    base=b.extract(text,'T',2,3,3)
    tasks=[dict(base,id=str(i),split='train',theorem_name='T',dependencies=[],dependency_sha256={},rejection_reasons=[]) for i in range(6)]
    calls=[]
    def checker(prefix,*args,**kwargs):
        calls.append(prefix)
        provenance=dict(contract_version=b.CONTRACT_VERSION,dependency_sha256={},
                        sha256=b.sha((prefix+args[0]+args[1]).encode()))
        if 'FALSE' in prefix:
            return dict(provenance,status='verifier_reject',certified=False,returncode=bad_rc,output=bad_output,command=['tlapm','--strict','--nofp'])
        return dict(provenance,status='pass',certified=True,returncode=0,proved=1,total=1,command=['tlapm','--strict','--nofp'])
    result=b.controls(dict(tasks=tasks),tmp_path,checker=checker)
    assert len(calls)==12
    assert result['admitted_train']==(6 if accepted else 0)
    assert (tmp_path/'manifest.json').exists()==accepted


def test_verifier_identity_change_blocks_admission(tmp_path,monkeypatch):
    identities=iter([{'checker':'a'},{'checker':'b'}])
    monkeypatch.setattr(b,'control_identity',lambda:next(identities))
    tasks=[dict(id=str(i),split='train',rejection_reasons=['unsupported']) for i in range(6)]
    result=b.controls(dict(tasks=tasks),tmp_path)
    assert not result['verifier_identity_stable']
    assert not (tmp_path/'manifest.json').exists()
