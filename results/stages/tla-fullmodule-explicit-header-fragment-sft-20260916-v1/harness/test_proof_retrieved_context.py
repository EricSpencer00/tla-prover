from tools.proof_retrieved_context import retrieve, render


def test_reference_answer_and_library_proofs_never_emitted(tmp_path):
    library = tmp_path/'Facts.tla'
    library.write_text('THEOREM Useful == B(x) \\in Nat\nBY LIBRARY_SECRET\n')
    task = dict(prefix='EXTENDS Facts\nLEMMA Bridge == A(x) = B(x)\nBY SECRET\nTHEOREM Target == A(x) \\in Nat\n',
                theorem_name='Target', target_goal='A(x) \\in Nat', reference_fragment='TARGET_SECRET')
    first = retrieve(task, library_roots=[tmp_path])
    assert first['imported_facts'][0]['name'] == 'Useful'
    assert 'SECRET' not in render(first)
    task['reference_fragment'] = 'CHANGED'
    library.write_text(library.read_text().replace('LIBRARY_SECRET', 'CHANGED_PROOF'))
    second = retrieve(task, library_roots=[tmp_path])
    assert render(first) == render(second)
    assert 'BY SMT' not in render(first)


def test_missing_dependency_hash_rejected(tmp_path):
    import pytest
    path = tmp_path/'D.tla'
    path.write_text('D == TRUE')
    with pytest.raises(ValueError):
        retrieve(dict(prefix='', theorem_name='T', dependencies=[str(path)]))
