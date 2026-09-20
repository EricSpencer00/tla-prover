from tools.proof_premise_search import candidates


def test_candidates_only_use_visible_definitions():
    prefix = '---- MODULE X ----\n(* Hidden == FALSE *)\nA == TRUE\nB(x) == x\nTHEOREM Target == A\n'
    got = list(candidates(prefix))
    assert got[:3] == ['BY SMT', 'BY SMT DEF A, B', 'BY DEF A, B']
    assert all('Hidden' not in s and 'Target' not in s for s in got)


def test_no_definitions_still_has_backend_baseline():
    assert list(candidates('THEOREM T == TRUE\n')) == ['BY SMT']


def test_imported_definitions_and_unique_candidates():
    got = list(candidates('EXTENDS Protocol\n', ['State == TRUE\n']))
    assert got == ['BY SMT', 'BY SMT DEF State', 'BY DEF State']
