from tools.proof_fact_search import statements, proposals, libraries


def test_excludes_target_later_facts_comments_and_proof_answers():
    source = '''(* LEMMA Hidden == Secret *)
LEMMA Bridge == A(x) = B(x)
 BY SecretProof
THEOREM Target == A(x)
THEOREM Later == Forbidden
'''
    facts = statements(source, 'Target')
    assert facts == [{'name': 'Bridge', 'statement': 'A(x) = B(x)'}]


def test_bridge_statement_retrieval_and_no_answer_lookup():
    prefix = 'LEMMA Bridge == Foo(x) = Bar(x)\n BY HiddenAnswer\nTHEOREM Target == Foo(x) \\in Nat\n'
    got, context = proposals(prefix, 'Target', 'Foo(x) \\in Nat', [],
        ['THEOREM Distractor == Unrelated(y)\nTHEOREM Relevant == Bar(x) \\in Nat\n'])
    assert context['ranked_imported_facts'][0]['name'] == 'Relevant'
    assert 'BY SMT, Bridge, Relevant' in got
    assert not any('HiddenAnswer' in x or 'Target' in x for x in got)
    assert len(got) == len(set(got))


def test_only_explicit_imports(tmp_path):
    for module in ('Public', 'NotImported'):
        (tmp_path/(module+'.tla')).write_text('')
    assert libraries('EXTENDS Public\n(* EXTENDS NotImported *)', [], [tmp_path]) == [tmp_path/'Public.tla']


def test_statement_extraction_stops_before_definitions():
    assert statements('AXIOM Known == TRUE\nHidden == Answer\n') == [{'name':'Known', 'statement':'TRUE'}]


def test_changing_visible_proof_answers_cannot_change_retrieval():
    prefix = 'LEMMA Bridge == Foo(x) = Bar(x)\n BY ANSWER\nTHEOREM Target == Foo(x) \\in Nat\n'
    library = 'THEOREM Relevant == Bar(x) \\in Nat\n BY LIBRARY_ANSWER\n'
    first = proposals(prefix, 'Target', 'Foo(x) \\in Nat', [], [library])
    second = proposals(prefix.replace('ANSWER', 'DifferentProof'), 'Target',
                       'Foo(x) \\in Nat', [], [library.replace('LIBRARY_ANSWER', 'OtherProof')])
    assert first == second


def test_named_assumption_is_a_fact_not_definition():
    assert statements('ASSUME FiniteDomain == IsFiniteSet(Nodes)\nVARIABLE state\n') == [
        {'name': 'FiniteDomain', 'statement': 'IsFiniteSet(Nodes)'}]


def test_real_library_trailer_not_proposed():
    from pathlib import Path
    library = Path('tools/tlapm/lib/tlapm/stdlib/TLAPS.tla').read_text()
    candidates, context = proposals('THEOREM Target == TRUE\n', 'Target', 'TRUE', [], [library])
    assert {f['name'] for f in context['ranked_imported_facts']} == {
        'SetExtensionality', 'NoSetContainsEverything'}
    assert not any('RuleINV' in c or 'RuleInvImplication' in c for c in candidates)


def test_local_library_statement_not_exported_or_joined_to_prior_body():
    library = 'THEOREM Public == TRUE\nLOCAL\nTHEOREM Hidden == FALSE\n'
    assert statements(library, exported=True) == [{'name': 'Public', 'statement': 'TRUE'}]
    assert [f['name'] for f in statements(library)] == ['Public', 'Hidden']


def test_scope_applies_to_imports_and_definitions(tmp_path):
    from tools.proof_premise_search import candidates
    for name in ['Live', 'Hidden', 'Trailer']:
        (tmp_path/(name+'.tla')).write_text('')
    source = ('---- MODULE A ----\nEXTENDS Live,\n Live\nPublic == TRUE\n'
              '---- MODULE Inner ----\nEXTENDS Hidden\nSecret == TRUE\n====\n'
              '====\nEXTENDS Trailer\nGhost == TRUE\n')
    assert libraries(source, [], [tmp_path]) == [tmp_path/'Live.tla']
    assert list(candidates(source)) == ['BY SMT', 'BY SMT DEF Public', 'BY DEF Public']
    local = 'LOCAL\nHidden == TRUE\nPublic == TRUE\n'
    assert 'BY SMT DEF Hidden, Public' in list(candidates(local))
    assert list(candidates('', [local])) == ['BY SMT', 'BY SMT DEF Public', 'BY DEF Public']
