import pytest
from pathlib import Path

from tools.proof_step_candidates import step_candidates


def run(proof, **kwargs):
    return step_candidates('---- MODULE Example ----\nD == TRUE\nTHEOREM Target == TRUE\n' + proof,
                           'Target', **kwargs)


def test_completed_siblings_and_backend_mix():
    candidates, meta = run('<1>a. TRUE\n BY D\n<1>b TRUE\n OBVIOUS\n<1> QED ',
        visible_backends=['SMT', 'PTL'], visible_definitions=['D'])
    assert [s['label'] for s in meta['visible_steps']] == ['<1>a', '<1>b']
    assert candidates[:3] == ['BY <1>a, <1>b', 'BY SMT, <1>a, <1>b', 'BY PTL, <1>a, <1>b']
    assert 'BY <1>a, <1>b DEF D' in candidates
    assert meta['current_goal'] == 'TRUE'


def test_current_assertion_never_a_premise():
    candidates, meta = run('<1>1 TRUE BY D\n<1>2 FALSE\n')
    assert candidates == ['BY <1>1']
    assert meta['current_goal'] == 'FALSE'


def test_completed_parent_visible_closed_child_hidden():
    candidates, meta = run('<1>1 TRUE\n <2>a TRUE BY D\n <2> QED BY <2>a\n<1>2 TRUE\n')
    assert candidates == ['BY <1>1']
    assert [s['label'] for s in meta['visible_steps']] == ['<1>1']


def test_open_ancestors_not_treated_as_proved():
    candidates, meta = run('<1>1 FALSE\n <2>1 TRUE BY D\n <2>2 TRUE\n')
    assert candidates == ['BY <2>1']


def test_even_completed_outer_siblings_omitted_from_inner_scope():
    candidates, meta = run('<1>old TRUE BY D\n<1>active TRUE\n <2>1 TRUE BY D\n <2>2 TRUE\n')
    assert candidates == ['BY <2>1']


def test_assume_labels_conservatively_omitted():
    candidates, meta = run('<1>1 ASSUME TRUE PROVE TRUE\n BY D\n<1>2 ASSUME FALSE PROVE FALSE\n')
    assert candidates == []
    assert meta['omitted_assumption_labels'] == ['<1>1', '<1>2']
    assert meta['current_goal'] is None


@pytest.mark.parametrize('command', ['SUFFICES TRUE', 'PICK x : TRUE', 'HIDE <1>1', 'DEFINE A == TRUE'])
def test_unsupported_scope_commands_fail_closed(command):
    candidates, meta = run('<1>1 TRUE BY D\n<1> ' + command)
    assert candidates == [] and meta['status'] == 'unsupported'


def test_labels_in_comments_proofs_and_prior_theorem_not_indexed():
    prefix = ('---- MODULE Example ----\nTHEOREM Earlier == TRUE\n<1>old TRUE BY Fake\n'
              '<1> QED BY <1>old\nTHEOREM Target == TRUE\n'
              '(* <1>fake FALSE BY Trick *)\n<1>a TRUE BY SecretAnswer\n<1> QED ')
    first = step_candidates(prefix, 'Target')
    second = step_candidates(prefix.replace('SecretAnswer', 'DifferentAnswer'), 'Target')
    assert first == second
    assert first[0] == ['BY <1>a']
    assert 'SecretAnswer' not in str(first)


def test_invalid_context_and_bounds():
    with pytest.raises(ValueError):
        run('<1>a TRUE BY D\n<1> QED ', visible_definitions=['Missing'])
    with pytest.raises(ValueError):
        run('<1> QED ', visible_backends=['MadeUp'])
    with pytest.raises(ValueError):
        run('<1> QED ', limit=33)


def test_unproved_previous_step_not_promoted_and_complete_prefix_rejected():
    assert run('<1>a FALSE\n<1> QED ')[0] == []
    assert run('<1>a TRUE BY D')[1]['status'] == 'unsupported'


def test_scope_jumps_and_anonymous_marker_fail_closed():
    assert run('<1>a TRUE\n<3>b TRUE')[1]['status'] == 'unsupported'
    assert run('<*> TRUE')[1]['status'] == 'unsupported'
def test_qed_goal_excludes_proof_intro_preserving_literal():
    from tools.proof_step_candidates import step_candidates
    prefix = ('---- MODULE T ----\nTHEOREM Target == "PROOF" = "PROOF"\n'
              'PROOF\n<1>a. TRUE\nOBVIOUS\n<1> QED\n')
    choices, context = step_candidates(prefix, 'Target')
    assert choices == ['BY <1>a']
    assert context['current_goal'] == '"PROOF" = "PROOF"'


@pytest.mark.skipif(not (Path(__file__).resolve().parents[1]/'tools/tlapm/bin/tlapm').exists(),
                    reason='local TLAPS unavailable')
def test_real_tlaps_step_candidate_and_false_target(tmp_path):
    from harness.proof_fragment_check import certify_fragment
    from tools.proof_step_candidates import step_candidates
    prefix = ('---- MODULE StepControl ----\nEXTENDS TLAPS\nTHEOREM Target == TRUE\n'
              '<1>a. TRUE\nOBVIOUS\n<1> QED\n')
    choices, _ = step_candidates(prefix, 'Target')
    assert choices == ['BY <1>a']
    good = certify_fragment(prefix, choices[0], '\n====\n', theorem_name='Target',
                            work_root=tmp_path/'good', timeout=5)
    assert good['certified'], good
    false_prefix = prefix.replace('THEOREM Target == TRUE', 'THEOREM Target == FALSE')
    bad = certify_fragment(false_prefix, choices[0], '\n====\n', theorem_name='Target',
                           work_root=tmp_path/'false', timeout=5)
    assert not bad['certified'], bad
    assert 'Could not prove or check' in bad['output'], bad


@pytest.mark.skipif(not (Path(__file__).resolve().parents[1]/'tools/tlapm/bin/tlapm').exists(),
                    reason='local TLAPS unavailable')
def test_real_tlaps_closed_child_is_not_visible(tmp_path):
    from harness.proof_fragment_check import certify_fragment
    from tools.proof_step_candidates import step_candidates
    prefix = ('---- MODULE ClosedScopeControl ----\nEXTENDS TLAPS\nTHEOREM Target == TRUE\n'
              '<1>a. TRUE\n<2>b. TRUE\nOBVIOUS\n<2> QED\nBY <2>b\n<1> QED\n')
    choices, context = step_candidates(prefix, 'Target')
    assert choices == ['BY <1>a']
    assert [s['label'] for s in context['visible_steps']] == ['<1>a']
    good = certify_fragment(prefix, choices[0], '\n====\n', theorem_name='Target',
                            work_root=tmp_path/'good', timeout=5)
    assert good['certified'], good
    bad = certify_fragment(prefix, 'BY <2>b', '\n====\n', theorem_name='Target',
                           work_root=tmp_path/'closed', timeout=5)
    assert not bad['certified'], bad
