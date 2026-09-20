from pathlib import Path

import pytest

from harness import proof_fragment_check as p

PREFIX = '---- MODULE ProofControl ----\nTHEOREM Test == TRUE\n'
SUFFIX = '\n====\n'


def _skip_if_tlapm_sandbox_blocked(result):
    output = result.get('output', '') or ''
    if '/bin/ps: Operation not permitted' in output and 'End_of_file' in output:
        pytest.skip('TLAPS cannot execute ps in this sandboxed environment')


@pytest.mark.parametrize('fragment', ['OMITTED', 'PROOF OMITTED', 'OBVIOUS\nTHEOREM Cheat == TRUE\nOBVIOUS',
    'OBVIOUS\n====\n', 'OBVIOUS\nAXIOM FALSE', 'BY (*{ _@ prover: "trivial" }*)',
    'OBVIOUS\\* hide suffix', 'OBVIOUS (*', '*) OBVIOUS', 'BY\nFake == TRUE', ''])
def test_injection_rejected(fragment):
    with pytest.raises(ValueError):
        p.validate_fragment(PREFIX, fragment, SUFFIX, 'Test')


def test_leaf_hole_with_fixed_suffix():
    assert p.validate_fragment(PREFIX + 'PROOF\n<1>1. TRUE\n', 'OBVIOUS',
                               '\n<1> QED BY <1>1\n====\n', 'Test') == 'ProofControl'


def test_statement_hole_rejected():
    with pytest.raises(ValueError):
        p.validate_fragment(PREFIX.rstrip() + ' /\\ ', 'TRUE', '\nOBVIOUS\n====\n', 'Test')


def test_commented_proof_does_not_establish_hole():
    with pytest.raises(ValueError):
        p.validate_fragment(PREFIX + '(* PROOF\nOBVIOUS *)\n', 'TRUE', SUFFIX, 'Test')


@pytest.mark.parametrize('rc,out,timeout,status', [
    (0, '[INFO]: All 1 obligation proved.\n', False, 'pass'),
    (1, '[INFO]: All 1 obligation proved.\n', False, 'verifier_reject'),
    (0, '[INFO]: All 1 obligation proved.\n', True, 'timeout'),
    (0, 'All 0 obligations proved', False, 'no_obligations'),
    (0, 'All 2 obligations proved\n1 obligation omitted', False, 'error'),
    (0, 'All 2 obligations proved\nERROR backend died', False, 'error'),
    (0, 'All 2 obligations proved\nAll 1 obligation proved', False, 'unrecognized_output'),
    (0, 'source says All 1 obligation proved', False, 'unrecognized_output'),
    (0, '1/2 obligations proved', False, 'unrecognized_output'),
])
def test_classification(rc, out, timeout, status):
    assert p.classify_result(rc, out, timeout)[0] == status


def test_fresh_dirs_and_no_fingerprints(tmp_path, monkeypatch):
    calls = []
    def run(cmd, cwd, timeout):
        calls.append(cwd)
        assert '--strict' in cmd and '--nofp' in cmd and '--cache-dir' in cmd
        assert not (cwd / '.tlacache').exists()
        assert (cwd / 'ProofControl.tla').read_text() == PREFIX + 'OBVIOUS' + SUFFIX
        return 0, '[INFO]: All 1 obligation proved.\n', .1, False
    monkeypatch.setattr(p.runner, 'run_cmd', run)
    for _ in range(2):
        assert p.certify_fragment(PREFIX, 'OBVIOUS', SUFFIX, theorem_name='Test', work_root=tmp_path)['certified']
    assert calls[0] != calls[1]


def test_legacy_tlapm_uses_single_worker_without_newer_flags(tmp_path, monkeypatch):
    seen = []
    def run(cmd, cwd, timeout):
        seen.append(cmd)
        return 0, '[INFO]: All 1 obligation proved.\n', .1, False
    monkeypatch.setattr(p.runner, 'run_cmd', run)
    monkeypatch.setenv('PROVE_TLA_TLAPM_LEGACY', '1')
    result = p.certify_fragment(PREFIX, 'OBVIOUS', SUFFIX, theorem_name='Test', work_root=tmp_path)
    assert result['certified']
    cmd = seen[0]
    assert '--strict' not in cmd and '--cache-dir' not in cmd
    assert cmd[cmd.index('--threads') + 1] == '1'


def test_dependency_cannot_overwrite_candidate(tmp_path):
    dep = tmp_path / 'ProofControl.tla'
    dep.write_text('malicious dependency')
    result = p.certify_fragment(PREFIX, 'OBVIOUS', SUFFIX, theorem_name='Test', work_root=tmp_path,
                                dependencies=(dep,))
    assert not result['certified']
    assert result['status'] == 'contract_reject'


def test_missing_executable_is_unmeasured(tmp_path):
    result = p.certify_fragment(PREFIX, 'OBVIOUS', SUFFIX, theorem_name='Test', work_root=tmp_path,
                                tlapm=tmp_path / 'absent')
    assert result['status'] == 'infrastructure_error'


def test_unproved_custom_import_cannot_supply_target(tmp_path):
    dep = tmp_path/'Unproved.tla'
    dep.write_text('---- MODULE Unproved ----\nTHEOREM Circular == FALSE\n====\n')
    result = p.certify_fragment(PREFIX, 'OBVIOUS', SUFFIX, theorem_name='Test',
                               work_root=tmp_path, dependencies=(dep,))
    assert result['status'] == 'contract_reject'
    assert not result['certified']
    assert 'independent certification' in result['reason']


@pytest.mark.skipif(not p.runner.TLAPM.exists(), reason='local TLAPS unavailable')
def test_actual_good_bad_controls(tmp_path):
    good = p.certify_fragment(PREFIX, 'OBVIOUS', SUFFIX, theorem_name='Test', work_root=tmp_path)
    _skip_if_tlapm_sandbox_blocked(good)
    assert good['certified'], good['output']
    bad = p.certify_fragment(PREFIX.replace('== TRUE', '== FALSE'), 'OBVIOUS', SUFFIX,
                             theorem_name='Test', work_root=tmp_path, timeout=10)
    _skip_if_tlapm_sandbox_blocked(bad)
    assert not bad['certified']


@pytest.mark.skipif(not p.runner.TLAPM.exists(), reason='local TLAPS unavailable')
def test_actual_numeric_leading_module(tmp_path):
    prefix = PREFIX.replace('ProofControl', '2_ProofControl')
    result = p.certify_fragment(prefix, 'OBVIOUS', SUFFIX, theorem_name='Test', work_root=tmp_path)
    _skip_if_tlapm_sandbox_blocked(result)
    assert result['certified'], result
    assert Path(result['candidate_path']).name == '2_ProofControl.tla'


@pytest.mark.parametrize('name', ['123', '../Escape', 'a/b', 'a.b'])
def test_module_name_cannot_be_number_or_path(name):
    with pytest.raises(ValueError, match='missing module header'):
        p.validate_fragment(PREFIX.replace('ProofControl', name), 'OBVIOUS', SUFFIX, 'Test')


def test_frozen_trailing_history_comments_are_preserved():
    suffix = SUFFIX + '\\* Modification History: THEOREM ignored == FALSE\n'
    assert p.validate_fragment(PREFIX, 'OBVIOUS', suffix, 'Test') == 'ProofControl'


@pytest.mark.skipif(not p.runner.TLAPM.exists(), reason='local TLAPS unavailable')
def test_prior_proved_helper_cannot_mask_false_target(tmp_path):
    prefix = PREFIX.replace('THEOREM Test == TRUE',
        'THEOREM Helper == TRUE\nOBVIOUS\nTHEOREM Test == FALSE')
    result = p.certify_fragment(prefix, 'OBVIOUS', SUFFIX, theorem_name='Test',
                               work_root=tmp_path, timeout=10)
    _skip_if_tlapm_sandbox_blocked(result)
    assert not result['certified'], result


@pytest.mark.skipif(not p.runner.TLAPM.exists(), reason='local TLAPS unavailable')
def test_unproved_local_helper_cannot_mask_false_target(tmp_path):
    prefix = PREFIX.replace('THEOREM Test == TRUE',
        'THEOREM Helper == FALSE\nTHEOREM Test == FALSE')
    result = p.certify_fragment(prefix, 'BY Helper', SUFFIX, theorem_name='Test',
                               work_root=tmp_path, timeout=10)
    _skip_if_tlapm_sandbox_blocked(result)
    assert not result['certified'], result
    assert result['returncode'] != 0, result
    assert 'missing' in result['output'].lower(), result
