"""Pure contract tests; run `-k actual` separately in the owned TLAPS lane."""
import hashlib
from pathlib import Path

import pytest

from harness import proof_full_fragment_check as p

PREFIX = '---- MODULE FullControl ----\nEXTENDS TLAPS\nTHEOREM Test == TRUE\n'
SUFFIX = '\n====\n'
GOOD = ('(* ordinary (* nested *) explanatory comment *)\nPROOF\n'
        '<1> DEFINE Fresh == TRUE\n'
        '<1>1. Fresh BY DEF Fresh\n<1> QED BY <1>1\n')


@pytest.mark.parametrize('fragment', [GOOD, '(* intro *) OBVIOUS',
    'PROOF\n<1> DEFINE R(i) == i = i\n<1> QED OBVIOUS\n',
    'OBVIOUS \\* comment ends at newline\n'])
def test_supported_proofs(fragment):
    assert p.validate_fragment(PREFIX, fragment, SUFFIX, 'Test') == 'FullControl'


@pytest.mark.parametrize('fragment', [
    'OBVIOUS (*', '*) OBVIOUS', 'OBVIOUS\nAXIOM FALSE',
    'OBVIOUS\nTHEOREM Other == TRUE\nOBVIOUS', 'OBVIOUS\n====',
    'PROOF OMITTED', 'BY (*{ _@ prover: "trivial" }*)',
    'OBVIOUS\nFresh == TRUE', 'PROOF\nDEFINE Fresh == TRUE\nOBVIOUS',
    'PROOF\n<1> DEFINE Fresh == TRUE\nOther == FALSE\n<1> QED OBVIOUS',
    'PROOF\n<1> DEFINE Fresh(i, i) == TRUE\n<1> QED OBVIOUS',
    'PROOF\n<1> DEFINE Test == TRUE\n<1> QED BY Test',
    'PROOF\n<1> DEFINE TRUE == FALSE\n<1> QED OBVIOUS',
    'PROOF\n<1> DEFINE Fresh == LET X == TRUE IN X\n<1> QED OBVIOUS',
    'PROOF\n<1> DEFINE Fresh == TRUE\n<1> DEFINE Fresh == FALSE\n<1> QED OBVIOUS',
    'PROOF\n<1> QED OBVIOUS\n<1> DEFINE Fresh == TRUE',
    'PROOF\n<3> DEFINE Fresh == TRUE\n<3> QED OBVIOUS',
    'PROOF\n<1> DEFINE Fresh == TRUE\nOBVIOUS',
    'PROOF\n<1> DEFINE Fresh ==\n<1> QED OBVIOUS',
    'OBVIOUS\nEXTENDS Unsafe', 'OBVIOUS\nINSTANCE Unsafe',
    'OBVIOUS\n<1> DEFINE Fresh == TRUE\n<1> QED OBVIOUS',
    'PROOF\n<1> DEFINE SMT == TRUE\n<1> QED BY SMT',
])
def test_unsafe_or_unsupported_proofs_rejected(fragment):
    with pytest.raises(ValueError):
        p.validate_fragment(PREFIX, fragment, SUFFIX, 'Test')


@pytest.mark.parametrize('prefix,suffix', [
    (PREFIX + '(*', SUFFIX), (PREFIX, '*)\n====\n'),
    (PREFIX, '\n<1> QED OBVIOUS\n====\n'),
    (PREFIX.rstrip(), SUFFIX), (PREFIX, '====\n'),
    (PREFIX + 'OBVIOUS\n', SUFFIX),
])
def test_cross_boundary_and_partial_proofs_rejected(prefix, suffix):
    with pytest.raises(ValueError):
        p.validate_fragment(prefix, GOOD, suffix, 'Test')


@pytest.mark.parametrize('declaration', ['Fresh == FALSE', 'CONSTANT Fresh', 'VARIABLE Fresh'])
def test_local_name_cannot_shadow_global(declaration):
    prefix = PREFIX.replace('THEOREM Test', declaration + '\nTHEOREM Test')
    with pytest.raises(ValueError, match='shadows'):
        p.validate_fragment(prefix, GOOD, SUFFIX, 'Test')


def test_local_name_cannot_shadow_target_binder():
    prefix = PREFIX.replace('== TRUE', '== \\A Fresh : Fresh = Fresh')
    with pytest.raises(ValueError, match='shadows'):
        p.validate_fragment(prefix, GOOD, SUFFIX, 'Test')


def test_exact_bytes_strict_fresh_directory_and_version(tmp_path, monkeypatch):
    calls = []
    def run(cmd, cwd, timeout):
        calls.append(cwd)
        assert '--strict' in cmd and '--nofp' in cmd and '--cache-dir' in cmd
        assert not (cwd / '.tlacache').exists()
        assert (cwd / 'FullControl.tla').read_bytes() == (PREFIX + GOOD + SUFFIX).encode()
        return 0, 'All 3 obligations proved\n', .1, False
    monkeypatch.setattr(p.runner, 'run_cmd', run)
    for _ in range(2):
        result = p.certify_fragment(PREFIX, GOOD, SUFFIX, theorem_name='Test', work_root=tmp_path)
        assert result['certified'] and result['total'] == 3
        assert result['contract_version'] == p.CONTRACT_VERSION
        assert result['sha256'] == hashlib.sha256((PREFIX + GOOD + SUFFIX).encode()).hexdigest()
    assert calls[0] != calls[1]


@pytest.mark.parametrize('declaration', ['THEOREM Cheat == FALSE', 'AXIOM FALSE'])
def test_no_custom_imported_trust(tmp_path, declaration):
    dep = tmp_path / 'Unsafe.tla'
    dep.write_text('---- MODULE Unsafe ----\n' + declaration + '\n====\n')
    result = p.certify_fragment(PREFIX, GOOD, SUFFIX, theorem_name='Test',
        work_root=tmp_path, dependencies=(dep,))
    assert result['status'] == 'contract_reject' and not result['certified']


def test_nonzero_exit_cannot_be_masked_by_proved_count(tmp_path, monkeypatch):
    monkeypatch.setattr(p.runner, 'run_cmd', lambda *a: (11, 'All 3 obligations proved\n', .1, False))
    result = p.certify_fragment(PREFIX, GOOD, SUFFIX, theorem_name='Test', work_root=tmp_path)
    assert not result['certified'] and result['status'] == 'verifier_reject'


@pytest.mark.skipif(not p.runner.TLAPM.exists(), reason='local TLAPS unavailable')
def test_actual_good_define_and_wrong_goal(tmp_path):
    good = p.certify_fragment(PREFIX, GOOD, SUFFIX, theorem_name='Test', work_root=tmp_path, timeout=30)
    assert good['certified'], good
    assert good['total'] > 0 and good['returncode'] == 0
    bad = p.certify_fragment(PREFIX.replace('== TRUE', '== FALSE'), GOOD, SUFFIX,
        theorem_name='Test', work_root=tmp_path, timeout=30)
    assert not bad['certified'], bad
    assert bad['status'] == 'verifier_reject', bad


@pytest.mark.skipif(not p.runner.TLAPM.exists(), reason='local TLAPS unavailable')
def test_actual_shadow_and_global_redefinition_controls(tmp_path):
    for candidate in [GOOD.replace('Fresh', 'Test'), GOOD + 'Global == TRUE\n']:
        result = p.certify_fragment(PREFIX, candidate, SUFFIX, theorem_name='Test', work_root=tmp_path)
        assert result['status'] == 'contract_reject' and not result['certified']
        assert 'command' not in result
