import hashlib
import json
import pytest
from tools.proof_official_extension import build_task, summarize, prepare, evaluate, source_aware_candidates
from tools.proof_fact_search import proposals


def fixture(tmp_path, raw):
    (tmp_path/'source.tla').write_bytes(raw)
    return dict(id='source', module_file='source.tla', category='math',
                theorem_name='Target', sha256=hashlib.sha256(raw).hexdigest())


@pytest.mark.parametrize('newline', ['\n','\r\n'])
def test_exact_reconstruction_numeric_module_and_trailing_comments(tmp_path, newline):
    raw = newline.join(['---- MODULE 2_Test ----', 'EXTENDS TLAPS',
                        'THEOREM Target == TRUE', '====', '\\* history', '']).encode()
    task = build_task(fixture(tmp_path, raw), tmp_path)
    assert (task['prefix']+task['suffix']).encode() == raw
    assert task['target_goal'] == 'TRUE'
    assert task['split'] == 'official_test'
    assert 'reference_fragment' not in task


def test_rejects_changed_source(tmp_path):
    entry = fixture(tmp_path, b'---- MODULE Test ----\nTHEOREM Target == TRUE\n====\n')
    entry['sha256'] = 'bad'
    with pytest.raises(ValueError, match='hash mismatch'):
        build_task(entry, tmp_path)


def test_no_target_proof_answers_accepted_or_retrieved(tmp_path):
    raw = b'---- MODULE Test ----\nTHEOREM Target == TRUE\nBY SecretAnswer\n====\n'
    with pytest.raises(ValueError, match='bare final theorem'):
        build_task(fixture(tmp_path, raw), tmp_path)
    raw = raw.replace(b'BY SecretAnswer\n', b'')
    task = build_task(fixture(tmp_path, raw), tmp_path)
    got, context = proposals(task['prefix'], 'Target', task['target_goal'], [], [])
    assert context['visible_facts'] == []
    assert not any('Target' in proposal for proposal in got)


def test_denominator_retains_unattempted_and_failed():
    tasks = [dict(id=str(i), category='math') for i in range(119)]
    result = summarize(tasks, [dict(task='0', certified=True), dict(task='1', certified=False)], {})
    assert (result['requested_tasks'], result['attempted_tasks'], result['certified_tasks'],
            result['unattempted_tasks']) == (119, 2, 1, 117)


def test_prepare_rejects_reduced_population(tmp_path):
    manifest = tmp_path/'input.json'
    manifest.write_text(json.dumps([]))
    with pytest.raises(ValueError, match='119'):
        prepare(manifest, tmp_path, tmp_path/'output')


def test_backend_candidates_without_import_do_not_invent_operator():
    choices = ['BY SMT', 'BY SMT DEF Inv', 'BY DEF Inv', 'BY SMT, Fact', 'BY Fact']
    corrected, visible = source_aware_candidates(choices, ['EXTENDS TLC\n(* EXTENDS TLAPS *)'])
    assert not visible
    assert corrected == ['OBVIOUS', 'BY DEF Inv', 'BY Fact']
    assert choices[0] == 'BY SMT'


@pytest.mark.parametrize('source', ['EXTENDS TLC, TLAPS\n', 'SMT == TRUE\n'])
def test_visible_backend_candidates_unchanged(source):
    choices = ['BY SMT', 'BY SMT DEF Inv', 'BY DEF Inv']
    corrected, visible = source_aware_candidates(choices, [source])
    assert visible and corrected == choices


def test_actual_default_backend_without_tlaps_import(tmp_path):
    from harness.proof_fragment_check import certify_fragment
    from harness.runner import TLAPM
    if not TLAPM.exists():
        pytest.skip('local TLAPS unavailable')
    prefix = '---- MODULE 2_NoImport ----\nTHEOREM Target == TRUE\n'
    choices, visible = source_aware_candidates(['BY SMT'], [prefix])
    assert not visible
    for goal, expected in [('TRUE', True), ('FALSE', False)]:
        result = certify_fragment(prefix.replace('== TRUE', '== '+goal), choices[0], '\n====\n',
                                  theorem_name='Target', work_root=tmp_path/goal, timeout=5)
        assert result['certified'] is expected, result


def test_evaluation_round_robin_and_no_task_dropped(tmp_path):
    entry = fixture(tmp_path, b'---- MODULE Test ----\nTHEOREM Target == TRUE\n====\n')
    original = tmp_path/'official.json'
    original.write_text(json.dumps([{**entry, 'id':str(i)} for i in range(119)]))
    prepared = tmp_path/'prepared'
    manifest = prepare(original, tmp_path, prepared)
    for task in manifest['tasks']:
        task['symbolic_candidates'] = ['BY SMT', 'OBVIOUS']
    frozen = prepared/'two-candidates.json'
    frozen.write_text(json.dumps(manifest))
    calls = []
    def fake(prefix, fragment, suffix, **kwargs):
        calls.append(kwargs['work_root'].parts[-2:])
        return dict(certified=False, status='verifier_reject')
    summary = evaluate(frozen, tmp_path/'run', attempts=2, seconds=900, checker=fake)
    assert calls[:119] == [(str(i), '0') for i in range(119)]
    assert calls[119:] == [(str(i), '1') for i in range(119)]
    assert summary['requested_tasks'] == summary['attempted_tasks'] == 119
    assert summary['certified_tasks'] == 0
    assert len(summary['task_statuses']) == 119
    manifest['tasks'][0]['theorem_name'] = 'Helper'
    forged = prepared/'wrong-target.json'
    forged.write_text(json.dumps(manifest))
    with pytest.raises(ValueError, match='identity mismatch'):
        evaluate(forged, tmp_path/'wrong-target-run', checker=fake)
    assert not (tmp_path/'wrong-target-run').exists()
def test_backend_detection_ignores_nested_and_trailing_declarations():
    from tools.proof_official_extension import source_aware_candidates
    source = ('---- MODULE Outer ----\n---- MODULE Inner ----\n'
              'EXTENDS TLAPS\nSMT == TRUE\n====\n====\nEXTENDS TLAPS\nSMT == TRUE\n')
    assert source_aware_candidates(['BY SMT'], [source]) == (['OBVIOUS'], False)
