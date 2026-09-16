import copy
import json
from pathlib import Path

import pytest
from tools import proof_fullmodule_sany_checks as m


GOOD = '---- MODULE Example ----\nX == 1\n===================='


@pytest.fixture
def case(tmp_path):
    source = tmp_path / 'source.tla'; source.write_text(GOOD)
    task = dict(id='2', module_name='Example', dependencies={},
                source=dict(path=str(source), sha256=m.file_sha(source)))
    current = dict(java='/fake/java', library='/fake/library', classpath='/fake/jar')
    return task, current, tmp_path / 'check'


def execute(output, rc=0, **extra):
    def run(command, cwd, timeout):
        return dict(command=command, cwd=str(cwd), returncode=rc, output=output,
                    seconds=.01, timed_out=False, execution_complete=True,
                    cleanup_complete=True, output_complete=True, **extra)
    return run


def test_pass_bound_to_raw_input_process_and_candidate(case):
    task, current, work = case
    result = m.check(task, GOOD, work, current, execute=execute('Semantic processing of module Example\n'))
    assert result['sany'] == 1
    m.audit(task, GOOD, result, work, current)
    (work / 'Example.tla').write_text(GOOD.replace('1', '2'))
    with pytest.raises(ValueError, match='Immutable'):
        m.audit(task, GOOD, result, work, current)


@pytest.mark.parametrize('reply,status', [('not a module', 'model_extraction'),
                                         (GOOD.replace('Example', 'Wrong'), 'model_module_name')])
def test_model_contract_rejections_have_no_process(case, reply, status):
    task, current, work = case
    result = m.check(task, reply, work, current)
    assert result['status'] == status and result['sany'] == 0 and result['process'] is None
    m.audit(task, reply, result, work, current)


@pytest.mark.parametrize('diagnostic,rc,status,reward', [
    ('***Parse Error***\nEncountered ")"\n', 1, 'model_sany_reject', 0),
    ('Cannot find source file Missing.tla\n', 1, 'unmeasured_infrastructure', None),
    ('', 0, 'unmeasured_unknown', None),
])
def test_raw_diagnostics_distinguish_unknowns(case, diagnostic, rc, status, reward):
    task, current, work = case
    result = m.check(task, GOOD, work, current, execute=execute(diagnostic, rc))
    assert result['status'] == status and result['sany'] == reward
    m.audit(task, GOOD, result, work, current)


def test_incomplete_owned_process_never_passes(case):
    task, current, work = case
    def incomplete(command, cwd, timeout):
        value = execute('Semantic processing of module Example\n')(command, cwd, timeout)
        value['cleanup_complete'] = False
        return value
    result = m.check(task, GOOD, work, current, execute=incomplete)
    assert result['sany'] is None and result['status'] == 'unmeasured_process'
    m.audit(task, GOOD, result, work, current)


def test_dependencies_use_declared_module_name_not_numeric_source_filename(case):
    task, current, work = case
    dep = work.parent / '17.tla'; dep.write_text('---- MODULE Dependency ----\nY == 2\n====')
    task['dependencies'] = {str(dep): m.file_sha(dep)}
    result = m.check(task, GOOD, work, current, execute=execute('Semantic processing of module Example\n'))
    assert (work / 'Dependency.tla').read_bytes() == dep.read_bytes()
    m.audit(task, GOOD, result, work, current)


def test_duplicate_dependency_headers_fail_closed(case):
    task, current, work = case
    for filename in ('1.tla', '2.tla'):
        dep = work.parent / filename; dep.write_text('---- MODULE Duplicate ----\n====')
        task['dependencies'][str(dep)] = m.file_sha(dep)
    result = m.check(task, GOOD, work, current)
    assert result['sany'] is None and 'collision' in result['error']


def test_negative_inserted_before_whole_final_terminator():
    text = m.negative(GOOD)
    assert text.endswith(m.NEGATIVE_NAME + ' == )\n====================')
    assert m.gen_eval.extract_module(text) == text
    with pytest.raises(ValueError, match='collision'):
        m.negative(text)


def test_changed_diagnostic_cannot_be_audited(case):
    task, current, work = case
    result = m.check(task, GOOD, work, current, execute=execute('Semantic processing of module Example\n'))
    (work / 'sany.log').write_text('different')
    with pytest.raises(ValueError, match='diagnostic'):
        m.audit(task, GOOD, result, work, current)


def test_controls_never_reduce_denominator(tmp_path):
    with pytest.raises(ValueError, match='All30'):
        m.controls([], tmp_path / 'controls')
