import pytest
from tools.proof_repair_pilot import prompt_for, selected_tasks, with_dependency_context


def test_prompt_does_not_leak_reference():
    task = dict(prefix='fixed theorem\n', suffix='\n====', reference_fragment='SECRET_REFERENCE')
    prompt = prompt_for(task)
    assert 'SECRET_REFERENCE' not in prompt
    assert 'fixed theorem\n<PROOF_HOLE>\n====' in prompt


def test_feedback_bounded_and_scaffold_unchanged():
    task = dict(prefix='prefix', suffix='suffix')
    prompt = prompt_for(task, 'x'*5000+'FAILURE')
    assert 'prefix<PROOF_HOLE>suffix' in prompt
    assert prompt.endswith('FAILURE')
    assert 'x'*3001 not in prompt


def test_explicit_split_selection():
    tasks = [dict(id='a', split='train'), dict(id='b', split='development')]
    assert selected_tasks(dict(tasks=tasks), 'development') == [tasks[1]]
    assert selected_tasks(dict(tasks=tasks), 'all') == tasks


def test_no_silent_empty_or_duplicate_evaluation():
    with pytest.raises(ValueError):
        selected_tasks(dict(tasks=[dict(id='a', split='train')]), 'development')
    with pytest.raises(ValueError):
        selected_tasks(dict(tasks=[dict(id='a'), dict(id='a')]), 'all')


def test_dependency_context_contains_source_not_reference_answer():
    task = dict(prefix='target', suffix='end', reference_fragment='SECRET',
                dependency_context=[dict(module='Imported', text='State == TRUE')])
    prompt = prompt_for(task)
    assert 'State == TRUE' in prompt and 'BEGIN DEPENDENCY Imported' in prompt
    assert 'SECRET' not in prompt


def test_dependency_context_checks_hash_and_does_not_mutate(tmp_path):
    from hashlib import sha256
    path = tmp_path/'Imported.tla'
    path.write_text('State == TRUE')
    task = dict(dependencies=[str(path)], dependency_sha256={str(path): sha256(path.read_bytes()).hexdigest()})
    copied = with_dependency_context(task)
    assert 'dependency_context' not in task
    assert copied['dependency_context'][0]['text'] == 'State == TRUE'
    path.write_text('State == FALSE')
    with pytest.raises(ValueError):
        with_dependency_context(task)
