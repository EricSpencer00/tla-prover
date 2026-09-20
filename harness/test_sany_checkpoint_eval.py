import hashlib
import tools.sany_checkpoint_eval as evaluator
from tools.sany_checkpoint_eval import tasks_from_parent, summarize


def test_parent_tasks_restore_reference(tmp_path, monkeypatch):
    monkeypatch.setattr(evaluator, 'REPO', tmp_path)
    (tmp_path/'data').mkdir()
    sources = ['---- MODULE AdaptiveK ----\nIF cat = "bugfix" THEN 1 ELSE IF cat = "integration" THEN 2 ELSE 3\n====',
               "---- MODULE Counter ----\nnumber' = number + 1\nnumber' = number - 1\n===="]
    config = {'audits': []}
    for i, source in enumerate(sources):
        (tmp_path/'data'/f'{i}.tla').write_text(source)
        config['audits'].append(dict(source=f'/old/data/{i}.tla',
                                    source_sha256=hashlib.sha256(source.encode()).hexdigest()))
    tasks = tasks_from_parent(config)
    assert len(tasks) == 7
    assert len({t['mod'] for t in tasks}) == 2
    for task in tasks:
        assert task['prefix']+task['target']+task['suffix'] == task['reference']


def test_failures_and_timeouts_stay_in_denominator():
    rows = [dict(task='a', sany=s, candidate_sha256=str(i))
            for i,s in enumerate(['pass', 'fail', 'timeout', 'fail_missing_module'])]
    result = summarize(rows, 1000, 20, finished=True)
    assert result['attempts'] == 4
    assert result['pass_fraction_all_attempts'] == .25
    assert result['stop_reason'] == 'time_budget'
    assert result['unique_candidates'] == 4


def test_target_is_attempts_not_passes():
    result = summarize([dict(task='a', sany='fail', candidate_sha256='x')], 1, 2, True)
    assert result['stop_reason'] == 'target_reached'
    assert result['pass_fraction_all_attempts'] == 0
