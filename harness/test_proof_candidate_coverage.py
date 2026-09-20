from tools.proof_candidate_coverage import augment, evaluate


def test_step_candidates_reserved_before_truncation():
    task = dict(prefix='---- MODULE Test ----\nTHEOREM Target == TRUE\n'
                       '<1>a. TRUE\nOBVIOUS\n<1> QED\n',
                theorem_name='Target', candidates=['base'+str(i) for i in range(8)],
                context=dict(library_sha256={}))
    choices, context = augment(task)
    assert choices[:3] == ['base0', 'base1', 'BY <1>a']
    assert len(choices) == 8
    assert not context['reference_fragment_used']


def test_unsupported_steps_preserve_base_population():
    task = dict(prefix='THEOREM Target == TRUE\n', theorem_name='Target',
                candidates=['BY SMT'], context=dict(library_sha256={}))
    choices, context = augment(task)
    assert choices == task['candidates']
    assert context['status'] == 'unsupported'


def test_round_robin_full_denominator_and_stop_on_pass(tmp_path):
    tasks = [dict(id=str(i), prefix='p',suffix='s',theorem_name='Target',
                  candidates=['a','b']) for i in range(50)]
    calls = []
    def check(prefix, fragment, suffix, **kw):
        calls.append((kw['work_root'].parent.name,fragment))
        return dict(certified=fragment=='b')
    result = evaluate(tasks, tmp_path, checker=check)
    assert calls[:50] == [(str(i),'a') for i in range(50)]
    assert result['requested_train_tasks'] == result['certified_train_tasks'] == 50
    assert result['checker_attempts'] == 100
    assert result['parameter_updates'] == 0
