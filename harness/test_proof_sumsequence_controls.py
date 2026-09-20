import json

import pytest

from tools import proof_sumsequence_controls as module


FALSE_LOG = '[ERROR]: Could not prove or check:\n             FALSE\n[ERROR]: 1/1 obligation failed.\n'
BOUND_FALSE_LOG = '''Zenon error: exhausted search space without finding a proof
(* created new "/Users/eric/GitHub/prove-TLA/results/runs/proof-sumsequence-controls-20260906-v1/checks/FrontDef/false_conclusion/proof-full-x9oukx9p/.tlacache/SumSequence.tlaps/SumSequence.thy" *)
(* fingerprints written in "/Users/eric/GitHub/prove-TLA/results/runs/proof-sumsequence-controls-20260906-v1/checks/FrontDef/false_conclusion/proof-full-x9oukx9p/.tlacache/SumSequence.tlaps/fingerprints" *)
File "./SumSequence.tla", line 7, characters 1-2:
[ERROR]: Could not prove or check:
           ASSUME Front(s) == SubSeq(s, 1, Len(s) - 1)
           PROVE  FALSE
File "./SumSequence.tla", line 1, character 1 to line 9, character 4:
[ERROR]: 1/1 obligation failed.
There were backend errors processing module `"SumSequence"`.
'''


def test_discovery_preserves_targets_and_removes_unchecked_context():
    result = module.discover()
    assert [t['id'] for t in result['tasks']] == ['FrontDef','Lemma2','Lemma3','Lemma4']
    assert not result['training_authorized']
    first, second = result['tasks'][:2]
    assert 'THEOREM FrontDef' in second['prefix'] and 'BY DEF Front' in second['prefix']
    for task in (first, second):
        assert 'Lemma1' not in task['prefix'] and 'Lemma5' not in task['prefix']
        assert 'SequenceTheorems' not in task['prefix'] and 'ValAssump' not in task['prefix']
        assert task['negative_prefix'].endswith('== FALSE\n')
        assert task['statement'] in task['prefix']
    assert all(not t['control_eligible'] for t in result['tasks'][2:])


@pytest.mark.parametrize('extra', ['parse error', 'undefined operator', 'exception', 'cannot find backend'])
def test_negative_requires_intended_failure(extra):
    result = dict(status='verifier_reject', timed_out=False, certified=False, returncode=10, output=FALSE_LOG)
    assert module.intended_false_failure(result)
    assert not module.intended_false_failure(dict(result, output=FALSE_LOG+extra))


def test_observed_bound_false_sequent():
    result = dict(status='verifier_reject', timed_out=False, certified=False,
                  returncode=10, output=BOUND_FALSE_LOG)
    assert module.intended_false_failure(result)
    assert not module.intended_false_failure(dict(result, returncode=1))
    assert not module.intended_false_failure(dict(result, timed_out=True))


@pytest.mark.parametrize('text', [
    BOUND_FALSE_LOG.replace('PROVE  FALSE', 'PROVE  TRUE'),
    BOUND_FALSE_LOG.replace('PROVE  FALSE', 'PROVE  FALSE /\\ P'),
    BOUND_FALSE_LOG.replace('1/1 obligation', '2/2 obligations'),
    BOUND_FALSE_LOG + '[ERROR]: 1/1 obligation failed.\n',
    BOUND_FALSE_LOG + FALSE_LOG,
    BOUND_FALSE_LOG + 'Could not load backend\n',
    BOUND_FALSE_LOG + 'out of memory\n',
    BOUND_FALSE_LOG + 'syntax error\n',
])
def test_bound_false_rejects_other_failures(text):
    assert not module.intended_false_failure(dict(status='verifier_reject',
        timed_out=False, certified=False, returncode=10, output=text))


@pytest.fixture
def run(tmp_path, monkeypatch):
    monkeypatch.setattr(module, 'file_identity', lambda: {'stable': True})
    calls = []
    def execute(cmd, cwd, timeout):
        calls.append((cmd, cwd, timeout))
        negative = 'false_conclusion' in cwd.parts
        return dict(command=list(cmd), cwd=str(cwd), returncode=10 if negative else 0,
            output=FALSE_LOG if negative else 'All 1 obligations proved.\n', seconds=.1,
            timed_out=False, execution_complete=True, cleanup_complete=True, output_complete=True)
    return tmp_path/'controls', calls, execute


def test_pairs_and_scoped_restore(run):
    output, calls, execute = run
    original = module.runner.run_cmd
    module.controls(output, execute=execute, identify=lambda: {'runtime':'fixed'})
    assert module.runner.run_cmd is original
    assert len(calls)==4 and all(c[2]==30 for c in calls)
    result=json.loads((output/'summary.json').read_text())
    assert result['controls_admitted'] and result['completed_pair_ids']==['FrontDef','Lemma2']
    assert not result['training_authorized'] and result['discovered']==4
    assert len(list(output.rglob('process.json')))==4


@pytest.mark.parametrize('field', ['execution_complete','cleanup_complete','output_complete'])
def test_incomplete_blocks_downstream(run, field):
    output, calls, execute=run
    def incomplete(*args):
        result=execute(*args); result[field]=False; return result
    module.controls(output, execute=incomplete, identify=lambda: {})
    summary=json.loads((output/'summary.json').read_text())
    assert len(calls)==2 and not summary['controls_admitted']
    assert not summary['completed_pair_ids']


def test_surviving_false_blocks_lemma2(run):
    output, calls, execute=run
    def survived(*args):
        result=execute(*args)
        result.update(returncode=0, output='All 1 obligations proved.\n')
        return result
    module.controls(output, execute=survived, identify=lambda: {})
    assert len(calls)==2
    assert not json.loads((output/'summary.json').read_text())['controls_admitted']


def test_runtime_drift_fails_and_restores(run):
    output, _, execute=run
    identity=iter([{'v':1},{'v':2}])
    original=module.runner.run_cmd
    with pytest.raises(ValueError, match='identity drift'):
        module.controls(output, execute=execute, identify=lambda: next(identity))
    assert module.runner.run_cmd is original
    assert not json.loads((output/'failure.json').read_text())['controls_admitted']


def test_no_checks_when_initial_identity_uses_budget(run):
    output, calls, execute=run
    times=iter([0,120,120,120,120])
    module.controls(output, execute=execute, identify=lambda: {}, clock=lambda: next(times))
    assert not calls
    assert not json.loads((output/'summary.json').read_text())['controls_admitted']
