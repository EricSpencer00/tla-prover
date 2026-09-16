import json
import pytest
from tools import proof_sumsequence_lemma3 as module
from harness.test_proof_sumsequence_lemma2a import execute


def test_original_statement_proof_and_proven_prerequisites():
    task=module.task()
    original=module.base.discover()['tasks'][2]
    assert task['statement']==original['statement']
    assert task['reference_fragment']==original['reference_fragment']
    assert module.prior.task()['statement']+'OBVIOUS\n' in task['prefix']
    assert 'BY DEF Front' in task['prefix']
    assert 'Lemma1' not in task['prefix'] and 'SequenceTheorems' not in task['prefix']
    assert task['negative_prefix'].endswith('LEMMA Lemma3 == FALSE\n')


def test_pair_and_restore(tmp_path):
    old=module.runner.run_cmd
    module.controls(tmp_path/'run',execute=execute,identify=lambda:{})
    summary=json.loads((tmp_path/'run/summary.json').read_text())
    assert summary['controls_admitted'] and summary['attempted_controls']==2
    assert not summary['training_authorized'] and module.runner.run_cmd is old


@pytest.mark.parametrize('field',['execution_complete','cleanup_complete','output_complete'])
def test_incomplete_cannot_admit(tmp_path,field):
    def broken(*args):
        row=execute(*args);row[field]=False;return row
    module.controls(tmp_path/'run',execute=broken,identify=lambda:{})
    assert not json.loads((tmp_path/'run/summary.json').read_text())['controls_admitted']


def test_runtime_drift_blocks(tmp_path):
    runtime=iter([{}, {'new':True}]);old=module.runner.run_cmd
    with pytest.raises(ValueError,match='Identity drift'):
        module.controls(tmp_path/'run',execute=execute,identify=lambda:next(runtime))
    assert module.runner.run_cmd is old


def test_budget_stops_checks(tmp_path):
    times=iter([0,60,60,60])
    module.controls(tmp_path/'run',execute=lambda *args:pytest.fail('Over budget check'),
                    identify=lambda:{},clock=lambda:next(times))
    summary=json.loads((tmp_path/'run/summary.json').read_text())
    assert summary['attempted_controls']==0 and not summary['controls_admitted']
