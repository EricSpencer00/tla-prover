import json
import pytest
from tools import proof_sumsequence_lemma2a as module


def test_exact_statement_and_bound_false():
    task=module.task()
    assert task['statement'] in task['prefix']
    assert 'ASSUME NEW S, NEW s \\in Seq(S), Len(s) > 1' in task['negative_prefix']
    assert task['negative_prefix'].endswith('PROVE  FALSE\n')
    assert 'Lemma2 ==' not in task['prefix'] and 'SequenceTheorems' not in task['prefix']
    assert all('DEFINE' not in text for _,text in module.CANDIDATES)


def execute(cmd,cwd,timeout):
    negative='false_conclusion' in cwd.parts
    return dict(command=list(cmd),cwd=str(cwd),returncode=10 if negative else 0,
        output=('[ERROR]: Could not prove or check:\n           ASSUME NEW S, NEW s \\in Seq(S), Len(s) > 1\n'
                '           PROVE  FALSE\n[ERROR]: 1/1 obligation failed.\n' if negative else 'All 1 obligations proved.\n'),
        seconds=.1,timed_out=False,execution_complete=True,cleanup_complete=True,output_complete=True)


def test_stops_on_first_pair_and_restores(tmp_path):
    original=module.runner.run_cmd
    module.controls(tmp_path/'run',execute=execute,identify=lambda:{})
    report=json.loads((tmp_path/'run/summary.json').read_text())
    assert report['controls_admitted'] and report['attempted_controls']==2 and report['winner']=='obvious'
    assert not report['training_authorized'] and module.runner.run_cmd is original


@pytest.mark.parametrize('field',['execution_complete','cleanup_complete','output_complete'])
def test_incomplete_never_admitted(tmp_path,field):
    def broken(*args):
        value=execute(*args);value[field]=False;return value
    module.controls(tmp_path/'run',execute=broken,identify=lambda:{})
    report=json.loads((tmp_path/'run/summary.json').read_text())
    assert not report['controls_admitted'] and report['attempted_controls']==6


def test_surviving_mutant_never_admitted(tmp_path):
    def survive(*args):
        value=execute(*args);value.update(returncode=0,output='All 1 obligations proved.\n');return value
    module.controls(tmp_path/'run',execute=survive,identify=lambda:{})
    assert not json.loads((tmp_path/'run/summary.json').read_text())['controls_admitted']


def test_runtime_drift(tmp_path):
    runtime=iter([{}, {'changed':True}])
    original=module.runner.run_cmd
    with pytest.raises(ValueError,match='Identity drift'):
        module.controls(tmp_path/'run',execute=execute,identify=lambda:next(runtime))
    assert module.runner.run_cmd is original
    assert not json.loads((tmp_path/'run/summary.json').read_text())['controls_admitted']
