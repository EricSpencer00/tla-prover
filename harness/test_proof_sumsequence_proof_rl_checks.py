from copy import deepcopy
import json
from pathlib import Path
import pytest
from tools import proof_sumsequence_proof_rl_checks as checks


@pytest.fixture(scope='module')
def tasks():
    return checks.policy.broader.export_tasks()[1]+checks.policy.extra.static_tasks()


def test_all40_actual_reference_extractors_and_assemblies(tasks):
    assert len(tasks)==40
    for task in tasks:
        fragment=checks.extract(task,task['reference_fragment'])['fragment']
        assert fragment is not None and fragment.strip()==task['reference_fragment'].strip()
        checks._validator(task)(task['prefix'],fragment,task['suffix'],task['theorem_name'])
        assert checks.sha((task['prefix']+task['reference_fragment']+task['suffix']).encode())==task['assembled_sha256']


def test_legacy_dev_requires_legacy_adapter_not_wholeproof(tasks):
    for task in tasks[32:36]:
        checks.legacy.validate_fragment(task['prefix'],task['reference_fragment'],task['suffix'],task['theorem_name'])
        with pytest.raises(ValueError):
            checks.full.validate_fragment(task['prefix'],task['reference_fragment'],task['suffix'],task['theorem_name'])


def test_negative_controls_preserve_legacy_assumptions(tasks):
    population=checks.control_population(tasks)
    assert len(population)==46 and [t['id'] for t,l in population[40:]]==[tasks[i]['id'] for i in (0,32,33,34,35,36)]
    for index in (32,33,34,35):
        original=tasks[index];bad=checks.negative_task(original)
        assert bad['reference_fragment']==original['reference_fragment'] and bad['suffix']==original['suffix']
        assert bad['prefix'].count('ASSUME')==original['prefix'].count('ASSUME')
        assert bad['prefix'].count('NEW')==original['prefix'].count('NEW')
        if index in (32,33):
            assert bad['prefix'].rsplit('=>',1)[0]==original['prefix'].rsplit('=>',1)[0]
        else:
            assert bad['prefix'].rsplit('PROVE',1)[0]==original['prefix'].rsplit('PROVE',1)[0]


def process(command,cwd,output,complete=True):
    return dict(command=command,cwd=str(cwd),returncode=0,output=output,seconds=.01,
        execution_complete=complete,cleanup_complete=complete,output_complete=complete,timed_out=False,output_limit=False)


def test_actual_legacy_sany_assembly_and_raw_audit(tasks,tmp_path):
    task=tasks[32];fragment=task['reference_fragment']
    def execute(command,cwd,timeout):
        candidate=Path(cwd)/command[-1]
        assert candidate.read_text()==task['prefix']+fragment+task['suffix']
        return process(command,cwd,'Semantic processing of module '+candidate.stem+'\n')
    result=checks.sany_check(task,fragment,tmp_path/'check',execute=execute)
    assert result['reward']==1
    current=dict(java=result['command'][0],library=checks.runner.TLA_LIBRARY,classpath=checks.runner.CLASSPATH)
    checks.audit_sany(task,fragment,result,current)
    (Path(result['workdir'])/'sany.log').write_text('tampered')
    with pytest.raises(ValueError):checks.audit_sany(task,fragment,result,current)


def test_incomplete_owned_sany_is_unknown(tasks,tmp_path):
    task=tasks[32]
    def execute(command,cwd,timeout):return process(command,cwd,'Semantic processing of module MC\n',False)
    result=checks.sany_check(task,task['reference_fragment'],tmp_path/'check',execute=execute)
    assert result['reward'] is None and result['status']=='unmeasured_timeout'


def test_new_statement_metadata_failure_is_instrument_failure(tasks):
    task=dict(tasks[36],statement='bad')
    with pytest.raises(ValueError):checks.extract(task,'garbage')


def test_negative_control_requires_intended_parsed_obligation(tasks):
    task=checks.negative_task(tasks[32])
    record=dict(status='verifier_reject',returncode=10,timed_out=False,certified=False,
        output='[ERROR]: 1/6 obligations failed.\n PROVE TypeOK /\\ [Next]_vars => FALSE\n')
    value=dict(sany=1,proof_evidence=dict(strict=record))
    assert checks.intended_negative(task,value)
    for text in ('Semantic errors: unknown operator f','[ERROR]: 1/6 obligations failed.\nPROVE FALSE\n'):
        record['output']=text;assert not checks.intended_negative(task,value)
