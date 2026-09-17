import copy
import json
from pathlib import Path

import pytest

from tools.proof_outcome_audit import classify_outcome

ROOT=Path(__file__).resolve().parents[1]


@pytest.fixture(scope='module')
def actual():
    result={}
    for arm,name in [('base','proof-cuda-fresh14-base-verified-20260905-v1'),
                     ('child','proof-cuda-fresh14-child-verified-20260905-v2')]:
        result[arm]={r['id']:r for r in map(json.loads,(ROOT/'results/runs'/name/'rows.jsonl').read_text().splitlines())}
    return result


def classify(row):return classify_outcome(row,provenance_verified=True)


@pytest.mark.parametrize('arm,task,expected',[
    ('child','fresh-DieHard-DieHard_proof-MinNat','proof_success'),
    ('base','fresh-DieHard-DieHard_proof-MinNat','model_contract'),
    ('base','fresh-Paxos-Consensus-LivenessTheorem','model_parse'),
    ('child','fresh-Paxos-Consensus-LivenessTheorem','model_parse'),
    ('base','fresh-byzpaxos-Consensus-LiveSpecEquals','model_parse'),
    ('child','fresh-spanning-spanning_proof-SntMsgInv','model_parse'),
    ('child','fresh-byzpaxos-Consensus-EnabledDef','model_scope'),
    ('child','fresh-ewd840-EWD840_proof-Safety','model_scope'),
    ('base','fresh-ewd998-AsyncTerminationDetection_proof-EnabledDT','unproved_obligation'),
    ('child','fresh-spanning-spanning_proof-SntMsgStep','unproved_obligation'),
])
def test_actual_diagnostic_anchors(actual,arm,task,expected):
    row=actual[arm][task];original=copy.deepcopy(row)
    answer=classify(row)
    assert answer['classification']==expected
    assert answer['measured_model_outcome'] and answer['reward_eligible']
    assert row==original


def test_actual_assertion_never_model_negative(actual):
    row=actual['child']['fresh-ewd840-SyncTerminationDetection_proof-Quiescent']
    assert row['returncode']==3
    assert 'e_levels.ml' in row['output'] and 'Assertion failed' in row['output']
    assert classify(row)['classification']=='unmeasured_checker_internal'
    assert not classify(row)['reward_eligible']


@pytest.mark.parametrize('suffix',['Error: Operator "Foo" not found',
    'tlapm ending abnormally with Failure("Proof.Parser")',
    '[INFO]: All 1 obligations proved.','[ERROR]: 1/1 obligation failed.'])
def test_assertion_overrides_other_diagnostics(actual,suffix):
    row=copy.deepcopy(actual['child']['fresh-ewd840-SyncTerminationDetection_proof-Quiescent'])
    row['output']+='\n'+suffix
    assert classify(row)['classification']=='unmeasured_checker_internal'


@pytest.mark.parametrize('text',[
    'Unknown mysterious exit', 'Error: some other failure',
    'tlapm ending abnormally with Failure("Unknown.Parser")',
    'tlapm ending abnormally with Failure("Expr.Anon: 99")',
    'There were backend errors processing module',
    'Zenon error: strange unknown failure',
])
def test_unknown_nonzero_fail_closed(actual,text):
    row=copy.deepcopy(actual['child']['fresh-byzpaxos-Consensus-EnabledDef']);row['output']=text
    answer=classify(row)
    assert answer['classification']=='unmeasured_unknown'
    assert not answer['measured_model_outcome'] and not answer['reward_eligible']


@pytest.mark.parametrize('key,value',[
    ('returncode',11),('total',0),('proved',0),('certified',False),('command',['tlapm']),
    ('candidate_path',None),('sha256','bad'),('timed_out',True),
])
def test_success_requires_complete_strict_record(actual,key,value):
    row=copy.deepcopy(actual['child']['fresh-DieHard-DieHard_proof-MinNat']);row[key]=value
    assert classify(row)['classification']!='proof_success'
    assert not classify(row)['reward_eligible']


def test_caller_must_bind_provenance(actual):
    row=actual['child']['fresh-DieHard-DieHard_proof-MinNat']
    result=classify_outcome(row)
    assert result['classification']=='proof_success'
    assert not result['measured_model_outcome'] and not result['reward_eligible']


@pytest.mark.parametrize('text',['Executable "z3" not found','z3: command not found',
    'No space left on device','solver timed out'])
def test_infrastructure_overrides_unproved(actual,text):
    row=copy.deepcopy(actual['child']['fresh-spanning-spanning_proof-SntMsgStep']);row['output']+='\n'+text
    assert classify(row)['classification']=='unmeasured_infrastructure'
    assert not classify(row)['reward_eligible']


def test_scaffold_contract_is_not_model_negative():
    row=dict(certified=False,status='contract_reject',reason='full-fragment prefix already contains target proof',sha256='a'*64)
    assert classify(row)['classification']=='unmeasured_unknown'


def test_unknown_error_prevents_unproved_rejection(actual):
    row=copy.deepcopy(actual['child']['fresh-spanning-spanning_proof-SntMsgStep'])
    row['output']+='\nError: unexplained backend condition\n'
    assert classify(row)['classification']=='unmeasured_unknown'


def test_unknown_fatal_prevents_parse_rejection(actual):
    row=copy.deepcopy(actual['child']['fresh-Paxos-Consensus-LivenessTheorem'])
    row['output']+='\nFatal error: mysterious new condition\n'
    assert classify(row)['classification']=='unmeasured_unknown'


def test_arbitrary_partial_generation_is_not_model_contract():
    assert classify(dict(status='generation_time_limit',certified=False))['classification']=='unmeasured_unknown'


def test_malformed_and_nonboolean_provenance():
    assert classify(None)['classification']=='unmeasured_unknown'
    with pytest.raises(ValueError):classify_outcome({},provenance_verified='yes')
