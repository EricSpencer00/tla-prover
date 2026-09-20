"""Exercise actual pinned proof feedback and successful CUDA probe artifacts."""
from copy import deepcopy
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from tools import proof_sumsequence_proof_rl_packet as packet


@pytest.fixture
def actual():
    root=packet.ROOT/'results/runs'
    a=SimpleNamespace(
        probe_results=root/'proof-sumsequence-compact-offload-20260906-v1',
        feedback=root/'proof-sumsequence-feedback-compact-20260906-v1/feedback.json',
        rollouts=root/'proof-sumsequence-stochastic-cycle-20260906-v1/child/rollouts.jsonl',
        verified_rows=root/'proof-sumsequence-stochastic-verified-20260906-v2/rows.json')
    return a,packet.load(a.probe_results/'admission.json')


def test_actual_complete_prerequisites(actual):
    a,current=actual
    feedback=packet.validate_prerequisites(a,current)
    assert len(feedback['rewards'])==32 and feedback['eligible_groups']==1
    assert sum(r['reward'] is None for r in feedback['rewards'])==2
    assert feedback['groups'][1]['rewards']==[0,1,0,0]
    assert feedback['training_authorized'] is False


def test_successful_gpu_admission_cannot_drift(actual):
    a,current=actual
    current=deepcopy(current)
    current['budget']['memory_limit']+=1
    with pytest.raises(ValueError,match='current inputs'):
        packet.validate_prerequisites(a,current)


@pytest.mark.parametrize('mutation',['drop','reward','unknown','policy','proof_record','groups','authorization','source'])
def test_feedback_semantics_checked_beyond_hash(actual,tmp_path,monkeypatch,mutation):
    a,current=actual
    feedback=packet.load(a.feedback)
    if mutation=='drop':feedback['rewards'].pop()
    elif mutation=='reward':feedback['rewards'][4]['reward']=1
    elif mutation=='unknown':next(r for r in feedback['rewards'] if r['reward'] is None)['reward']=0
    elif mutation=='policy':feedback['policy_sha256']='0'*64
    elif mutation=='proof_record':feedback['rewards'][4]['proof_record_sha256']='0'*64
    elif mutation=='groups':feedback['groups'][1]['advantages'][0]=0
    elif mutation=='authorization':feedback['training_authorized']=True
    else:feedback['packet_source_sha256']='0'*64
    a=SimpleNamespace(**vars(a));a.feedback=tmp_path/'feedback.json'
    a.feedback.write_text(json.dumps(feedback))
    # Bypass only the outer artifact pin to exercise the internal binding checks.
    monkeypatch.setattr(packet,'FEEDBACK_SHA',packet.probe.train.file_sha(a.feedback))
    with pytest.raises(ValueError):packet.validate_prerequisites(a,current)


def test_wrong_feedback_bytes_fail_pin(actual,tmp_path):
    a,current=actual;a=SimpleNamespace(**vars(a));a.feedback=tmp_path/'feedback.json'
    a.feedback.write_text('{}')
    with pytest.raises(ValueError,match='full32 proof feedback'):
        packet.validate_prerequisites(a,current)


def test_training_budget_is_explicit_and_bounded():
    assert packet.BUDGET['seconds']==900
    assert packet.BUDGET['memory_limit']==36*1024**3
    assert packet.BUDGET['host_memory_limit']==64*1024**3
    assert packet.BUDGET['checkpoint_reserve']==120
    assert packet.BUDGET['requested_samples']==32
    assert packet.BUDGET['gradient_samples']==4
    assert packet.BUDGET['optimizer_updates']==1
    assert packet.BUDGET['max_logprob_error']==.03
    assert packet.BUDGET['mean_logprob_error']==.003
    assert packet.BUDGET['new_generation'] is False
