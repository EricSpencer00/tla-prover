from copy import deepcopy
import json
import pytest
from tools import proof_sumsequence_feedback_packet as packet


@pytest.fixture
def inputs():
    root=packet.ROOT/'results/runs'
    cycle=root/'proof-sumsequence-stochastic-cycle-20260906-v1'
    evaluation=json.loads((cycle/'freeze.json').read_bytes())['arms']['child']['evaluation']
    raw=[json.loads(l) for l in (cycle/'child/rollouts.jsonl').read_bytes().splitlines()]
    records=json.loads((root/'proof-sumsequence-stochastic-verified-20260906-v2/rows.json').read_bytes())[32:]
    return evaluation,raw,records


def test_actual_child32_feedback_keeps_all_attempts(inputs):
    result=packet.build(*inputs)
    assert len(result['rewards'])==32 and result['eligible_groups']==1
    assert result['groups'][1]['rewards']==[0.,1.,0.,0.]
    assert result['groups'][1]['advantages']==[-.25,.75,-.25,-.25]
    assert result['groups'][0]['exclusion']=='incomplete_generation'
    assert result['training_authorized'] is False and result['numerical_admission_required'] is True
    assert sum(r['reward'] is None for r in result['rewards'])==2


@pytest.mark.parametrize('which',[1,2])
def test_filtering_attempts_rejected(inputs,which):
    args=list(inputs);args[which]=args[which][1:]
    with pytest.raises(ValueError,match='All32'):packet.build(*args)


@pytest.mark.parametrize('kind',['order','hash','policy','boolean','cap_positive','cap_negative','finish'])
def test_feedback_corruption_rejected(inputs,kind):
    evaluation,raw,records=deepcopy(inputs)
    if kind=='order':records[0],records[1]=records[1],records[0]
    elif kind=='hash':records[0]['rollout_sha256']='wrong'
    elif kind=='policy':evaluation['policy_sha256']=packet.verifier.sampling.POLICIES['parent']
    elif kind=='boolean':records[4]['proof']=True
    elif kind.startswith('cap'):
        row=next(r for r in records if r['proof'] is None);row['proof']=1 if kind=='cap_positive' else 0
    else:records[4]['finish_reason']='token_limit'
    with pytest.raises(ValueError):packet.build(evaluation,raw,records)
