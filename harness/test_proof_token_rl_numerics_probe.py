"""Pure diagnostic reporting/selection tests; no GPU, checkpoints, or jobs."""
import pytest
import torch
from tools.proof_token_rl_numerics_probe import compare,select_rows


def test_comparison_preserves_frozen_tolerances_and_exactness():
    exact=compare(torch.tensor([-1.,-2.]),[-1.,-2.])
    assert exact['bitwise_equal'] and exact['within_frozen_tolerance']
    drift=compare(torch.tensor([-1.,-2.05]),[-1.,-2.])
    assert not drift['within_frozen_tolerance'] and drift['worst_token_index']==1
    assert drift['max_abs']==pytest.approx(.05,abs=1e-6)
    mean=compare(torch.tensor([-1.01,-2.01]),[-1.,-2.])
    assert mean['max_abs']<.03 and not mean['within_frozen_tolerance']


@pytest.mark.parametrize('values,expected',[(torch.tensor([float('nan')]),[0.]),
    (torch.tensor([0.]),[float('nan')]),(torch.tensor([[0.]]),[0.]),
    (torch.tensor([]),[]),(torch.tensor([0.,0.]),[0.])])
def test_nonfinite_or_mismatched_comparison_rejected(values,expected):
    with pytest.raises(ValueError):compare(values,expected)


def fixture():
    rows=[];rewards=[]
    for i in range(32):
        rows.append(dict(sample_id=str(i),finish_reason='eos',input_token_ids=[1]*(100 if i==24 else 2),token_ids=[2,3]))
        rewards.append(dict(task_id='task'+str(i//4),prompt_sha256='a'*64,policy_sha256='b'*64,
            split='train',finish_reason='eos',measured_model_outcome=True,reward_eligible=True,
            reward=i%2 if 8<=i<12 else 1))
    return rows,rewards


def test_selection_longest_complete_then_whole_eligible_group():
    rows,rewards=fixture()
    assert [r['sample_id'] for r in select_rows(rows,rewards)]==['24','8','9','10','11']
    rows[24]['finish_reason']='token_limit';rewards[24]['finish_reason']='token_limit'
    assert [r['sample_id'] for r in select_rows(rows,rewards)]==['0','8','9','10','11']


def test_selection_does_not_duplicate_longest_or_silently_filter():
    rows,rewards=fixture();rows[8]['input_token_ids']=[1]*200
    assert [r['sample_id'] for r in select_rows(rows,rewards)]==['8','9','10','11']
    with pytest.raises(ValueError):select_rows(rows[:-1],rewards)
