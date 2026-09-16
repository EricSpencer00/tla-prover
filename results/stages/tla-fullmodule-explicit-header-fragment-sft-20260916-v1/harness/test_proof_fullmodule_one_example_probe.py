import json
from contextlib import nullcontext

import pytest
from tools import proof_fullmodule_one_example_probe as m


def test_exact_shortest_train_row_and_hashes():
    row, enc, value = m.selected((m.ROOT/'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json').read_bytes())
    assert row['id'] == m.TASK_ID and row['split'] == 'train'
    assert enc['prompt_tokens'] == 385 and enc['response_tokens'] == 139
    task = m.checker_task(value, row)
    assert task['module_name'] == 'W4Od0m0p1t0'


@pytest.mark.parametrize('tokens,elapsed,finish', [([128009], .1, 'eos'), ([1]*256, .1, 'token_limit'), ([], 46., 'time_limit')])
def test_exact_generation_accounting(tokens, elapsed, finish):
    value=m.output_fields(tokens, '', elapsed)
    assert value['finish_reason']==finish


def test_invalid_tokens_rejected():
    with pytest.raises(ValueError): m.output_fields([True], '', .1)


def test_stage_isolated_train_reference(tmp_path):
    row, _, value=m.selected((m.ROOT/'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json').read_bytes())
    task=m.stage_task(m.checker_task(value,row),tmp_path)
    assert task['dependencies']=={} and (tmp_path/'reference/W4Od0m0p1t0.tla').is_file()


def test_distinct_lineage_and_policy_checkpoint_pins():
    pins={'lineage':m.lineage.CHILD_SHA,'policy':m.POLICY_SHA}
    m.validate_pins('lineage','policy',file_hash=pins.__getitem__)
    with pytest.raises(ValueError,match='8866'):
        m.validate_pins('policy','policy',file_hash=pins.__getitem__)
    with pytest.raises(ValueError,match='fba'):
        m.validate_pins('lineage','lineage',file_hash=pins.__getitem__)


def test_tiny_128_update_uses_response_only_labels(monkeypatch):
    torch=pytest.importorskip('torch')
    class Tiny(torch.nn.Module):
        def __init__(self): super().__init__();self.p=torch.nn.Parameter(torch.zeros(7))
        def forward(self,input_ids,labels=None,**kwargs):
            logits=self.p[None,None,:].expand(1,input_ids.shape[1],7)
            return type('R',(),dict(logits=logits,loss=torch.nn.functional.cross_entropy(logits[:,:-1].reshape(-1,7),labels[:,1:].reshape(-1),ignore_index=-100)))()
    net=Tiny(); monkeypatch.setattr(m,'BUDGET',dict(m.BUDGET,updates=3))
    monkeypatch.setattr(m.lineage,'gradients',lambda selected:{'p':float(selected['p'].grad.norm())})
    enc=dict(input_ids=[1,2,3],labels=[-100,2,3])
    opt, rows=m.update(net,dict(net.named_parameters()),enc,device='cpu',context=nullcontext)
    assert len(rows)==3 and opt.state and all(r['gradient_norms']['p']>0 for r in rows)


def test_source_closure_and_claims():
    # The inherited trainer's source closure may include historical packet code,
    # but this probe only admits the pinned TRAIN packet and never accepts a
    # holdout path/packet argument.
    assert 'packet' not in m.worker.__code__.co_varnames
    assert m.BUDGET['updates']==128 and m.BUDGET['train_only'] and not m.BUDGET['gate_claim']
    assert m.POLICY_SHA != m.lineage.CHILD_SHA
