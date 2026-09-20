from contextlib import nullcontext

import pytest
from tools import proof_fullmodule_multiexample_4train_probe as m

PACKET = m.ROOT / 'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json'


def test_four_train_rows_and_two_eval_rows_are_pinned():
    chosen, value = m.selected(PACKET.read_bytes())
    assert tuple(m.TRAIN_ROWS) == (42, 43, 44, 49)
    assert tuple(m.EVAL_ROWS) == (47, 107)
    assert set(chosen) == set(m.TRAIN_ROWS + m.EVAL_ROWS)
    assert [chosen[i][0]['id'] for i in m.TRAIN_ROWS] == [m.ROW_IDS[i] for i in m.TRAIN_ROWS]
    assert [chosen[i][0]['id'] for i in m.EVAL_ROWS] == [m.ROW_IDS[i] for i in m.EVAL_ROWS]
    assert all(chosen[i][0]['split'] == 'train' for i in chosen)
    assert all(m.checker_task(value, chosen[i][0])['module_name'].startswith('W4O') for i in chosen)


def test_variant_has_more_structural_training_tokens_without_eval_leakage():
    chosen, _ = m.selected(PACKET.read_bytes())
    train_tokens = sum(chosen[i][1]['response_tokens'] for i in m.TRAIN_ROWS)
    eval_tokens = sum(chosen[i][1]['response_tokens'] for i in m.EVAL_ROWS)
    assert train_tokens == 1161 and eval_tokens == 833
    assert not set(m.TRAIN_ROWS) & set(m.EVAL_ROWS)


def test_variant_generation_accounting():
    assert m.output_fields([128009], '', .1)['finish_reason'] == 'eos'
    assert m.output_fields([1] * 1024, '', .1)['finish_reason'] == 'token_limit'
    assert m.output_fields([], '', 46.)['finish_reason'] == 'time_limit'
    with pytest.raises(ValueError): m.output_fields([True], '', .1)


def test_fixed_order_four_example_average_update_contract(monkeypatch):
    torch = pytest.importorskip('torch')
    class Tiny(torch.nn.Module):
        def __init__(self): super().__init__(); self.p = torch.nn.Parameter(torch.zeros(7))
        def forward(self, input_ids, labels=None, **kwargs):
            logits = self.p[None, None, :].expand(1, input_ids.shape[1], 7)
            return type('R', (), dict(logits=logits, loss=torch.nn.functional.cross_entropy(logits[:, :-1].reshape(-1, 7), labels[:, 1:].reshape(-1), ignore_index=-100)) )()
    net = Tiny(); monkeypatch.setattr(m, 'BUDGET', dict(m.BUDGET, updates=3)); seen = []
    monkeypatch.setattr(m.base.lineage, 'gradients', lambda selected: {'p': float(selected['p'].grad.norm())})
    encs = [dict(input_ids=[1, 2, 3], labels=[-100, 2, 3]), dict(input_ids=[1, 4, 5], labels=[-100, 4, 5]), dict(input_ids=[1, 3, 4], labels=[-100, 3, 4]), dict(input_ids=[1, 5, 6], labels=[-100, 5, 6])]
    opt, rows = m.update(net, dict(net.named_parameters()), encs, device='cpu', context=nullcontext, measure=lambda x: seen.append(x))
    assert len(rows) == 3 and len(seen) == 3 and opt.state
    assert all(r['gradient_norms']['p'] > 0 and len(r['loss']) == 4 for r in rows)


def test_no_gate_claims_and_exact_lineage_pins():
    assert m.BUDGET['updates'] == 128 and m.BUDGET['max_new_tokens'] == 1024
    assert not any(m.BUDGET[k] for k in ('gate_claim', 'generalization_claim', 'proof_claim', 'tlc_claim', 'nonvacuity_claim'))
    assert m.base.POLICY_SHA != m.base.lineage.CHILD_SHA


def test_worker_dispatch_configures_four_row_partition(monkeypatch):
    seen = {}
    monkeypatch.setattr(m.base, 'worker', lambda arg: seen.update(train=m.base.TRAIN_ROWS, eval=m.base.EVAL_ROWS) or {'ok': True})
    assert m.worker(object()) == {'ok': True}
    assert seen == {'train': (42, 43, 44, 49), 'eval': (47, 107)}
