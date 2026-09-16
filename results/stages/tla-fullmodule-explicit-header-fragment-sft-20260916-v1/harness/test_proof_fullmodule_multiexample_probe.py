import json
from contextlib import nullcontext

import pytest
from tools import proof_fullmodule_multiexample_probe as m

PACKET = m.ROOT / 'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json'


def test_pinned_train_eval_rows_and_hashes():
    chosen, value = m.selected(PACKET.read_bytes())
    assert set(chosen) == {44, 49, 47, 107}
    assert [chosen[i][0]['id'] for i in m.TRAIN_ROWS] == [m.ROW_IDS[44], m.ROW_IDS[49]]
    assert [chosen[i][0]['id'] for i in m.EVAL_ROWS] == [m.ROW_IDS[47], m.ROW_IDS[107]]
    assert all(chosen[i][0]['split'] == 'train' for i in chosen)
    assert all(m.checker_task(value, chosen[i][0])['module_name'].startswith('W4O') for i in chosen)


def test_stage_tasks_are_isolated(tmp_path):
    chosen, value = m.selected(PACKET.read_bytes())
    staged = [m.stage_task(m.checker_task(value, chosen[i][0]), tmp_path, str(i)) for i in chosen]
    assert len({x['source']['path'] for x in staged}) == 4
    assert all((tmp_path / 'reference' / str(i)).is_dir() for i in chosen)


@pytest.mark.parametrize('tokens,elapsed,finish', [([128009], .1, 'eos'), ([1]*1024, .1, 'token_limit'), ([], 46., 'time_limit')])
def test_exact_generation_accounting(tokens, elapsed, finish):
    assert m.output_fields(tokens, '', elapsed)['finish_reason'] == finish


def test_invalid_tokens_rejected():
    with pytest.raises(ValueError): m.output_fields([True], '', .1)


def test_distinct_lineage_and_policy_checkpoint_pins():
    pins = {'lineage': m.lineage.CHILD_SHA, 'policy': m.POLICY_SHA}
    m.validate_pins('lineage', 'policy', file_hash=pins.__getitem__)
    with pytest.raises(ValueError, match='8866'): m.validate_pins('policy', 'policy', file_hash=pins.__getitem__)
    with pytest.raises(ValueError, match='fba'): m.validate_pins('lineage', 'lineage', file_hash=pins.__getitem__)


def test_fixed_order_response_only_two_example_update(monkeypatch):
    torch = pytest.importorskip('torch')
    class Tiny(torch.nn.Module):
        def __init__(self): super().__init__(); self.p = torch.nn.Parameter(torch.zeros(7))
        def forward(self, input_ids, labels=None, **kwargs):
            logits = self.p[None, None, :].expand(1, input_ids.shape[1], 7)
            return type('R', (), dict(logits=logits, loss=torch.nn.functional.cross_entropy(logits[:, :-1].reshape(-1, 7), labels[:, 1:].reshape(-1), ignore_index=-100)))()
    net = Tiny(); monkeypatch.setattr(m, 'BUDGET', dict(m.BUDGET, updates=3)); seen = []
    monkeypatch.setattr(m.lineage, 'gradients', lambda selected: {'p': float(selected['p'].grad.norm())})
    encs = [dict(input_ids=[1, 2, 3], labels=[-100, 2, 3]), dict(input_ids=[1, 4, 5], labels=[-100, 4, 5])]
    opt, rows = m.update(net, dict(net.named_parameters()), encs, device='cpu', context=nullcontext, measure=lambda x: seen.append(x))
    assert len(rows) == 3 and len(seen) == 3 and opt.state
    assert all(r['gradient_norms']['p'] > 0 and len(r['loss']) == 2 for r in rows)


def test_no_gate_or_generalization_claims():
    assert m.BUDGET['updates'] == 128 and m.BUDGET['max_new_tokens'] == 1024
    assert tuple(m.BUDGET['eval_rows']) == m.EVAL_ROWS
    assert not any(m.BUDGET[k] for k in ('gate_claim', 'generalization_claim', 'proof_claim', 'tlc_claim', 'nonvacuity_claim'))
    assert m.POLICY_SHA != m.lineage.CHILD_SHA


def test_footer_processor_forces_eos_only_after_complete_footer():
    torch = pytest.importorskip('torch')
    proc = m.ForceEosAfterFooter([8, 9], 99, prompt_tokens=3)
    scores = torch.zeros((2, 120))
    # First row has prompt + pinned header + complete footer.
    out = proc(torch.tensor([[1, 2, 3, 4, 8, 9], [1, 2, 3, 4, 8, 7]]), scores)
    assert out[0, 99] == 0 and torch.isneginf(out[0]).sum() == 119
    assert torch.equal(out[1], torch.zeros(120))


def test_decode_prefix_is_context_and_total_budget_is_reserved(monkeypatch):
    torch = pytest.importorskip('torch')

    class Tokenizer:
        eos_token_id = 99
        pad_token_id = 0

        def encode(self, text, add_special_tokens=False):
            return {'HEADER\n': [20, 21], '====': [8, 9]}[text]

        def decode(self, ids, **kwargs):
            return 'decoded:' + ','.join(map(str, ids))

    class Net:
        def __init__(self):
            self.kwargs = None

        def generate(self, **kwargs):
            self.kwargs = kwargs
            ids = kwargs['input_ids']
            # The returned sequence includes the input context, as HF does.
            return torch.cat((ids, torch.tensor([[7, 99]], device=ids.device)), dim=1)

    net = Net()
    enc = {'input_ids': [1, 2, 3, 4], 'prompt_tokens': 2}
    monkeypatch.setattr(m, 'BUDGET', dict(m.BUDGET, max_new_tokens=6))
    result = m.decode(net, Tokenizer(), enc, device='cpu', forced_prefix='HEADER\n')
    assert net.kwargs['input_ids'].tolist() == [[1, 2, 20, 21]]
    assert net.kwargs['max_new_tokens'] == 8  # full body budget plus two pinned header ids
    assert result['token_ids'] == [20, 21, 7, 99]
    assert result['raw_reply'].startswith('decoded:20,21')
