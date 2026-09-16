from contextlib import contextmanager
from types import SimpleNamespace

import pytest
import torch

from tools.proof_token_rl_cached_score import cached_token_logps
from tools.proof_token_rl_sampling import sample_tokens


class Causal(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.table = torch.nn.Parameter(torch.arange(16.).reshape(4, 4) / 7)
        self.child = torch.nn.Dropout(.5)
        self.calls = []

    def forward(self, input_ids, attention_mask, past_key_values=None, use_cache=True):
        old = 0 if past_key_values is None else past_key_values
        assert attention_mask.shape == (1, old + input_ids.shape[1])
        assert bool((attention_mask == 1).all()) and use_cache
        self.calls.append((input_ids.tolist(), old, torch.is_grad_enabled(), self.training))
        return SimpleNamespace(logits=self.table[input_ids],
                               past_key_values=old + input_ids.shape[1])


def score(model, response=None, **kwargs):
    args = dict(eos_token_ids=[3], seconds=10)
    args.update(kwargs)
    return cached_token_logps(model, torch.tensor([0, 1]),
                              torch.tensor([2, 1, 3]) if response is None else response, **args)


def test_exact_calls_differentiability_and_modes():
    model = Causal().train(); model.child.eval()
    result = score(model)
    assert result.shape == (3,) and result.dtype == torch.float32 and result.requires_grad
    assert model.calls == [([[0, 1]], 0, True, False), ([[2]], 2, True, False),
                           ([[1]], 3, True, False)]
    assert model.training and not model.child.training
    result.sum().backward()
    assert model.table.grad.abs().sum() > 0


def test_no_grad_caller_preserved_for_numerical_replay():
    model = Causal().train(); model.child.eval()
    with torch.no_grad():
        result = score(model)
    assert not result.requires_grad and all(not call[2] for call in model.calls)
    assert model.training and not model.child.training
    torch.testing.assert_close(result, score(model).detach(), rtol=0, atol=0)


def test_eos_only_one_forward_no_append():
    model = Causal()
    assert score(model, torch.tensor([3])).shape == (1,)
    assert len(model.calls) == 1


@pytest.mark.parametrize('response', [[1], [3, 3], [3, 1], [], [-1, 3]])
def test_incomplete_or_interior_eos_rejected_before_forward(response):
    model = Causal()
    with pytest.raises(ValueError): score(model, torch.tensor(response, dtype=torch.long))
    assert not model.calls


@pytest.mark.parametrize('kwargs', [{'seconds':0}, {'seconds':float('nan')},
    {'max_context':4}, {'max_context':8193}, {'eos_token_ids':[]},
    {'eos_token_ids':[3, 3]}, {'clock':None}, {'context_factory':None}])
def test_bad_contract(kwargs):
    with pytest.raises(ValueError): score(Causal(), **kwargs)


@pytest.mark.parametrize('ids', [torch.tensor([1.,3.]), torch.tensor([[1,3]])])
def test_response_requires_one_dimensional_long_ids(ids):
    with pytest.raises(ValueError): score(Causal(), ids)


def test_nonfinite_and_out_of_vocab_fail_closed():
    model = Causal().train()
    with torch.no_grad(): model.table[1,0] = float('nan')
    with pytest.raises(ValueError, match='Finite'): score(model)
    assert model.training
    with pytest.raises(ValueError, match='in-vocabulary'):
        score(Causal(), torch.tensor([9]), eos_token_ids=[9])


def test_no_trainable_graph_rejected_except_explicit_no_grad():
    model = Causal().requires_grad_(False)
    with pytest.raises(ValueError, match='Differentiable policy'): score(model)
    with torch.no_grad(): assert score(model).shape == (3,)


@pytest.mark.parametrize('ticks,calls', [([0, 2], 0), ([0, 0, 2], 1),
                                      ([0, 0, 0, 2], 1)])
def test_soft_deadline_fails_closed_and_restores_modes(ticks, calls):
    model = Causal().train(); model.child.eval(); clock = iter(ticks)
    with pytest.raises(TimeoutError): score(model, seconds=1, clock=lambda:next(clock))
    assert len(model.calls) == calls and model.training and not model.child.training


def test_context_each_call_and_no_cache_failure():
    entries = []
    @contextmanager
    def context():
        entries.append('enter'); yield; entries.append('exit')
    score(Causal(), context_factory=context)
    assert entries == ['enter'] + ['enter', 'exit'] * 3 + ['exit']
    class Missing(Causal):
        def forward(self, **kwargs):
            result = super().forward(**kwargs); result.past_key_values = None; return result
    model = Missing().train()
    with pytest.raises(ValueError, match='cache'): score(model)
    assert model.training


def tiny_llama():
    from transformers import LlamaConfig, LlamaForCausalLM
    torch.manual_seed(7)
    model = LlamaForCausalLM(LlamaConfig(vocab_size=8, hidden_size=16,
        intermediate_size=32, num_hidden_layers=2, num_attention_heads=2,
        num_key_value_heads=2, max_position_embeddings=128, attention_dropout=0))
    for parameter in model.parameters(): parameter.requires_grad_(False)
    for parameter in model.model.layers[-1].parameters(): parameter.requires_grad_(True)
    return model.eval()


def test_one_autocast_weight_cache_per_invocation_not_per_token():
    class TwoLinear(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.embedding=torch.nn.Embedding(32,32).requires_grad_(False)
            self.first=torch.nn.Linear(32,32,bias=False)
            self.second=torch.nn.Linear(32,32,bias=False)
        def forward(self,input_ids,attention_mask,past_key_values=None,use_cache=True):
            return SimpleNamespace(logits=self.second(self.first(self.embedding(input_ids))),
                past_key_values=(past_key_values or 0)+input_ids.shape[1])
    model=TwoLinear();prompt=torch.tensor([0,1]);response=torch.tensor([2]*20+[31])
    context=lambda:torch.autocast('cpu',dtype=torch.bfloat16)
    def replay():
        return cached_token_logps(model,prompt,response,eos_token_ids=[31],seconds=10,
                                  context_factory=context)
    # Separate invocation contexts prevent no_grad-created casts poisoning grads.
    with torch.no_grad():reference=replay()
    storages=set()
    def pack(tensor):
        if tensor.dtype==torch.bfloat16 and tensor.shape==(32,32):
            storages.add(tensor.untyped_storage().data_ptr())
        return tensor
    with torch.autograd.graph.saved_tensors_hooks(pack,lambda tensor:tensor):
        values=replay()
    assert 0<len(storages)<=2
    torch.testing.assert_close(values.detach(),reference,rtol=0,atol=0)
    values.sum().backward()
    assert model.first.weight.grad.norm()>0 and model.second.weight.grad.norm()>0


@pytest.mark.parametrize('bf16', [False, True])
def test_actual_llama_sampler_replay_and_full_sequence_gradients(bf16):
    model = tiny_llama(); prompt = torch.tensor([1, 2, 3])
    from contextlib import nullcontext
    context = (lambda:torch.autocast('cpu', dtype=torch.bfloat16)) if bf16 else nullcontext
    sampled = sample_tokens(model, prompt, generator=torch.Generator().manual_seed(91),
        eos_token_ids=[7], max_new_tokens=64, seconds=30, max_context=128,
        context_factory=context)
    assert sampled['finish_reason'] == 'eos' and len(sampled['token_ids']) > 1
    response = torch.tensor(sampled['token_ids'])
    replay = cached_token_logps(model, prompt, response, eos_token_ids=[7], seconds=30,
                                max_context=128, context_factory=context)
    with torch.no_grad():
        no_grad_replay = cached_token_logps(model, prompt, response, eos_token_ids=[7],
            seconds=30, max_context=128, context_factory=context)
    assert not no_grad_replay.requires_grad
    torch.testing.assert_close(no_grad_replay, replay.detach(), rtol=0, atol=1e-6)
    torch.testing.assert_close(replay.detach(), torch.tensor(sampled['selected_token_logprobs']),
                               rtol=0, atol=1e-6)
    (-replay.sum()).backward()
    cached_grads = {name:p.grad.clone() for name,p in model.named_parameters() if p.requires_grad}
    for suffix in ('k_proj.weight', 'v_proj.weight'):
        matching = [g for name,g in cached_grads.items() if name.endswith(suffix)]
        assert len(matching) == 1 and matching[0].abs().sum() > 0
    model.zero_grad(set_to_none=True)
    ids = torch.cat((prompt, response)).unsqueeze(0)
    with context():
        logits = model(input_ids=ids, attention_mask=torch.ones_like(ids), use_cache=False).logits
    full = logits[0, len(prompt)-1:-1].float().log_softmax(-1).gather(1, response[:,None])[:,0]
    (-full.sum()).backward()
    # CPU BF16 is a diagnostic only; FP32 establishes the differentiable-cache
    # correctness, including gradients through earlier trainable K/V tensors.
    if not bf16:
        torch.testing.assert_close(replay.detach(), full.detach(), rtol=1e-5, atol=2e-6)
        for name, parameter in model.named_parameters():
            if parameter.requires_grad:
                torch.testing.assert_close(cached_grads[name], parameter.grad, rtol=2e-4, atol=2e-6)
    else:
        assert torch.isfinite(full).all()
        assert all(torch.isfinite(g).all() for g in cached_grads.values())
