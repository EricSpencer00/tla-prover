import ast
from pathlib import Path
from types import SimpleNamespace
import pytest
import torch
from torch.multiprocessing.reductions import StorageWeakRef
from tools.proof_token_rl_cached_score import cached_token_logps as original
from tools.proof_token_rl_cached_score_compact import cached_token_logps as compact
from tools.proof_logprob_offload import LogprobOffload
from tools.proof_saved_tensor_census import tiny_model,detach_cache_wrapper
from tools.proof_token_rl_sampling import sample_tokens


def test_only_executable_change_is_selected_scalar_clone():
    root=Path(__file__).resolve().parents[1]/'tools'
    baseline=(root/'proof_token_rl_cached_score.py').read_text()
    candidate=(root/'proof_token_rl_cached_score_compact.py').read_text()
    expected=ast.parse(baseline.replace('selected.append(logps[ident])','selected.append(logps[ident].clone())'))
    actual=ast.parse(candidate)
    expected.body.pop(0);actual.body.pop(0)
    assert ast.dump(actual)==ast.dump(expected)


def test_cloned_scalar_releases_full_storage_before_stack_and_backward():
    for clone in (False,True):
        scores=torch.randn(128,requires_grad=True)
        context=LogprobOffload(128,1,allow_cpu=True)
        with context:
            logps=scores.log_softmax(-1)
            storage_ref=StorageWeakRef(logps.untyped_storage())
            selected=[logps[3].clone() if clone else logps[3]]
            assert selected[0].untyped_storage().nbytes()==(4 if clone else 512)
            del logps
            # StorageWeakRef queries C++ allocation lifetime, not Tensor-object
            # weakrefs: the scalar view itself keeps its 512-byte storage alive.
            assert storage_ref.expired() is clone
            result=torch.stack(selected)
        context.validate('forward')
        result.sum().backward();context.validate('backward')
        assert torch.isfinite(scores.grad).all()


def run_replay(model,prompt,response,scorer,detach=False):
    model.zero_grad(set_to_none=True)
    context=LogprobOffload(128,len(response),allow_cpu=True)
    with context:
        result=scorer(detach_cache_wrapper(model) if detach else model,prompt,response,
                      eos_token_ids=[127],seconds=20,max_context=512,
                      context_factory=lambda:torch.autocast('cpu',dtype=torch.bfloat16))
    context.validate('forward');result.sum().backward();context.validate('backward')
    gradients={n:p.grad.detach().clone() for n,p in model.named_parameters() if p.requires_grad}
    return result.detach().clone(),gradients


def test_real_llama_compact_offload_exact_all_nine_and_causal_negative():
    model=tiny_model();initial={n:p.detach().clone() for n,p in model.named_parameters()}
    for length in (4,12,32):
        prompt=torch.arange(64)%126+1
        response=torch.cat((torch.arange(length-1)%126+1,torch.tensor([127])))
        baseline,grads=run_replay(model,prompt,response,original)
        actual,actual_grads=run_replay(model,prompt,response,compact)
        assert torch.equal(baseline,actual) and len(actual_grads)==9
        assert all(g.dtype==torch.float32 and torch.isfinite(g).all() and torch.equal(grads[n],g)
                   for n,g in actual_grads.items())
        negative,negative_grads=run_replay(model,prompt,response,compact,detach=True)
        assert torch.equal(actual,negative)
        assert any(not torch.equal(actual_grads[n],negative_grads[n]) for n in grads)
    assert all(torch.equal(initial[n],p) for n,p in model.named_parameters())


class SampleFixture(torch.nn.Module):
    def __init__(self):
        super().__init__();self.bias=torch.nn.Parameter(torch.zeros(8));self.calls=[]
    def forward(self,input_ids,attention_mask,past_key_values,use_cache):
        self.calls.append((input_ids.tolist(),attention_mask.tolist(),past_key_values is None,use_cache))
        step=attention_mask.shape[1]-4
        logits=self.bias+torch.nn.functional.one_hot(torch.tensor([1,2,7][step]),8)*1000
        return SimpleNamespace(logits=logits.expand(1,input_ids.shape[1],8),past_key_values=object())


def test_actual_sampling_call_shapes_and_eos_identical():
    model=SampleFixture();prompt=torch.tensor([1,2,3,4])
    sampled=sample_tokens(model,prompt,generator=torch.Generator().manual_seed(5),
                          eos_token_ids=[7],max_new_tokens=3,seconds=5,max_context=32)
    calls=list(model.calls);model.calls.clear()
    assert sampled['finish_reason']=='eos' and sampled['token_ids']==[1,2,7]
    response=torch.tensor(sampled['token_ids'])
    values=compact(model,prompt,response,eos_token_ids=[7],seconds=5,max_context=32)
    assert model.calls==calls
    assert values.tolist()==sampled['selected_token_logprobs']
    values.sum().backward();assert torch.isfinite(model.bias.grad).all()


@pytest.mark.parametrize('response',[[1,2],[7,1,7],[]])
def test_no_synthetic_or_early_eos(response):
    with pytest.raises(ValueError):
        compact(SampleFixture(),torch.tensor([1,2,3,4]),torch.tensor(response,dtype=torch.long),
                eos_token_ids=[7],seconds=5,max_context=32)
