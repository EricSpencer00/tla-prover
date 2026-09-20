from copy import deepcopy
import pytest
import torch
from tools.proof_logprob_offload import LogprobOffload,validate_report
from tools.proof_saved_tensor_census import tiny_model,replay,detach_cache_wrapper
from tools.proof_token_rl_cached_score import cached_token_logps


def synthetic():
    scores=torch.randn(128,requires_grad=True)
    context=LogprobOffload(128,1,allow_cpu=True)
    with context:
        logps=scores.log_softmax(-1)
        assert torch.isfinite(logps).all()
        selected=logps[3]
    return context,scores,selected


def test_duplicate_exact_copy_and_stage_accounting():
    context,scores,selected=synthetic()
    report=context.validate('forward')
    assert report['target_pack_calls']==2 and report['unique_storages']==1
    assert report['host_bytes']==512
    selected.backward()
    report=context.validate('backward')
    assert report['unpack_calls']==1 and report['records'][0]['restored_devices']==['cpu']
    assert torch.isfinite(scores.grad).all()
    with pytest.raises(ValueError,match='reuse'):context.__enter__()
    with pytest.raises(ValueError):context.validate('forward')
    with pytest.raises(ValueError):validate_report(report,vocab_size=128,response_tokens=1,stage='backward')


def test_completed_response_context_and_host_copy_release_without_gc():
    import weakref
    context,scores,selected=synthetic()
    context_ref=weakref.ref(context)
    host_refs=[weakref.ref(entry['host']) for entry in context.entries.values()]
    assert context.hooks is None
    selected.backward()
    context.validate('backward')
    del selected,context,scores
    # No gc.collect: per-response memory must not depend on cyclic collection.
    assert context_ref() is None
    assert all(ref() is None for ref in host_refs)


def test_cpu_production_rejected_and_failed_context():
    context=LogprobOffload(128,1)
    with pytest.raises(ValueError,match='CUDA'):
        with context:torch.randn(128,requires_grad=True).log_softmax(-1)
    assert context.report()['failed']
    with pytest.raises(ValueError):context.validate()


def test_count_budget_and_resident_graph_payload():
    with pytest.raises(ValueError,match='budget'):LogprobOffload(128256,3072)
    context=LogprobOffload(128,2,allow_cpu=True)
    tensor=torch.randn(128,requires_grad=True)*2
    with context:
        packed=context._pack(tensor)
        assert packed[0]=='resident' and not packed[1].requires_grad
        assert packed[1].untyped_storage().data_ptr()==tensor.untyped_storage().data_ptr()
    with pytest.raises(ValueError,match='accounting'):context.validate()


def test_duplicate_version_and_repeated_backward_refused():
    context=LogprobOffload(128,1,allow_cpu=True)
    with context:
        logps=torch.randn(128,requires_grad=True).log_softmax(-1)
        logps.detach().add_(0)
        with pytest.raises(ValueError,match='version'):context._pack(logps)
    context,scores,selected=synthetic()
    selected.backward(retain_graph=True)
    with pytest.raises(ValueError,match='Repeated'):selected.backward()


@pytest.mark.parametrize('field,value',[
    ('source_device','cuda:0'),('restored_devices',['cuda:0']),('host_bytes',0),
    ('dtype','torch.bfloat16'),('grad_fn','MulBackward0'),('unpack_calls',2),('pack_calls',0),
    ('shape',[127]),('stride',[2]),('version',-1),
])
def test_raw_metadata_tamper_refused(field,value):
    context,scores,selected=synthetic();selected.backward()
    report=deepcopy(context.validate('backward'));report['records'][0][field]=value
    with pytest.raises(ValueError):
        validate_report(report,vocab_size=128,response_tokens=1,stage='backward',require_cuda=False)


def test_real_llama_exact_all_nine_gradients_and_causal_negative():
    model=tiny_model();initial={n:p.detach().clone() for n,p in model.named_parameters()}
    for length in (4,12,32):
        prompt=torch.arange(48)%126+1
        response=torch.cat((torch.arange(length-1)%126+1,torch.tensor([127])))
        baseline,grads,_=replay(model,prompt,response)
        model.zero_grad(set_to_none=True)
        context=LogprobOffload(128,length,allow_cpu=True)
        with context:
            values=cached_token_logps(model,prompt,response,eos_token_ids=[127],seconds=20,max_context=512,
                context_factory=lambda:torch.autocast('cpu',dtype=torch.bfloat16))
        context.validate('forward');values.sum().backward();context.validate('backward')
        assert torch.equal(baseline,values)
        actual={n:p.grad for n,p in model.named_parameters() if p.requires_grad}
        assert len(actual)==9
        assert all(torch.equal(grads[n],g) and g.dtype==torch.float32 and torch.isfinite(g).all() for n,g in actual.items())
        negative,negative_grads,_=replay(model,prompt,response,detach=True)
        assert torch.equal(baseline,negative)
        assert any(not torch.equal(grads[n],negative_grads[n]) for n in grads)
    assert all(torch.equal(initial[n],p) for n,p in model.named_parameters())
