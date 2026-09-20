import torch
from tools.proof_saved_tensor_census import Census,experiment


def test_views_deduplicated_and_exact():
    model=torch.nn.Linear(3,2);census=Census(model,offload=True)
    base=torch.arange(48.).reshape(4,12)
    a=base[:,1:9:2];b=base[1:3,:].T
    pa=census.pack(a);pb=census.pack(b)
    assert len(census.copies)==1
    assert torch.equal(census.unpack(pa),a) and torch.equal(census.unpack(pb),b)
    assert census.report()['copied_unique_bytes']==base.untyped_storage().nbytes()


def test_resident_parameters_never_copied():
    model=torch.nn.Linear(3,2);census=Census(model,offload=True)
    assert census.pack(model.weight)[0]=='resident'
    assert not census.copies
    packed=census.pack(model.weight)
    assert not packed[1].requires_grad and packed[1].grad_fn is None
    assert packed[1].untyped_storage().data_ptr()==model.weight.untyped_storage().data_ptr()


def test_vocab_classifier_and_isfinite_duplicate_pack():
    from types import SimpleNamespace
    model=torch.nn.Linear(3,2);model.config=SimpleNamespace(vocab_size=128)
    census=Census(model,offload='vocab_only')
    unrelated=torch.ones(128,requires_grad=True)*2
    assert census.pack(unrelated)[0]=='resident'
    scores=torch.randn(128,requires_grad=True)
    with torch.autograd.graph.saved_tensors_hooks(census.pack,census.unpack):
        logps=scores.log_softmax(-1)
        assert torch.isfinite(logps).all()
        chosen=logps[3]
    category=census.report()['categories']['fp32_vocab_vector']
    assert category['pack_calls']==2 and category['unique_storages']==1
    assert len(census.copies)==1
    assert {r['grad_fn'] for r in census.calls if r['kind']=='fp32_vocab_vector'}=={'LogSoftmaxBackward0'}
    chosen.backward()
    assert torch.isfinite(scores.grad).all()


def test_real_llama_exact_offload_and_detached_negative():
    report=experiment(lengths=(4,12),prompt_length=24)
    assert report['optimizer_updates']==0
    for row in report['rows']:
        assert row['all_nine_gradients_exact'] and row['exact_token_logprobs']
        assert any(row['detached_cache_gradient_max_delta'].values())
        assert row['selective_unique_storage_cpu_copy']['copied_unique_storages']>0
        assert row['vocab_only_values_and_all_nine_gradients_exact']
        narrow=row['vocab_only_cpu_copy']
        assert narrow['copied_unique_storages']==row['response_tokens']
        assert narrow['categories']['fp32_vocab_vector']['unique_storages']==row['response_tokens']
