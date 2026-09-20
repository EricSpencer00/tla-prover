"""Cheap real-Llama CPU saved-storage/offload mechanics; never GPU feasibility."""
import argparse
import json
import os
from pathlib import Path
import sys
import time
import weakref

for name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[name]='2'
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from tools.proof_token_rl_cached_score import cached_token_logps


class Census:
    def __init__(self,model,offload=False):
        self.parameter_storages={p.untyped_storage().data_ptr() for p in model.parameters()}
        self.weight_shapes={tuple(p.shape) for p in model.parameters()}
        self.weight_shapes|={tuple(reversed(s)) for s in self.weight_shapes}
        self.offload=offload;self.calls=[];self.storages={};self.copies={}
        self.vocab_size=getattr(getattr(model,'config',None),'vocab_size',None)
        self.vocab_tensor_refs=[]

    def pack(self,tensor):
        from torch.multiprocessing.reductions import StorageWeakRef
        storage=tensor.untyped_storage()
        # C++ weak storage identity avoids pointer-reuse collisions without
        # retaining the original device allocation after offload.
        key=(str(tensor.device),StorageWeakRef(storage),storage.nbytes(),str(tensor.dtype))
        shape=tuple(tensor.shape)
        grad_fn=type(tensor.grad_fn).__name__
        if (tensor.ndim==1 and str(tensor.dtype)=='torch.float32' and tensor.numel()==self.vocab_size
            and grad_fn=='LogSoftmaxBackward0'):
            kind='fp32_vocab_vector';self.vocab_tensor_refs.append(weakref.ref(tensor))
        elif storage.data_ptr() in self.parameter_storages:kind='resident_parameter'
        elif shape in self.weight_shapes:kind='weight_shape_candidate'
        elif tensor.ndim>=3:kind='activation_or_kv_3dplus'
        else:kind='other_activation'
        self.calls.append(dict(kind=kind,shape=list(shape),dtype=str(tensor.dtype),grad_fn=grad_fn,
            view_bytes=tensor.numel()*tensor.element_size(),storage_bytes=storage.nbytes()))
        self.storages.setdefault(key,dict(kind=kind,bytes=storage.nbytes(),shape=list(shape)))
        eligible=(kind=='fp32_vocab_vector' if self.offload=='vocab_only'
            else kind not in ('resident_parameter','weight_shape_candidate'))
        if not self.offload or not eligible:
            return ('resident',tensor.detach())
        if key not in self.copies:
            base=tensor.detach().as_strided((storage.nbytes()//tensor.element_size(),),(1,),storage_offset=0)
            # copy=True deliberately exercises transfer-copy semantics on CPU.
            self.copies[key]=base.to('cpu',copy=True)
        return ('offloaded',key,shape,tuple(tensor.stride()),tensor.storage_offset(),tensor.device)

    def unpack(self,packed):
        if packed[0]=='resident':return packed[1]
        _,key,shape,stride,offset,device=packed
        return self.copies[key].to(device).as_strided(shape,stride,storage_offset=offset)

    def report(self):
        kinds=sorted({r['kind'] for r in self.calls})
        return dict(pack_calls=len(self.calls),unique_storages=len(self.storages),
            total_pack_view_bytes=sum(r['view_bytes'] for r in self.calls),
            total_pack_storage_bytes=sum(r['storage_bytes'] for r in self.calls),
            unique_storage_bytes=sum(r['bytes'] for r in self.storages.values()),
            copied_unique_storages=len(self.copies),copied_unique_bytes=sum(t.numel()*t.element_size() for t in self.copies.values()),
            fp32_vocab_tensor_objects_alive_after_replay=sum(r() is not None for r in self.vocab_tensor_refs),
            liveness_caveat='Weakref object liveness is not allocator storage liveness; scalar selected-token views keep full-vocabulary storage during forward until final stack. Hook offload does not remove those Python-held views.',
            categories={kind:dict(pack_calls=sum(r['kind']==kind for r in self.calls),
                pack_view_bytes=sum(r['view_bytes'] for r in self.calls if r['kind']==kind),
                unique_storages=sum(r['kind']==kind for r in self.storages.values()),
                unique_bytes=sum(r['bytes'] for r in self.storages.values() if r['kind']==kind)) for kind in kinds},
            classification='Storage identity proves resident parameters; weight-shape and activation/KV categories are conservative heuristics, not tensor provenance proof')


def tiny_model():
    import torch
    from transformers import LlamaConfig,LlamaForCausalLM
    torch.set_num_threads(2);torch.manual_seed(20261003)
    config=LlamaConfig(vocab_size=128,hidden_size=64,intermediate_size=128,num_hidden_layers=2,
        num_attention_heads=4,num_key_value_heads=2,max_position_embeddings=512,attention_dropout=0.)
    config._attn_implementation='sdpa'
    model=LlamaForCausalLM(config).to(dtype=torch.bfloat16).eval().requires_grad_(False)
    model.model.layers[-1].to(dtype=torch.float32).requires_grad_(True)
    return model


def detach_cache_wrapper(model):
    """Intentionally WRONG causal-gradient control, isolated to this tiny census."""
    import torch
    class Detached(torch.nn.Module):
        def __init__(self):super().__init__();self.net=model
        def forward(self,**kwargs):
            result=self.net(**kwargs)
            for layer in result.past_key_values.layers:
                layer.keys=layer.keys.detach();layer.values=layer.values.detach()
            return result
    return Detached()


def replay(model,prompt,response,*,offload=False,detach=False):
    import torch
    model.zero_grad(set_to_none=True);census=Census(model,offload)
    net=detach_cache_wrapper(model) if detach else model
    with torch.autograd.graph.saved_tensors_hooks(census.pack,census.unpack):
        values=cached_token_logps(net,prompt,response,eos_token_ids=[127],seconds=20,max_context=512,
            context_factory=lambda:torch.autocast('cpu',dtype=torch.bfloat16))
    before=census.report();values.sum().backward()
    gradients={n:p.grad.detach().clone() for n,p in model.named_parameters() if p.requires_grad and p.grad is not None}
    selected={n for n,p in model.named_parameters() if p.requires_grad}
    if set(gradients)!=selected or len(gradients)!=9 or any(not torch.isfinite(v).all() for v in gradients.values()):
        raise ValueError('All nine actual final-layer gradients required')
    return values.detach().clone(),gradients,before


def experiment(lengths=(8,32,96),prompt_length=192):
    import torch
    import transformers
    if prompt_length<1 or max(lengths)+prompt_length>512:raise ValueError('Tiny bounded context required')
    model=tiny_model();initial={n:p.detach().clone() for n,p in model.named_parameters()}
    prompt=torch.arange(prompt_length)%126+1;reports=[];started=time.monotonic()
    for length in lengths:
        response=torch.cat((torch.arange(length-1)%126+1,torch.tensor([127])))
        values,grads,census=replay(model,prompt,response)
        off_values,off_grads,off_census=replay(model,prompt,response,offload=True)
        vocab_values,vocab_grads,vocab_census=replay(model,prompt,response,offload='vocab_only')
        negative_values,negative_grads,_=replay(model,prompt,response,detach=True)
        exact_values=torch.equal(values,off_values)
        exact_gradients=all(torch.equal(grads[n],off_grads[n]) for n in grads)
        negative_delta={n:float((grads[n]-negative_grads[n]).abs().max()) for n in grads}
        vocab_exact=torch.equal(values,vocab_values) and all(torch.equal(grads[n],vocab_grads[n]) for n in grads)
        vocab_category=vocab_census['categories'].get('fp32_vocab_vector',{})
        if (vocab_category.get('unique_storages')!=length or
            vocab_census['copied_unique_storages']!=length or
            vocab_census['copied_unique_bytes']!=length*model.config.vocab_size*4):
            raise ValueError('Exactly one unique FP32 LogSoftmaxBackward0 vocabulary storage per token required')
        if not exact_values or not exact_gradients or not vocab_exact or not any(negative_delta.values()):
            raise ValueError('CPU offload equivalence or causal-KV negative control failed')
        reports.append(dict(prompt_tokens=prompt_length,response_tokens=length,census=census,
            selective_unique_storage_cpu_copy=off_census,exact_token_logprobs=exact_values,
            vocab_only_cpu_copy=vocab_census,vocab_only_values_and_all_nine_gradients_exact=vocab_exact,
            all_nine_gradients_exact=exact_gradients,detached_cache_logprobs_exact=torch.equal(values,negative_values),
            detached_cache_gradient_max_delta=negative_delta))
    if any(not torch.equal(initial[n],p) for n,p in model.named_parameters()):raise ValueError('Unexpected weight update')
    return dict(rows=reports,seconds=time.monotonic()-started,torch_version=torch.__version__,
        transformers_version=transformers.__version__,device='cpu',optimizer_updates=0,
        scope='Tiny real Llama CPU diagnostic; copy=True tests exact storage/view reconstruction. CPU has no CUDA transfer timing, GPU allocator or headroom evidence.',
        recommendation='Probe only saved1D FP32 vocab_size LogSoftmaxBackward0 vectors on actual777-token response: nominal777*128256*4=398619648 bytes (380.15MiB). Scalar views still retain originals until cached replay returns, so this targets post-forward/backward pressure, not necessarily forward peak. Keep weights/casts/KV untouched and .03/.003,36GiB guards unchanged; no optimizer-memory claim.')


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();args.output.mkdir(parents=True,exist_ok=False)
    report=experiment()
    (args.output/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__=='__main__':main()
