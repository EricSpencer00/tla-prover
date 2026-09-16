"""Exact temperature1 categorical sampling without generate() defaults.

No top-k, nucleus, beams, logits processors, forced EOS or weight updates.
The caller supplies the frozen policy and matching device RNG. For the existing
mixed CUDA profile pass context_factory=lambda: torch.autocast('cuda',
dtype=torch.bfloat16). Model/optimizer identity attestation belongs to caller.
"""
from contextlib import nullcontext
import math
import time


def same_rng_device(generator_device,input_device,*,current_cuda_index=None):
    """Resolve only implicit CUDA ordinals; CPU/GPU and explicit ordinals differ.

    A CUDA Generator may report torch.device('cuda') while a tensor reports
    torch.device('cuda:0'). The omitted ordinal denotes the current CUDA device,
    not an arbitrary matching GPU. Injection supports hardware-free tests.
    """
    import torch
    left=torch.device(generator_device);right=torch.device(input_device)
    if left.type!=right.type:return False
    if left.type!='cuda':return left==right
    if left.index is not None and right.index is not None:return left.index==right.index
    current=torch.cuda.current_device() if current_cuda_index is None else current_cuda_index
    if type(current) is not int or current<0:raise ValueError('Valid current CUDA ordinal required')
    return (current if left.index is None else left.index)==(current if right.index is None else right.index)


def sample_tokens(model,input_token_ids,*,generator,eos_token_ids,max_new_tokens,
                  seconds,max_context=8192,context_factory=nullcontext,clock=time.monotonic):
    """Return actual sampled IDs/logps; incomplete prefixes are never completed.

    Input is one unpadded prompt on the model device. Incremental cache calls
    receive only the last sampled token and the complete attention mask.
    Deadline is checked before/after each model forward, not a preemptive kernel
    deadline: caller must provide the existing process watchdog for hard bounds.
    """
    import torch
    if (not isinstance(input_token_ids,torch.Tensor) or input_token_ids.ndim!=1 or
            input_token_ids.dtype!=torch.long or not len(input_token_ids) or
            bool((input_token_ids<0).any())):
        raise ValueError('Nonempty unpadded one-dimensional long prompt IDs required')
    if (type(max_new_tokens) is not int or not 1<=max_new_tokens<=3072 or
            type(max_context) is not int or not 1<=max_context<=8192 or
            len(input_token_ids)+max_new_tokens>max_context):
        raise ValueError('Full declared input/output context budget required')
    if type(seconds) not in (int,float) or not math.isfinite(seconds) or seconds<=0:
        raise ValueError('Positive finite wall budget required')
    if (not isinstance(eos_token_ids,(list,tuple)) or not eos_token_ids or
            any(type(i) is not int or i<0 for i in eos_token_ids) or len(set(eos_token_ids))!=len(eos_token_ids)):
        raise ValueError('Explicit distinct model EOS IDs required')
    if not isinstance(generator,torch.Generator) or not same_rng_device(generator.device,input_token_ids.device):
        raise ValueError('Explicit RNG on prompt device required')
    if not callable(context_factory) or not callable(clock):raise ValueError('Context and clock factories required')
    modes=[(module,module.training) for module in model.modules()]
    started=clock();tokens=[];logps=[];entropies=[];cache=None
    current=input_token_ids.unsqueeze(0);mask=torch.ones_like(current)
    finish='token_limit';forward_calls=0
    try:
        model.eval()
        with torch.no_grad():
            for _ in range(max_new_tokens):
                if clock()-started>=seconds:finish='time_limit';break
                with context_factory():
                    output=model(input_ids=current,attention_mask=mask,past_key_values=cache,use_cache=True)
                forward_calls+=1
                logits=output.logits
                if (not isinstance(logits,torch.Tensor) or logits.ndim!=3 or logits.shape[0]!=1 or
                        logits.shape[1]!=current.shape[1] or logits.device!=input_token_ids.device or
                        not logits.is_floating_point()):raise ValueError('Invalid causal model logits')
                scores=logits[0,-1].float()
                if not bool(torch.isfinite(scores).all()) or any(i>=scores.numel() for i in eos_token_ids):
                    raise ValueError('Finite full-vocabulary logits and in-vocabulary EOS required')
                # Float32 normalization exactly matches the training objective.
                log_probs=scores.log_softmax(-1);probabilities=log_probs.exp()
                if not bool(torch.isfinite(log_probs).all()) or not bool(torch.isfinite(probabilities).all()):
                    raise ValueError('Nonfinite normalized sampling distribution')
                if clock()-started>=seconds:finish='time_limit';break
                token=torch.multinomial(probabilities,1,replacement=True,generator=generator)
                ident=int(token.item())
                tokens.append(ident);logps.append(float(log_probs[ident].item()))
                entropies.append(float(-(probabilities*log_probs).sum().item()))
                # item()/entropy can synchronize CUDA after the earlier check.
                # Preserve sampled bytes, but do not admit an over-budget EOS.
                if clock()-started>=seconds:finish='time_limit';break
                if ident in eos_token_ids:finish='eos';break
                cache=output.past_key_values
                if cache is None:raise ValueError('Incremental KV cache required')
                current=token.reshape(1,1)
                mask=torch.cat((mask,torch.ones((1,1),dtype=mask.dtype,device=mask.device)),dim=1)
    finally:
        # Restore even deliberately mixed submodule training flags exactly.
        for module,training in modes:module.training=training
    return dict(token_ids=tokens,selected_token_logprobs=logps,
        sequence_logprob=sum(logps),token_entropies=entropies,finish_reason=finish,
        eos_reached=bool(tokens and tokens[-1] in eos_token_ids),
        deadline_exceeded=finish=='time_limit',hit_token_limit=len(tokens)==max_new_tokens,
        output_tokens=len(tokens),forward_calls=forward_calls,temperature=1.0,
        do_sample=True,distribution='full_vocabulary_categorical',elapsed_seconds=clock()-started)
