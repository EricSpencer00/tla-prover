"""Differentiable forced-token replay of the exact incremental sampling calls.

This is a candidate scoring primitive, not an on-policy or GPU certificate.
No cache tensors are detached: later token losses must reach earlier trainable
keys/values. The caller owns policy identity, memory guards and hard watchdogs.
"""
from contextlib import nullcontext
import math
import time


def cached_token_logps(model, input_token_ids, response_token_ids, *, eos_token_ids,
                      seconds, max_context=8192, context_factory=nullcontext,
                      clock=time.monotonic):
    """Score actual terminal-EOS response IDs, respecting caller gradient mode.

    Calls match sample_tokens: full unpadded prompt, then each previous response
    token, with a growing full attention mask and use_cache=True. No EOS is
    appended and no incomplete prefix is admitted. Each deadline check is soft;
    a long kernel/backward requires the caller's process-level watchdog. Normal
    grad-enabled use requires a differentiable result; torch.no_grad() supports
    independent numerical replay without allocating training graphs.
    One fresh outer precision context shares autocast weight copies within this
    invocation only. It must not span other calls or optimizer updates: casts
    created under no_grad must never be reused by a later gradient invocation.
    """
    import torch
    for name, ids in (('prompt', input_token_ids), ('response', response_token_ids)):
        if (not isinstance(ids, torch.Tensor) or ids.ndim != 1 or
                ids.dtype != torch.long or not len(ids) or bool((ids < 0).any())):
            raise ValueError('Nonempty one-dimensional long ' + name + ' IDs required')
    if response_token_ids.device != input_token_ids.device:
        raise ValueError('Prompt and response device must match')
    if (not isinstance(eos_token_ids, (list, tuple)) or not eos_token_ids or
            any(type(i) is not int or i < 0 for i in eos_token_ids) or
            len(set(eos_token_ids)) != len(eos_token_ids)):
        raise ValueError('Explicit distinct model EOS IDs required')
    response = response_token_ids.tolist()
    if response[-1] not in eos_token_ids or any(i in eos_token_ids for i in response[:-1]):
        raise ValueError('Actual sampled terminal EOS required; no synthetic EOS')
    if (type(max_context) is not int or not 1 <= max_context <= 8192 or
            len(response) > 3072 or len(input_token_ids) + len(response) > max_context):
        raise ValueError('Actual input/output context budget exceeded')
    if type(seconds) not in (int, float) or not math.isfinite(seconds) or seconds <= 0:
        raise ValueError('Positive finite wall budget required')
    if not callable(context_factory) or not callable(clock):
        raise ValueError('Context and clock factories required')
    modes = [(module, module.training) for module in model.modules()]
    grad_enabled = torch.is_grad_enabled()
    started = clock()
    current = input_token_ids.unsqueeze(0)
    mask = torch.ones_like(current)
    cache = None
    selected = []

    def deadline():
        if clock() - started >= seconds:
            raise TimeoutError('Cached scoring wall budget exceeded; no partial score admitted')

    try:
        model.eval()
        with context_factory():
            for index, ident in enumerate(response):
                deadline()
                with context_factory():
                    output = model(input_ids=current, attention_mask=mask,
                                   past_key_values=cache, use_cache=True)
                deadline()
                logits = output.logits
                if (not isinstance(logits, torch.Tensor) or logits.ndim != 3 or
                        logits.shape[:2] != current.shape or
                        logits.device != input_token_ids.device or not logits.is_floating_point()):
                    raise ValueError('Invalid causal model logits')
                scores = logits[0, -1].float()
                if (not bool(torch.isfinite(scores).all()) or
                        any(i >= scores.numel() for i in [ident, *eos_token_ids])):
                    raise ValueError('Finite full-vocabulary logits and in-vocabulary IDs required')
                logps = scores.log_softmax(-1)
                if not bool(torch.isfinite(logps).all()):
                    raise ValueError('Nonfinite normalized scoring distribution')
                selected.append(logps[ident])
                deadline()
                if index + 1 < len(response):
                    cache = output.past_key_values
                    if cache is None:
                        raise ValueError('Differentiable incremental KV cache required')
                    current = response_token_ids[index:index + 1].reshape(1, 1)
                    mask = torch.cat((mask, torch.ones((1, 1), dtype=mask.dtype,
                                                      device=mask.device)), dim=1)
            result = torch.stack(selected)
            if grad_enabled and not result.requires_grad:
                raise ValueError('Differentiable policy logits required')
            deadline()
            return result
    finally:
        for module, training in modes:
            module.training = training
