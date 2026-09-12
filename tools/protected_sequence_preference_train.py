"""Bounded full-sequence pairwise objective primitives; no execution authority."""
import math

BUDGET = {"steps": 8, "pairs": 20, "lr": 1e-7, "margin": 0.25,
          "anchor_weight": 0.1, "max_seconds": 600, "trainable_tensors": 9}
PACKET_SHA = "cb137c525117ff42010514dad9ce16de0d793acc21fb5a583ae0902824bf8530"
PARENT_SHA = "b0399b51aed001051fe200751b3087fc008482ca9dfeb64eb12884f71eee3bb6"


def response_mean_logprob(logits, tokens, prompt_length):
    """Mean response log-probability, including EOS, excluding the prompt."""
    import torch
    import torch.nn.functional as F
    if logits.ndim != 3 or tokens.ndim != 2 or logits.shape[:2] != tokens.shape:
        raise ValueError("aligned batch logits and token IDs required")
    if type(prompt_length) is not int or not 0 < prompt_length < tokens.shape[1]:
        raise ValueError("nonempty prompt and response required")
    # Token i is predicted by logits at i-1.  Include every response token.
    scores = F.log_softmax(logits[:, prompt_length - 1:-1].float(), dim=-1)
    targets = tokens[:, prompt_length:]
    selected = scores.gather(-1, targets.unsqueeze(-1)).squeeze(-1)
    if selected.numel() == 0 or not bool(torch.isfinite(selected).all()):
        raise ValueError("finite response token scores required")
    return selected.mean(dim=-1)


def pairwise_loss(positive_logprob, negative_logprob, margin=0.25, anchor_weight=0.1):
    """Length-normalized ranking plus positive NLL anchor.

    Normalization prevents longer malformed rollouts from winning merely by
    accumulating more negative log-probability; the anchor prevents lowering
    both sequences from satisfying the ranking objective.
    """
    import torch
    import torch.nn.functional as F
    if positive_logprob.shape != negative_logprob.shape or positive_logprob.numel() == 0:
        raise ValueError("matched nonempty pair scores required")
    if not all(math.isfinite(float(x)) for x in (margin, anchor_weight)) or margin <= 0 or anchor_weight <= 0:
        raise ValueError("positive finite margin and anchor required")
    gap = positive_logprob - negative_logprob
    loss = F.softplus(margin - gap) + anchor_weight * (-positive_logprob)
    if not bool(torch.isfinite(loss).all()):
        raise ValueError("finite pairwise loss required")
    return loss.mean(), gap.mean()


def score_sequence(net, prompt, response, *, device="cpu", context=None):
    """Run one complete prompt+response sequence without mutating parameters."""
    import torch
    if not prompt or not response:
        raise ValueError("complete prompt and response required")
    ids = torch.tensor([prompt + response], dtype=torch.long, device=device)
    context = context or torch.enable_grad
    with context():
        output = net(input_ids=ids, attention_mask=torch.ones_like(ids), use_cache=False)
    return response_mean_logprob(output.logits, ids, len(prompt))


def objective(net, pair, *, device="cpu", context=None):
    """Two complete forwards; suitable for a zero-update gradient preflight."""
    positive = score_sequence(net, pair["prompt_tokens"], pair["positive_tokens"],
                              device=device, context=context)
    negative = score_sequence(net, pair["prompt_tokens"], pair["negative_tokens"],
                              device=device, context=context)
    return pairwise_loss(positive, negative, BUDGET["margin"], BUDGET["anchor_weight"])
