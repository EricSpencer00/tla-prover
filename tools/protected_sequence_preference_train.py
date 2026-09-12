"""Bounded full-sequence pairwise objective and zero-update CUDA preflight."""
import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import protected_checkpoint_preflight as checkpoint
from tools import protected_sequence_objective_contract as contract

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


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(8 * 1024**2), b""):
            h.update(chunk)
    return h.hexdigest()


def runtime_preflight(packet_path, model_path, checkpoint_path, output):
    import torch
    import transformers
    packet_path, model_path, checkpoint_path, output = map(Path, (packet_path, model_path, checkpoint_path, output))
    if output.exists() or file_sha(packet_path) != PACKET_SHA or file_sha(checkpoint_path) != PARENT_SHA:
        raise ValueError("append-only output and exact packet/checkpoint required")
    value = contract.load(packet_path)
    if len(value["pairs"]) != BUDGET["pairs"]:
        raise ValueError("exact 20-pair packet required")
    files = checkpoint.model_files(model_path)
    saved = torch.load(checkpoint_path, map_location="cpu", weights_only=False)
    if (saved.get("config", {}).get("model_files") != files or
            saved.get("config", {}).get("dtype_profile") != checkpoint.PROFILE):
        raise ValueError("checkpoint model lineage mismatch")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    net = transformers.AutoModelForCausalLM.from_pretrained(
        model_path, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa").to("cuda").eval().requires_grad_(False)
    net.model.layers[-1].to(torch.float32)
    selected = {name: parameter for name, parameter in net.named_parameters()
                if name.startswith("model.layers.31.")}
    if len(selected) != BUDGET["trainable_tensors"]:
        raise ValueError("exact nine final-layer tensors required")
    checkpoint.restore_exact(selected, saved)
    initial = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    for parameter in selected.values():
        parameter.requires_grad_(True)
    pair = max(value["pairs"], key=lambda item: max(
        len(item["prompt_tokens"]) + len(item["positive_tokens"]),
        len(item["prompt_tokens"]) + len(item["negative_tokens"])))
    torch.cuda.reset_peak_memory_stats()
    context = lambda: torch.autograd.graph.save_on_cpu(pin_memory=False)
    with torch.autocast("cuda", dtype=torch.bfloat16):
        loss, gap = objective(net, pair, device="cuda", context=context)
    loss.backward()
    gradients = {name: float(parameter.grad.detach().float().norm())
                 for name, parameter in selected.items() if parameter.grad is not None}
    unchanged = all(torch.equal(parameter.detach().cpu(), initial[name])
                    for name, parameter in selected.items())
    if (set(gradients) != set(selected) or not all(math.isfinite(v) for v in gradients.values()) or
            not any(v > 0 for v in gradients.values()) or not unchanged):
        raise ValueError("zero-update gradient or parameter-drift guard failed")
    receipt = {
        "kind": "sequence_pairwise_zero_update_cuda_preflight_v1", "complete": True,
        "packet_sha256": PACKET_SHA, "checkpoint_sha256": PARENT_SHA,
        "source_id": pair["source_id"], "positive_full_tokens": len(pair["prompt_tokens"]) + len(pair["positive_tokens"]),
        "negative_full_tokens": len(pair["prompt_tokens"]) + len(pair["negative_tokens"]),
        "loss": float(loss.detach()), "gap": float(gap.detach()), "gradient_norms": gradients,
        "peak_cuda_allocated": torch.cuda.max_memory_allocated(),
        "peak_cuda_reserved": torch.cuda.max_memory_reserved(), "parameters_unchanged": True,
        "optimizer_updates": 0, "model_files": files, "gate_claim": False,
    }
    output.mkdir(parents=True)
    (output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("preflight",))
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    runtime_preflight(args.packet, args.model, args.checkpoint, args.output)


if __name__ == "__main__":
    main()
