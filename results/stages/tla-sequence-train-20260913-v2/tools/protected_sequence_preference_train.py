"""Bounded full-sequence pairwise objective and zero-update CUDA preflight."""
import argparse
from contextlib import nullcontext
import hashlib
import json
import math
from pathlib import Path
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import protected_checkpoint_preflight as checkpoint
from tools import protected_sequence_objective_contract as contract

BUDGET = {"steps": 8, "pairs": 20, "lr": 1e-7, "margin": 0.25,
          "anchor_weight": 0.1, "max_seconds": 600, "trainable_tensors": 9}
PACKET_SHA = "cb137c525117ff42010514dad9ce16de0d793acc21fb5a583ae0902824bf8530"
PARENT_SHA = "b0399b51aed001051fe200751b3087fc008482ca9dfeb64eb12884f71eee3bb6"
PLAN_SHA = "ae1c5bb5314b4e55338e68ad20d858a3307714d46c43998c763c64555a7cfa1d"


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


def load_training_plan(plan_path, packet):
    """Admit only the frozen, disjoint 8/12 non-protected split."""
    plan = json.loads(Path(plan_path).read_text())
    claimed = plan.pop("plan_sha256", None)
    if claimed != contract.digest(plan):
        raise ValueError("training plan identity mismatch")
    expected_budget = {
        "optimizer_updates": BUDGET["steps"], "learning_rate": BUDGET["lr"],
        "margin": BUDGET["margin"], "positive_nll_anchor_weight": BUDGET["anchor_weight"],
        "max_seconds": BUDGET["max_seconds"], "trainable_tensors": BUDGET["trainable_tensors"],
    }
    if (plan.get("kind") != "protected_sequence_training_plan_v1" or
            plan.get("budget") != expected_budget or
            plan.get("protected_training") is not False or
            plan.get("protected_model_selection") is not False or
            plan.get("internal_holdout_use") != "diagnostic_only_no_gate_credit" or
            plan.get("gate_claim") is not False):
        raise ValueError("exact leakage-resistant training plan required")
    if plan.get("acceptance_evaluation") != packet["evaluation"] or plan.get("retention") != packet["retention"]:
        raise ValueError("frozen acceptance and retention rules required")
    pairs = {pair["source_id"]: pair for pair in packet["pairs"]}
    train = plan.get("train_source_ids")
    holdout = plan.get("holdout_source_ids")
    if (not isinstance(train, list) or not isinstance(holdout, list) or len(train) != BUDGET["steps"] or
            len(holdout) != BUDGET["pairs"] - BUDGET["steps"] or len(set(train)) != len(train) or
            len(set(holdout)) != len(holdout) or set(train) & set(holdout) or set(train) | set(holdout) != set(pairs)):
        raise ValueError("exact disjoint full-packet split required")
    return plan, [pairs[source_id] for source_id in train], [pairs[source_id] for source_id in holdout]


def mean_gap(net, pairs, *, device, context, forward_context=None):
    """Diagnostic-only holdout measurement; never a protected gate."""
    values = []
    forward_context = forward_context or nullcontext
    for pair in pairs:
        with forward_context():
            _, gap = objective(net, pair, device=device, context=context)
        values.append(float(gap.detach()))
    if not values or not all(math.isfinite(value) for value in values):
        raise ValueError("finite nonempty holdout gaps required")
    return sum(values) / len(values)


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


def runtime_train(packet_path, plan_path, model_path, checkpoint_path, output):
    """Run exactly eight non-protected updates and write an append-only child."""
    import torch
    import transformers
    packet_path, plan_path, model_path, checkpoint_path, output = map(
        Path, (packet_path, plan_path, model_path, checkpoint_path, output))
    if (output.exists() or file_sha(packet_path) != PACKET_SHA or
            file_sha(plan_path) != PLAN_SHA or file_sha(checkpoint_path) != PARENT_SHA):
        raise ValueError("append-only output and exact packet/plan/checkpoint required")
    value = contract.load(packet_path)
    plan, train_pairs, holdout_pairs = load_training_plan(plan_path, value)
    if len(value["pairs"]) != BUDGET["pairs"]:
        raise ValueError("exact 20-pair packet required")
    files = checkpoint.model_files(model_path)
    saved = torch.load(checkpoint_path, map_location="cpu", weights_only=False)
    if (saved.get("config", {}).get("model_files") != files or
            saved.get("config", {}).get("dtype_profile") != checkpoint.PROFILE):
        raise ValueError("checkpoint model lineage mismatch")
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    random.seed(0)
    torch.manual_seed(0)
    torch.cuda.manual_seed_all(0)
    torch.backends.cuda.matmul.allow_tf32 = False
    started = time.monotonic()
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
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET["lr"], weight_decay=0.0, foreach=False)
    torch.cuda.reset_peak_memory_stats()
    no_grad = torch.no_grad
    autocast = lambda: torch.autocast("cuda", dtype=torch.bfloat16)
    holdout_before = mean_gap(net, holdout_pairs, device="cuda", context=no_grad,
                              forward_context=autocast)
    rows = []
    offload = lambda: torch.autograd.graph.save_on_cpu(pin_memory=False)
    for step, pair in enumerate(train_pairs, start=1):
        if time.monotonic() - started >= BUDGET["max_seconds"]:
            raise TimeoutError("training time budget exhausted before complete schedule")
        optimizer.zero_grad(set_to_none=True)
        with torch.autocast("cuda", dtype=torch.bfloat16):
            loss, gap = objective(net, pair, device="cuda", context=offload)
        loss.backward()
        norm = torch.nn.utils.clip_grad_norm_(selected.values(), 1.0, error_if_nonfinite=True)
        optimizer.step()
        if not all(bool(torch.isfinite(parameter).all()) for parameter in selected.values()):
            raise ValueError("nonfinite trained parameter")
        rows.append({"step": step, "source_id": pair["source_id"], "loss": float(loss.detach()),
                     "gap": float(gap.detach()), "gradient_norm": float(norm)})
    holdout_after = mean_gap(net, holdout_pairs, device="cuda", context=no_grad,
                             forward_context=autocast)
    state = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    delta = math.sqrt(sum(float((state[name] - initial[name]).double().square().sum()) for name in state))
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError("actual parent-child parameter change required")
    output.mkdir(parents=True)
    config = {"packet_sha256": PACKET_SHA, "plan_file_sha256": PLAN_SHA,
              "checkpoint_sha256": PARENT_SHA, "model_files": files,
              "plan_sha256": plan["plan_sha256"], "train_source_ids": plan["train_source_ids"],
              "holdout_source_ids": plan["holdout_source_ids"], "budget": plan["budget"],
              "protected_training": False, "protected_model_selection": False, "gate_claim": False}
    child = {"trainable_state": state, "optimizer": optimizer.state_dict(), "config": config,
             "metrics": rows, "torch_rng_state": torch.get_rng_state(),
             "python_rng_state": random.getstate(), "cuda_rng_state": torch.cuda.get_rng_state_all()}
    child_path = output / "policy_optimizer.pt"
    torch.save(child, child_path)
    with torch.no_grad():
        for parameter in selected.values():
            parameter.zero_()
        checkpoint.restore_exact(selected, child)
    reloaded = all(torch.equal(parameter.detach().cpu(), state[name]) for name, parameter in selected.items())
    if not reloaded:
        raise ValueError("child checkpoint exact reload failed")
    receipt = {
        "kind": "sequence_pairwise_true_update_cuda_train_v1", "complete": True,
        "packet_sha256": PACKET_SHA, "plan_file_sha256": PLAN_SHA, "plan_sha256": plan["plan_sha256"],
        "parent_checkpoint_sha256": PARENT_SHA, "child_checkpoint_sha256": file_sha(child_path),
        "optimizer_updates": len(rows), "train_source_ids": plan["train_source_ids"],
        "holdout_source_ids": plan["holdout_source_ids"], "holdout_gap_before": holdout_before,
        "holdout_gap_after": holdout_after, "parameter_delta_l2": delta,
        "reload_tensors_exact": reloaded, "peak_cuda_allocated": torch.cuda.max_memory_allocated(),
        "peak_cuda_reserved": torch.cuda.max_memory_reserved(), "elapsed_seconds": time.monotonic() - started,
        "protected_training": False, "protected_model_selection": False, "gate_claim": False,
    }
    (output / "train_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    (output / "steps.json").write_text(json.dumps(rows, indent=2) + "\n")
    print(json.dumps(receipt, sort_keys=True))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("preflight", "train"))
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--plan", type=Path)
    parser.add_argument("--model", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.mode == "preflight":
        runtime_preflight(args.packet, args.model, args.checkpoint, args.output)
    else:
        if args.plan is None:
            raise ValueError("plan is required for true-update training")
        runtime_train(args.packet, args.plan, args.model, args.checkpoint, args.output)


if __name__ == "__main__":
    main()
