#!/usr/bin/env python3
"""Train a bounded train-only contrastive selector from strict teacher anchors.

This is deterministic supervised ranking over one strict-certified TRAIN
anchor and answer-free hard negatives per task.  It does not sample verifier
rewards, read DEVELOPMENT targets, or make a proof-quality claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

MANIFEST_SHA256 = "c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344"
PACKET_SHA256 = "d6437a577cdee66efdeacb9b818463853a8d4aacfaf987561532693bccc147a0"
PARENT_SHA256 = "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"


def sha(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def validate_packet(packet: object) -> list[dict]:
    """Fail closed on the exact 17-row TRAIN-only teacher contract."""
    if not isinstance(packet, list) or len(packet) != 17:
        raise ValueError("exact17 TRAIN rows required")
    ids = set()
    for row in packet:
        if not isinstance(row, dict) or not isinstance(row.get("id"), str):
            raise ValueError("malformed teacher row")
        if row["id"] in ids or row["id"].startswith("crdt-"):
            raise ValueError("duplicate or DEVELOPMENT-style row id")
        ids.add(row["id"])
        if row.get("teacher_candidate_index") != 0:
            raise ValueError("teacher anchor must be candidate zero")
        if row.get("development_target_exported") is not False:
            raise ValueError("DEVELOPMENT target export must be false")
        if row.get("candidate_contract") != "strict_teacher_anchor_plus_answer_free_hard_negatives":
            raise ValueError("unexpected candidate contract")
        if row.get("context", {}).get("teacher_anchor_train_only") is not True:
            raise ValueError("train-only teacher attestation missing")
        if row.get("context", {}).get("reference_fragment_used") is not False:
            raise ValueError("retrieval context must attest no reference use")
        candidates = row.get("candidates")
        if not isinstance(candidates, list) or len(candidates) != 8:
            raise ValueError("exactly one teacher plus seven negatives required")
        if any(not isinstance(candidate, str) or not candidate.strip()
               for candidate in candidates):
            raise ValueError("candidate language must contain nonempty proof text")
        if any(key in row for key in ("reference_fragment", "response", "answer", "proof_body",
                                      "reward", "feedback", "repair")):
            raise ValueError("answer or verifier signal leaked into teacher row")
        if not isinstance(row.get("prompt"), str) or "<PROOF_HOLE>" not in row["prompt"]:
            raise ValueError("teacher prompt must expose the proof hole")
    return packet


def contrastive_loss(scores, target: int = 0, temperature: float = 1.0):
    """Cross-entropy for the teacher index; no verifier reward is involved."""
    import torch
    if scores.ndim != 1 or len(scores) < 2 or not 0 <= target < len(scores):
        raise ValueError("one-dimensional multi-candidate score vector required")
    if temperature <= 0:
        raise ValueError("positive temperature required")
    scaled = scores / temperature
    return -scaled[target] + torch.logsumexp(scaled, dim=0)


def centered_score_coefficients(scores, target: int = 0, temperature: float = 1.0):
    """Return exact d(loss)/d(score) coefficients for bounded recomputation.

    Candidate forward graphs are recomputed one at a time so an 8B model does
    not retain eight long-sequence autograd graphs simultaneously.  The
    coefficients are computed from the same pre-update score vector, making
    the accumulated backward pass exactly the contrastive loss gradient.
    """
    import torch
    if scores.ndim != 1 or not 0 <= target < len(scores) or temperature <= 0:
        raise ValueError("invalid contrastive score vector")
    probabilities = torch.softmax(scores / temperature, dim=0)
    coefficients = probabilities / temperature
    coefficients = coefficients.clone()
    coefficients[target] -= 1.0 / temperature
    return probabilities, coefficients


def resolve_runtime_path(name: str) -> Path:
    path = Path(name)
    return path if path.is_absolute() else ROOT / path


def restore_trainable(trainable: dict, saved: dict) -> None:
    import torch
    state = saved["trainable_state"]
    if set(state) != set(trainable):
        raise ValueError("checkpoint trainable parameter coverage mismatch")
    for name, parameter in trainable.items():
        if state[name].shape != parameter.shape or state[name].dtype != parameter.dtype:
            raise ValueError(f"checkpoint shape/dtype mismatch: {name}")
    with torch.no_grad():
        for name, parameter in trainable.items():
            parameter.copy_(state[name].to(parameter.device))


def verify_hashes(args, packet_raw: bytes) -> None:
    if sha(packet_raw) != args.expected_packet_sha256:
        raise ValueError("packet hash mismatch")
    if args.expected_manifest_sha256 and sha(args.manifest.read_bytes()) != args.expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    if args.expected_parent_sha256 and args.resume and sha(args.resume.read_bytes()) != args.expected_parent_sha256:
        raise ValueError("parent checkpoint hash mismatch")


def preflight(packet_path: Path, output: Path, expected_packet: str) -> dict:
    raw = packet_path.read_bytes()
    if sha(raw) != expected_packet:
        raise ValueError("packet hash mismatch")
    packet = validate_packet(json.loads(raw))
    output.mkdir(parents=True, exist_ok=False)
    summary = {
        "schema": 1,
        "kind": "train_only_teacher_anchor_contrastive_preflight",
        "packet_sha256": sha(raw),
        "train_tasks": len(packet),
        "candidates_per_task": sorted({len(row["candidates"]) for row in packet}),
        "teacher_anchor_count": len(packet),
        "negative_candidate_count": len(packet) * 7,
        "development_targets_exported": False,
        "development_reference_bytes_exported": False,
        "verifier_feedback_used": False,
        "reward_signal_used": False,
        "model_loaded": False,
        "cuda_touched": False,
        "optimizer_updates": 0,
        "quality_claim": False,
        "proof_claim": False,
        "gate_claim": False,
    }
    dump(output / "summary.json", summary)
    return summary


def worker(args) -> None:
    from tools.proof_candidate_rank import encode_candidate
    from tools.proof_candidate_rl import differentiable_mean_logp

    started = time.monotonic()
    packet_raw = args.packet.read_bytes()
    verify_hashes(args, packet_raw)
    packet = validate_packet(json.loads(packet_raw))
    if args.output.exists():
        raise ValueError("output already exists")
    args.output.mkdir(parents=True)
    (args.output / "packet.json").write_bytes(packet_raw)

    os.environ.update(HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1", TOKENIZERS_PARALLELISM="false")
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(args.seed)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model_path, local_files_only=True)
    encoded = [[encode_candidate(tokenizer, row["prompt"], candidate, args.max_tokens)
                for candidate in row["candidates"]] for row in packet]
    dump(args.output / "encodings.json", encoded)

    net = transformers.AutoModelForCausalLM.from_pretrained(
        args.model_path, local_files_only=True, torch_dtype=torch.float32).to(args.device).eval()
    net.requires_grad_(False)
    net.model.layers[-1].requires_grad_(True)
    trainable = {name: parameter for name, parameter in net.named_parameters()
                 if parameter.requires_grad}
    model_files = {path.name: sha(path.read_bytes()) for path in args.model_path.iterdir()
                   if path.is_file() and path.suffix in {".json", ".safetensors"}}
    saved_parent = torch.load(args.resume, map_location="cpu", weights_only=False)
    if saved_parent["config"]["model_files"] != model_files:
        raise ValueError("parent base-model identity mismatch")
    restore_trainable(trainable, saved_parent)
    initial = {name: parameter.detach().cpu().clone() for name, parameter in trainable.items()}
    optimizer = torch.optim.AdamW(trainable.values(), lr=args.lr, weight_decay=0)
    config = {
        "algorithm": "deterministic train-only contrastive teacher-anchor selector",
        "loss": "cross_entropy over mean conditional response logp; candidate zero is strict TRAIN teacher",
        "manifest_sha256": args.expected_manifest_sha256,
        "packet_sha256": sha(packet_raw),
        "parent_sha256": sha(args.resume.read_bytes()),
        "model_files": model_files,
        "trainable_names": list(trainable),
        "trainable_parameters": sum(parameter.numel() for parameter in trainable.values()),
        "temperature": args.temperature,
        "lr": args.lr,
        "seed": args.seed,
        "torch_version": torch.__version__,
        "transformers_version": transformers.__version__,
        "development_targets_exported": False,
        "reward_signal_used": False,
        "verifier_feedback_used": False,
    }
    dump(args.output / "runtime-config.json", config)

    def score(encoding):
        ids = torch.tensor([encoding["input_ids"]], device=args.device)
        return differentiable_mean_logp(net(input_ids=ids, use_cache=False).logits[0], encoding["labels"])

    metrics = []
    with (args.output / "steps.jsonl").open("x") as ledger:
        for step in range(args.steps):
            if time.monotonic() - started >= args.seconds - 60:
                break
            task_index = step % len(packet)
            row = packet[task_index]
            candidates = encoded[task_index]
            with torch.inference_mode():
                scores = torch.tensor([float(score(encoding)) for encoding in candidates],
                                      dtype=torch.float64)
            if not torch.isfinite(scores).all():
                raise ValueError("nonfinite candidate score")
            probabilities, coefficients = centered_score_coefficients(
                scores, target=row["teacher_candidate_index"], temperature=args.temperature)
            loss_value = float(contrastive_loss(scores, row["teacher_candidate_index"], args.temperature))
            teacher_score = float(scores[0])
            best_negative = float(scores[1:].max())
            optimizer.zero_grad(set_to_none=True)
            for index, encoding in enumerate(candidates):
                coefficient = float(coefficients[index])
                if coefficient:
                    (score(encoding) * coefficient).backward()
            norm = torch.nn.utils.clip_grad_norm_(trainable.values(), 1.0, error_if_nonfinite=True)
            optimizer.step()
            metric = {
                "step": step + 1,
                "task": row["id"],
                "loss": loss_value,
                "teacher_mean_logp": teacher_score,
                "best_negative_mean_logp": best_negative,
                "teacher_margin": teacher_score - best_negative,
                "probabilities": probabilities.tolist(),
                "gradient_norm": float(norm),
                "updated": True,
                "elapsed_seconds": time.monotonic() - started,
            }
            metrics.append(metric)
            ledger.write(json.dumps(metric) + "\n")
            ledger.flush()
            print(json.dumps(metric), flush=True)

    if len(metrics) != args.steps:
        raise RuntimeError("contrastive run stopped before the fixed update count")
    state = {name: parameter.detach().cpu().clone() for name, parameter in trainable.items()}
    checkpoint = args.output / "policy_optimizer.pt"
    # The optimizer state is not needed to consume this child as a parent and
    # more than doubles the artifact size.  Save only the exact trainable
    # tensors, first on node-local scratch, then copy atomically to home.  This
    # avoids the Polaris home-filesystem zip-writer failure seen after update
    # completion while retaining exact tensor/logit reload evidence.
    payload = {"trainable_state": state, "config": config, "metrics": metrics,
               "torch_rng_state": torch.get_rng_state(),
               "checkpoint_format": "weights_only_trainable_state_v2"}
    scratch_root = Path(os.environ.get("TMPDIR", "/tmp"))
    scratch_root.mkdir(parents=True, exist_ok=True)
    scratch = scratch_root / f"tla-teacher-contrastive-{os.getpid()}.pt"
    checkpoint_tmp = checkpoint.with_name(checkpoint.name + ".tmp")
    try:
        torch.save(payload, scratch)
        shutil.copyfile(scratch, checkpoint_tmp)
        with checkpoint_tmp.open("rb") as stream:
            os.fsync(stream.fileno())
        os.replace(checkpoint_tmp, checkpoint)
    finally:
        scratch.unlink(missing_ok=True)
        checkpoint_tmp.unlink(missing_ok=True)
    with torch.no_grad():
        probe = torch.tensor([encoded[0][0]["input_ids"]], device=args.device)
        before = net(input_ids=probe, use_cache=False).logits[:, -1].cpu().clone()
        for parameter in trainable.values():
            parameter.zero_()
        restore_trainable(trainable, torch.load(checkpoint, map_location="cpu", weights_only=False))
        restored_exact = all(torch.equal(parameter.detach().cpu(), state[name])
                             for name, parameter in trainable.items())
        after = net(input_ids=probe, use_cache=False).logits[:, -1].cpu()
    if not restored_exact or not torch.equal(before, after):
        raise RuntimeError("saved checkpoint did not reproduce exact tensors and probe logits")
    delta = sum(float((state[name] - initial[name]).double().square().sum()) for name in state) ** 0.5
    dump(args.output / "summary.json", {
        "schema": 1,
        "updates": len(metrics),
        "requested_updates": args.steps,
        "train_tasks": len(packet),
        "teacher_anchor_tasks": len(packet),
        "negative_candidates": len(packet) * 7,
        "parameter_delta_l2": delta,
        "checkpoint_sha256": sha(checkpoint.read_bytes()),
        "reload_tensors_exact": restored_exact,
        "reload_logits_exact": True,
        "development_responses_forwarded": 0,
        "reward_signal_used": False,
        "verifier_feedback_used": False,
        "elapsed_seconds": time.monotonic() - started,
        "stop_reason": "fixed_update_count",
        "scope": "TRAIN-only deterministic contrastive selector; no development proof-quality claim",
    })


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path, required=True)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--model-path", type=Path)
    parser.add_argument("--resume", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--device", choices=("cpu", "cuda"), default="cpu")
    parser.add_argument("--steps", type=int, default=17)
    parser.add_argument("--temperature", type=float, default=1.0)
    parser.add_argument("--lr", type=float, default=1e-5)
    parser.add_argument("--seconds", type=int, default=480)
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--seed", type=int, default=20260917)
    parser.add_argument("--expected-packet-sha256", default=PACKET_SHA256)
    parser.add_argument("--expected-manifest-sha256", default=MANIFEST_SHA256)
    parser.add_argument("--expected-parent-sha256", default=PARENT_SHA256)
    parser.add_argument("--preflight", action="store_true")
    args = parser.parse_args()
    if not (1 <= args.steps <= 64 and 0.05 <= args.temperature <= 5 and
            0 < args.lr <= 1e-4 and 120 <= args.seconds <= 900 and
            128 <= args.max_tokens <= 8192):
        parser.error("invalid bounded contrastive budget")
    if args.preflight:
        result = preflight(args.packet, args.output, args.expected_packet_sha256)
        print(json.dumps(result, indent=2))
        return 0
    if not args.manifest or not args.model_path or not args.resume:
        parser.error("training requires --manifest, --model-path, and --resume")
    if sha(args.manifest.read_bytes()) != args.expected_manifest_sha256:
        raise ValueError("manifest hash mismatch")
    worker(args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
