#!/usr/bin/env python3
"""Bounded prefix-conditioned response SFT for the non-protected packet rows.

This branch is deliberately distinct from pairwise span preference training:
the frozen user prefix is retained and every reference response token,
including EOS, receives response-only causal supervision. Protected rows are
used only for the unchanged before/after diagnostic and never for training or
model selection. The result is a diagnostic child, not a gate claim.
"""

from __future__ import annotations

import argparse
from contextlib import nullcontext
import json
import math
from pathlib import Path
import random
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
try:
    from tools.proof_syntax_preference_train import (  # noqa: E402
        PROFILE,
        file_sha,
        restore,
        sany,
        save_exact_weights,
        sha,
    )
except ModuleNotFoundError:
    from proof_syntax_preference_train import (  # noqa: E402
        PROFILE,
        file_sha,
        restore,
        sany,
        save_exact_weights,
        sha,
    )

PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
PARENT_SHA = "fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d"
TRAIN = (45, 46, 50, 51)
VALID = (52, 53)
PROTECTED = (47, 107)
BUDGET = dict(
    updates=16,
    lr=2e-7,
    weight_decay=0.0,
    clip=1.0,
    seed=20260914,
    training_seconds=600,
    max_new_tokens=1024,
    generation_seconds=45,
)


def load_packet(packet_path: Path):
    raw = packet_path.read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError("frozen full-module packet changed")
    packet = json.loads(raw)
    rows = packet.get("rows")
    encodings = packet.get("encodings")
    if not isinstance(rows, list) or not isinstance(encodings, list) or len(rows) != len(encodings):
        raise ValueError("packet rows and encodings must be aligned")
    for index in TRAIN + VALID + PROTECTED:
        row, encoding = rows[index], encodings[index]
        if encoding.get("id") != row.get("id"):
            raise ValueError(f"packet encoding identity mismatch at row {index}")
        if row.get("response_sha256") != sha(row.get("response", "").encode()):
            raise ValueError(f"packet response identity mismatch at row {index}")
        ids, labels = encoding.get("input_ids"), encoding.get("labels")
        prompt_tokens = encoding.get("prompt_tokens")
        if (not isinstance(ids, list) or not isinstance(labels, list) or len(ids) != len(labels)
                or type(prompt_tokens) is not int or not 0 < prompt_tokens < len(ids)):
            raise ValueError(f"packet encoding shape mismatch at row {index}")
        if labels[:prompt_tokens] != [-100] * prompt_tokens:
            raise ValueError(f"prompt labels are not fully masked at row {index}")
        if any(label == -100 for label in labels[prompt_tokens:]):
            raise ValueError(f"response labels contain masked tokens at row {index}")
    return raw, packet


def model_files(model_path: Path):
    return {
        path.name: file_sha(path)
        for path in sorted(model_path.iterdir())
        if path.is_file() and (path.suffix in (".json", ".safetensors")
                               or path.name in ("tokenizer.model", "chat_template.jinja"))
    }


def prepare(args):
    raw, packet = load_packet(args.packet)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    (output / "packet.json").write_bytes(raw)
    shutil.copyfile(Path(__file__), output / "proof_prefix_sft_train.py")
    shutil.copyfile(ROOT / "tools/proof_syntax_preference_train.py",
                    output / "proof_syntax_preference_train.py")
    manifest = dict(
        kind="prefix_conditioned_response_sft_v1",
        packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA,
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        budget=BUDGET,
        train_response_sha256={str(index): packet["rows"][index]["response_sha256"] for index in TRAIN},
        validation_response_sha256={str(index): packet["rows"][index]["response_sha256"] for index in VALID},
        no_protected_training=True,
        no_protected_model_selection=True,
        gate_claim=False,
        model_improvement_claim=False,
    )
    manifest_bytes = json.dumps(manifest, indent=2, sort_keys=True).encode() + b"\n"
    (output / "manifest.json").write_bytes(manifest_bytes)
    sums = {
        name: file_sha(output / name)
        for name in ("packet.json", "manifest.json", "proof_prefix_sft_train.py",
                     "proof_syntax_preference_train.py")
    }
    (output / "SHA256SUMS").write_text(
        "".join(f"{digest}  {name}\n" for name, digest in sorted(sums.items())),
        encoding="utf-8",
    )
    print(json.dumps({"manifest_sha256": file_sha(output / "manifest.json"), "packet_sha256": PACKET_SHA}))


def verify_tokenizer(tokenizer, packet):
    for index in TRAIN + VALID + PROTECTED:
        row, encoding = packet["rows"][index], packet["encodings"][index]
        messages = [{"role": "user", "content": row["prompt"]}]
        rendered_prompt = tokenizer.apply_chat_template(
            messages, tokenize=False, add_generation_prompt=True)
        full = tokenizer.apply_chat_template(
            messages + [{"role": "assistant", "content": row["response"]}],
            tokenize=False, add_generation_prompt=False)
        prompt_ids = tokenizer.encode(rendered_prompt, add_special_tokens=False)
        full_ids = tokenizer.encode(full, add_special_tokens=False)
        if (rendered_prompt != encoding["rendered_prompt"]
                or prompt_ids != encoding["input_ids"][:encoding["prompt_tokens"]]
                or full_ids != encoding["input_ids"]):
            raise ValueError(f"actual tokenizer/prefix drift at row {index}")


def response_loss(net, encoding, device, context):
    import torch
    ids = torch.tensor([encoding["input_ids"]], dtype=torch.long, device=device)
    labels = torch.tensor([encoding["labels"]], dtype=torch.long, device=device)
    with context():
        result = net(input_ids=ids, attention_mask=torch.ones_like(ids),
                     labels=labels, use_cache=False)
    if not bool(torch.isfinite(result.loss)):
        raise ValueError("nonfinite response-only loss")
    return result


def mean_response_loss(net, encodings, device, context):
    values = []
    import torch
    with torch.no_grad():
        for encoding in encodings:
            values.append(float(response_loss(net, encoding, device, context).loss))
    if not values or not all(math.isfinite(value) for value in values):
        raise ValueError("nonfinite validation loss")
    return sum(values) / len(values)


def generate(net, tokenizer, packet, output, phase, java, jar, context):
    import torch
    records = []
    for index in PROTECTED:
        encoding = packet["encodings"][index]
        ids = torch.tensor([encoding["input_ids"][:encoding["prompt_tokens"]]], device="cuda")
        started = time.monotonic()
        with torch.inference_mode(), context():
            answer = net.generate(
                input_ids=ids,
                attention_mask=torch.ones_like(ids),
                do_sample=False,
                max_new_tokens=BUDGET["max_new_tokens"],
                max_time=BUDGET["generation_seconds"],
                eos_token_id=[128001, 128008, 128009],
                pad_token_id=128009,
                use_cache=True,
            )
        tokens = answer[0, ids.shape[1]:].tolist()
        text = tokenizer.decode(tokens, skip_special_tokens=True)
        terminal = bool(tokens and tokens[-1] in (128001, 128008, 128009))
        record = dict(
            row=index,
            phase=phase,
            raw_reply=text,
            raw_reply_sha256=sha(text.encode()),
            token_count=len(tokens),
            elapsed_seconds=time.monotonic() - started,
            finish_reason="eos" if terminal else "token_or_time_limit",
            prefix_conditioned_sft=True,
            training=phase == "trained_child",
            protected_training=False,
            gate_claim=False,
        )
        record["sany"] = sany(text, output / f"sany/{phase}/{index}", java, jar)
        records.append(record)
        (output / f"{phase}-row-{index}.json").write_text(json.dumps(record, indent=2) + "\n")
    return records


def train(args):
    import torch
    import transformers

    raw, packet = load_packet(args.packet)
    if file_sha(args.manifest) != args.manifest_sha256 or file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError("manifest/checkpoint identity mismatch")
    manifest = json.loads(args.manifest.read_text())
    expected_manifest = dict(
        kind="prefix_conditioned_response_sft_v1",
        packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA,
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        budget=BUDGET,
        train_response_sha256={str(index): packet["rows"][index]["response_sha256"] for index in TRAIN},
        validation_response_sha256={str(index): packet["rows"][index]["response_sha256"] for index in VALID},
        no_protected_training=True,
        no_protected_model_selection=True,
        gate_claim=False,
        model_improvement_claim=False,
    )
    if manifest != expected_manifest:
        raise ValueError("training manifest changed")
    if args.output.exists():
        raise ValueError("append-only output already exists")
    args.output.mkdir(parents=True)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    verify_tokenizer(tokenizer, packet)
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    files = model_files(args.model)
    saved = torch.load(args.checkpoint, map_location="cpu", weights_only=False)
    if (saved.get("config", {}).get("model_files") != files
            or saved.get("config", {}).get("dtype_profile") != PROFILE):
        raise ValueError("parent checkpoint model lineage mismatch")
    net = transformers.AutoModelForCausalLM.from_pretrained(
        args.model, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa").to("cuda").eval().requires_grad_(False)
    net.model.layers[-1].to(torch.float32)
    selected = {name: parameter for name, parameter in net.named_parameters()
                if name.startswith("model.layers.31.")}
    if len(selected) != 9:
        raise ValueError("expected exactly nine final-layer tensors")
    restore(selected, saved)
    initial = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    for parameter in selected.values():
        parameter.requires_grad_(True)
    encodings = packet["encodings"]
    train_encodings = [encodings[index] for index in TRAIN]
    valid_encodings = [encodings[index] for index in VALID]
    context = lambda: torch.autocast("cuda", dtype=torch.bfloat16)
    before_validation = mean_response_loss(net, valid_encodings, "cuda", context)
    longest = max(train_encodings, key=lambda encoding: len(encoding["input_ids"]))
    net.zero_grad(set_to_none=True)
    preflight_result = response_loss(net, longest, "cuda", context)
    preflight_loss = float(preflight_result.loss.detach())
    preflight_result.loss.backward()
    gradient_norms = {
        name: float(parameter.grad.detach().float().norm())
        for name, parameter in selected.items()
        if parameter.grad is not None
    }
    if (set(gradient_norms) != set(selected)
            or not all(math.isfinite(value) and value > 0 for value in gradient_norms.values())):
        raise ValueError("preflight requires finite nonzero gradients on all nine tensors")
    if any(not torch.equal(parameter.detach().cpu(), initial[name])
           for name, parameter in selected.items()):
        raise ValueError("preflight changed parent parameters")
    net.zero_grad(set_to_none=True)
    (args.output / "preflight.json").write_text(json.dumps(dict(
        longest_input_tokens=len(longest["input_ids"]),
        loss=preflight_loss,
        gradient_norms=gradient_norms,
        parameters_unchanged=True,
        optimizer_updates=0,
    ), indent=2) + "\n")
    before = generate(net, tokenizer, packet, args.output, "restored_parent", args.java, args.jar, context)
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET["lr"],
                                  weight_decay=BUDGET["weight_decay"], foreach=False)
    random.seed(BUDGET["seed"])
    torch.manual_seed(BUDGET["seed"])
    started = time.monotonic()
    ledger = []
    for step in range(BUDGET["updates"]):
        if time.monotonic() - started >= BUDGET["training_seconds"]:
            raise TimeoutError("training time budget exhausted before complete schedule")
        encoding = train_encodings[step % len(train_encodings)]
        optimizer.zero_grad(set_to_none=True)
        result = response_loss(net, encoding, "cuda", context)
        result.loss.backward()
        norm = float(torch.nn.utils.clip_grad_norm_(selected.values(), BUDGET["clip"],
                                                    error_if_nonfinite=True))
        if not math.isfinite(norm) or norm <= 0:
            raise ValueError("nonfinite or zero training gradient norm")
        optimizer.step()
        if any(not bool(torch.isfinite(parameter).all()) for parameter in selected.values()):
            raise ValueError("nonfinite trained parameter")
        ledger.append(dict(step=step + 1, row=TRAIN[step % len(TRAIN)],
                           loss=float(result.loss.detach()), gradient_norm=norm))
        with (args.output / "steps.jsonl").open("a", encoding="utf-8") as stream:
            stream.write(json.dumps(ledger[-1]) + "\n")
        print(json.dumps(ledger[-1]), flush=True)
    state = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    delta = math.sqrt(sum(float((state[name] - initial[name]).double().square().sum())
                          for name in state))
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError("trained child did not change finitely")
    config = dict(
        kind=manifest["kind"], packet_sha256=PACKET_SHA, parent_checkpoint_sha256=PARENT_SHA,
        manifest_sha256=args.manifest_sha256, model_files=files, dtype_profile=PROFILE,
        budget=BUDGET, train_rows=list(TRAIN), validation_rows=list(VALID),
        protected_rows=list(PROTECTED), optimizer_state_stored=False,
        optimizer_resume_supported=False, checkpoint_serialization="legacy_no_zip_exact_fp32_weights",
    )
    checkpoint_path = args.output / "policy_optimizer.pt"
    save_exact_weights(torch, dict(trainable_state=state, config=config, metrics=ledger), checkpoint_path)
    loaded = torch.load(checkpoint_path, map_location="cpu", weights_only=False)
    restore(selected, loaded)
    if not all(torch.equal(parameter.detach().cpu(), state[name])
               for name, parameter in selected.items()):
        raise ValueError("child checkpoint tensor reload failed")
    after_validation = mean_response_loss(net, valid_encodings, "cuda", context)
    after = generate(net, tokenizer, packet, args.output, "trained_child", args.java, args.jar, context)
    receipt = dict(
        complete=True,
        kind=manifest["kind"],
        packet_sha256=PACKET_SHA,
        manifest_sha256=args.manifest_sha256,
        parent_checkpoint_sha256=PARENT_SHA,
        updates=len(ledger),
        parameter_delta_l2=delta,
        validation_loss_before=before_validation,
        validation_loss_after=after_validation,
        child_sha256=file_sha(checkpoint_path),
        child_bytes=checkpoint_path.stat().st_size,
        reload_tensors_exact=True,
        optimizer_state_stored=False,
        optimizer_resume_supported=False,
        checkpoint_serialization="legacy_no_zip_exact_fp32_weights",
        preflight=json.loads((args.output / "preflight.json").read_text()),
        before_protected=before,
        after_protected=after,
        protected_training=False,
        protected_model_selection=False,
        gate_claim=False,
        model_improvement_claim=False,
    )
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, sort_keys=True), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="mode", required=True)
    prepare_parser = subparsers.add_parser("prepare")
    prepare_parser.add_argument("--packet", type=Path, required=True)
    prepare_parser.add_argument("--output", type=Path, required=True)
    train_parser = subparsers.add_parser("train")
    for name in ("packet", "manifest", "checkpoint", "model", "jar", "output"):
        train_parser.add_argument("--" + name, type=Path, required=True)
    train_parser.add_argument("--manifest-sha256", required=True)
    train_parser.add_argument("--java", default="java")
    args = parser.parse_args()
    if args.mode == "prepare":
        prepare(args)
    else:
        train(args)


if __name__ == "__main__":
    main()
