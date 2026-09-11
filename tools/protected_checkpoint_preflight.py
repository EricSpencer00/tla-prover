#!/usr/bin/env python3
"""Preflight direct trained-checkpoint inference on the frozen protected rows.

This is deliberately a preflight, not an evaluator: it proves that the exact
base model, tokenizer, packet prompts, and saved trainable tensors agree before
any generation arm may be run.  It never changes a checkpoint or claims a gate.
"""
import argparse
import hashlib
import importlib
import importlib.metadata
import json
from pathlib import Path
import site
import sys


PACKET_SHA = "a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c"
PROTECTED = (47, 107)
PROFILE = "frozen bf16 base with float32 final transformer layer; bf16 autocast"
WANTED_IDS = {
    47: "w4-fullmodule:w4opus::d2-m7-p4-t2",
    107: "w4-fullmodule:w4opus::d3-m0-p0-t0",
}


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def model_files(model):
    files = sorted(p for p in Path(model).iterdir() if p.is_file() and
                   (p.suffix in (".json", ".safetensors") or
                    p.name in ("tokenizer.model", "chat_template.jinja")))
    if not any(p.suffix == ".safetensors" for p in files):
        raise ValueError("expected cached safetensors base model")
    return {p.name: file_sha(p) for p in files}


def protected_rows(packet):
    rows, encodings = packet.get("rows"), packet.get("encodings")
    if not isinstance(rows, list) or not isinstance(encodings, list) or len(rows) != len(encodings):
        raise ValueError("frozen packet rows/encodings are malformed")
    selected = {}
    for number, wanted in WANTED_IDS.items():
        found = [(row, encoding) for row, encoding in zip(rows, encodings)
                 if row.get("id") == wanted]
        if len(found) != 1:
            raise ValueError(f"protected row {number} is missing or duplicated")
        selected[number] = found[0]
    return selected


def verify_prompt_tokens(tokenizer, selected):
    evidence = {}
    for number, (row, encoding) in selected.items():
        rendered = tokenizer.apply_chat_template(
            [{"role": "user", "content": row["prompt"]}],
            tokenize=False, add_generation_prompt=True,
        )
        actual = tokenizer.encode(rendered, add_special_tokens=False)
        count = encoding.get("prompt_tokens")
        expected = encoding.get("input_ids", [])[:count]
        if not isinstance(count, int) or count <= 0 or actual != expected:
            raise ValueError(f"protected row {number} tokenizer/prompt mismatch")
        evidence[str(number)] = dict(prompt_sha256=hashlib.sha256(row["prompt"].encode()).hexdigest(),
                                     prompt_tokens=count)
    return evidence


def restore_exact(selected, saved):
    import torch
    state = saved.get("trainable_state")
    if not isinstance(state, dict) or set(selected) != set(state):
        raise ValueError("checkpoint trainable tensor names mismatch")
    with torch.no_grad():
        for name, parameter in selected.items():
            value = state[name]
            if value.dtype != parameter.dtype or value.shape != parameter.shape or not torch.isfinite(value).all():
                raise ValueError("checkpoint tensor mismatch: " + name)
            parameter.copy_(value.to(parameter.device))
    if not all(torch.equal(parameter.detach().cpu(), state[name].cpu())
               for name, parameter in selected.items()):
        raise ValueError("checkpoint tensor restore was not exact")


def load_xgrammar(site_path, grammar_path):
    """Load and exercise the isolated grammar dependency before CUDA/model work."""
    if site_path is not None:
        if not site_path.is_dir():
            raise ValueError(f"xgrammar site path is not a directory: {site_path}")
        site.addsitedir(str(site_path))
    try:
        xgrammar = importlib.import_module("xgrammar")
    except ModuleNotFoundError as error:
        raise ValueError("xgrammar is unavailable before model loading") from error
    try:
        compiled = xgrammar.Grammar.from_ebnf(grammar_path.read_text())
    except Exception as error:
        raise ValueError("xgrammar grammar compilation failed before model loading") from error
    if compiled is None:
        raise ValueError("xgrammar grammar compilation returned no grammar")
    try:
        version = importlib.metadata.version("xgrammar")
    except importlib.metadata.PackageNotFoundError:
        version = getattr(xgrammar, "__version__", "unknown")
    return xgrammar, version


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", type=Path)
    parser.add_argument("--model", type=Path)
    parser.add_argument("--checkpoint", type=Path)
    parser.add_argument("--grammar", type=Path, required=True)
    parser.add_argument("--xgrammar-site", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--dependency-only", action="store_true",
                        help="compile grammar without importing torch or allocating CUDA")
    args = parser.parse_args()
    _, xgrammar_version = load_xgrammar(args.xgrammar_site, args.grammar)
    if args.dependency_only:
        print(json.dumps(dict(kind="xgrammar_dependency_preflight_v1",
                              grammar_sha256=file_sha(args.grammar),
                              xgrammar_version=xgrammar_version,
                              xgrammar_site=None if args.xgrammar_site is None else str(args.xgrammar_site),
                              cuda_touched=False, gate_claim=False), sort_keys=True))
        return
    if None in (args.packet, args.model, args.checkpoint, args.output):
        raise ValueError("packet, model, checkpoint, and output are required unless dependency-only")
    if args.output.exists():
        raise ValueError("append-only output already exists")
    if file_sha(args.packet) != PACKET_SHA:
        raise ValueError("frozen packet hash mismatch")
    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError("CUDA bf16 required")
    packet = json.loads(args.packet.read_text())
    selected_rows = protected_rows(packet)
    files = model_files(args.model)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    prompt_evidence = verify_prompt_tokens(tokenizer, selected_rows)
    saved = torch.load(args.checkpoint, map_location="cpu", weights_only=False)
    if saved.get("config", {}).get("model_files") != files or saved["config"].get("dtype_profile") != PROFILE:
        raise ValueError("checkpoint base model/dtype profile mismatch")
    net = transformers.AutoModelForCausalLM.from_pretrained(
        args.model, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation="sdpa").to("cuda").eval().requires_grad_(False)
    layer = net.model.layers[-1]
    layer.to(dtype=torch.float32)
    trainable_ids = {id(parameter) for parameter in layer.parameters()}
    selected = {name: parameter for name, parameter in net.named_parameters()
                if id(parameter) in trainable_ids}
    restore_exact(selected, saved)
    args.output.mkdir(parents=True)
    receipt = dict(kind="protected_checkpoint_preflight_v1", complete=True,
                   packet_sha256=PACKET_SHA, checkpoint_sha256=file_sha(args.checkpoint),
                   model_files=files, restored_parameter_count=len(selected),
                   restored_tensors_exact=True, protected_prompt_tokens=prompt_evidence,
                   grammar_sha256=file_sha(args.grammar),
                   grammar_compiled=True, producer="preflight_only", gate_claim=False)
    receipt["xgrammar_version"] = xgrammar_version
    receipt["xgrammar_site"] = None if args.xgrammar_site is None else str(args.xgrammar_site)
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, sort_keys=True))


if __name__ == "__main__":
    main()
