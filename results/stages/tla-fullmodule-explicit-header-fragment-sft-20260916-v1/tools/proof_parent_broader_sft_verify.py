#!/usr/bin/env python3
"""Independent same-runtime verification for a parent-broader SFT child."""
import argparse
import hashlib
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

PACKET_SHA = '5adb8315e8d9563fbf42a40fa5055d4e4b3b7f3e3c6e4ec7fe889b05ca030860'
PARENT_SHA = 'fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d'
CHILD_SHA = '3d7e08733268eccad08ab7dace3484c0e3b7158b5e84ab27658ccdd004af7304'
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'
EXPECTED = tuple('model.layers.31.' + name for name in (
    'input_layernorm.weight', 'mlp.down_proj.weight', 'mlp.gate_proj.weight',
    'mlp.up_proj.weight', 'post_attention_layernorm.weight',
    'self_attn.k_proj.weight', 'self_attn.o_proj.weight',
    'self_attn.q_proj.weight', 'self_attn.v_proj.weight'))
PARAMETERS = 218112000


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def model_files(path):
    paths = sorted(p for p in Path(path).iterdir() if p.is_file() and
                   (p.suffix in ('.json', '.safetensors') or
                    p.name in ('tokenizer.model', 'chat_template.jinja')))
    return {p.name: file_sha(p) for p in paths}


def selected_layer(net):
    import torch
    net.eval().requires_grad_(False)
    layer = net.model.layers[-1]
    layer.to(dtype=torch.float32)
    ids = {id(parameter) for parameter in layer.parameters()}
    selected = {name: parameter for name, parameter in net.named_parameters()
                if id(parameter) in ids}
    if tuple(sorted(selected)) != tuple(sorted(EXPECTED)):
        raise ValueError('Final-layer tensor inventory mismatch')
    if any(parameter.dtype != torch.float32 for parameter in selected.values()):
        raise ValueError('Final-layer tensors are not FP32')
    return selected


def restore(selected, state):
    import torch
    if set(state) != set(EXPECTED) or sum(value.numel() for value in state.values()) != PARAMETERS:
        raise ValueError('Child tensor inventory mismatch')
    with torch.no_grad():
        for name, parameter in selected.items():
            value = state[name]
            if (value.dtype != torch.float32 or value.shape != parameter.shape or
                    not bool(torch.isfinite(value).all())):
                raise ValueError('Child tensor invalid: ' + name)
            parameter.copy_(value)


def verify(args):
    import torch
    import transformers
    raw = args.packet.read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError('Frozen packet changed')
    packet = json.loads(raw)
    if packet.get('evaluation_responses_exported') is not False or len(packet['rows']) != 32:
        raise ValueError('Protected/evaluation material entered verification')
    if file_sha(args.child) != CHILD_SHA:
        raise ValueError('Retained child SHA mismatch')
    child = torch.load(args.child, map_location='cpu', weights_only=False)
    state = child.get('trainable_state')
    config = child.get('config', {})
    metrics = child.get('metrics')
    if (not isinstance(state, dict) or not isinstance(metrics, list) or len(metrics) != 100 or
            'optimizer' in child or config.get('parent_sha256') != PARENT_SHA or
            config.get('dtype_profile') != PROFILE or config.get('input_sha256') != PACKET_SHA):
        raise ValueError('Child metadata or optimizer omission mismatch')
    if (set(state) != set(EXPECTED) or sum(value.numel() for value in state.values()) != PARAMETERS or
            any(value.dtype != torch.float32 or not bool(torch.isfinite(value).all())
                for value in state.values())):
        raise ValueError('Child tensors are not exact finite FP32 state')
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model_path, local_files_only=True)
    from tools.proof_candidate_rank import encode_candidate
    probe = encode_candidate(tokenizer, packet['rows'][0]['prompt'], packet['rows'][0]['response'], 8192)
    hashes = model_files(args.model_path)
    if config.get('model_files') != hashes:
        raise ValueError('Child model-file identity mismatch')
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 is required for model-level reload verification')
    net = transformers.AutoModelForCausalLM.from_pretrained(
        args.model_path, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation='sdpa').to('cuda').eval()
    selected = selected_layer(net)
    restore(selected, state)
    ids = torch.tensor([probe['input_ids']], device='cuda')
    with torch.no_grad(), torch.autocast('cuda', dtype=torch.bfloat16):
        first = net(input_ids=ids, attention_mask=torch.ones_like(ids), use_cache=False).logits[0, -1].cpu()
    with torch.no_grad():
        for parameter in selected.values():
            parameter.zero_()
    reloaded = torch.load(args.child, map_location='cpu', weights_only=False)
    restore(selected, reloaded['trainable_state'])
    with torch.no_grad(), torch.autocast('cuda', dtype=torch.bfloat16):
        second = net(input_ids=ids, attention_mask=torch.ones_like(ids), use_cache=False).logits[0, -1].cpu()
    if not torch.equal(first, second):
        raise ValueError('Same-runtime child logit reload is not exact')
    result = dict(kind='parent_broader_sft_model_reload_verification_v1', complete=True,
                  packet_sha256=PACKET_SHA, parent_sha256=PARENT_SHA,
                  child_sha256=CHILD_SHA, child_bytes=args.child.stat().st_size,
                  tensor_names_exact=True, trainable_parameters=PARAMETERS,
                  tensors_finite_fp32=True, updates=100, optimizer_state_stored=False,
                  model_files_sha256=hashes, probe_input_ids_sha256=sha(
                      json.dumps(probe['input_ids'], sort_keys=True, separators=(',', ':')).encode()),
                  same_runtime_logits_exact=True, cuda_device=torch.cuda.get_device_name(),
                  torch_version=torch.__version__, transformers_version=transformers.__version__,
                  protected_training_rows=[], reference_responses_loaded=False,
                  gate_claim=False, quality_claim=False)
    if args.output:
        dump(args.output, result)
    print(json.dumps(result))
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--child', type=Path, required=True)
    parser.add_argument('--model-path', type=Path, required=True)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    verify(args)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
