#!/usr/bin/env python3
"""Train one parent-initialized, whole-target broader SFT child.

This branch is deliberately separate from the historical fresh-base broader
cycle.  It consumes the frozen 32-row packet, restores the exact nine final
transformer tensors from the admitted parent, uses fresh AdamW state, and
writes only an exact FP32 child checkpoint (no optimizer state).  Protected
rows are never loaded by the training path.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import random
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

PACKET_SHA = '5adb8315e8d9563fbf42a40fa5055d4e4b3b7f3e3c6e4ec7fe889b05ca030860'
PARENT_SHA = 'fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d'
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'
ALGORITHM = 'response-only causal cross-entropy SFT; parent-initialized final layer; fresh float32 AdamW; no RL'
SEED = 20260915
STEPS = 100
SECONDS = 600
MAX_TOKENS = 8192
LR = 1e-6
NAMES = (
    'input_layernorm.weight', 'mlp.down_proj.weight', 'mlp.gate_proj.weight',
    'mlp.up_proj.weight', 'post_attention_layernorm.weight',
    'self_attn.k_proj.weight', 'self_attn.o_proj.weight',
    'self_attn.q_proj.weight', 'self_attn.v_proj.weight')
EXPECTED_NAMES = tuple('model.layers.31.' + name for name in NAMES)
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


def schedule(count=32, steps=STEPS, seed=SEED):
    if count != 32 or steps != STEPS:
        raise ValueError('This branch has an immutable 32-row, 100-update schedule')
    rng = random.Random(seed)
    indices = []
    while len(indices) < steps:
        epoch = list(range(count))
        rng.shuffle(epoch)
        indices.extend(epoch)
    return indices[:steps]


def model_files(model_path):
    paths = sorted(p for p in Path(model_path).iterdir() if p.is_file() and
                   (p.suffix in ('.json', '.safetensors') or
                    p.name in ('tokenizer.model', 'chat_template.jinja')))
    if not any(p.suffix == '.safetensors' for p in paths):
        raise ValueError('Expected cached safetensors model')
    return {p.name: file_sha(p) for p in paths}


def validate_packet(raw):
    if sha(raw) != PACKET_SHA:
        raise ValueError('Frozen broader packet SHA mismatch')
    packet = json.loads(raw)
    # The packet validator is stdlib-only apart from its imported constants;
    # it never executes a checker or reads a protected answer.
    from tools.proof_broader_packet import validate_training_packet
    rows = validate_training_packet(packet)
    if len(rows) != 32 or packet['evaluation_responses_exported'] is not False:
        raise ValueError('Exact non-protected 32-row packet required')
    return packet, rows


def encode(tokenizer, row):
    from tools.proof_candidate_rank import encode_candidate
    value = encode_candidate(tokenizer, row['prompt'], row['response'], MAX_TOKENS)
    if value['response_tokens'] < 2 or value['response_tokens'] > 3072:
        raise ValueError('Frozen whole-target response budget mismatch: ' + row['id'])
    if value['input_ids'][-1] != tokenizer.eos_token_id:
        raise ValueError('Training response must end at the tokenizer EOS: ' + row['id'])
    return value


def preflight(args):
    raw = args.input.read_bytes()
    packet, rows = validate_packet(raw)
    if args.checkpoint.exists() and file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('Parent checkpoint SHA mismatch')
    if not args.checkpoint.is_file():
        raise ValueError('Parent checkpoint is missing')
    import transformers
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model_path, local_files_only=True)
    encoded = [encode(tokenizer, row) for row in rows]
    frozen = packet['token_feasibility']['rows']
    if [r['id'] for r in frozen[:32]] != [r['id'] for r in rows]:
        raise ValueError('Packet feasibility ordering mismatch')
    for row, value, expected in zip(rows, encoded, frozen[:32]):
        actual_ids_sha = sha(json.dumps(value['input_ids'], sort_keys=True,
                                        separators=(',', ':')).encode())
        if expected['training_token_ids_sha256'] != actual_ids_sha:
            raise ValueError('Frozen token identity mismatch: ' + row['id'])
        if (expected['prompt_tokens'] != value['prompt_tokens'] or
                expected['response_tokens'] != value['response_tokens'] or
                expected['total_tokens'] != len(value['input_ids']) or
                expected['training_inference_prefix_equal'] is not True):
            raise ValueError('Frozen tokenizer feasibility mismatch: ' + row['id'])
    result = dict(kind='parent_broader_sft_cpu_preflight_v1', complete=True,
                  packet_sha256=PACKET_SHA, parent_sha256=PARENT_SHA,
                  train_rows=32, protected_rows=[],
                  tokenization_rows=len(encoded), max_tokens=MAX_TOKENS,
                  schedule_sha256=sha(json.dumps(schedule(), separators=(',', ':')).encode()),
                  model_files=model_files(args.model_path),
                  reference_responses_loaded=False, cuda_loaded=False,
                  gate_claim=False, quality_claim=False)
    if args.receipt:
        dump(args.receipt, result)
    print(json.dumps(result))
    return result


def select_final_layer(net, train=False):
    import torch
    net.eval().requires_grad_(False)
    layer = net.model.layers[-1]
    layer.to(dtype=torch.float32)
    layer.requires_grad_(train)
    layer_parameter_ids = {id(parameter) for parameter in layer.parameters()}
    selected = {name: parameter for name, parameter in net.named_parameters()
                if id(parameter) in layer_parameter_ids}
    if tuple(sorted(selected)) != tuple(sorted(EXPECTED_NAMES)):
        raise ValueError('Expected exactly nine final-layer tensors')
    if any(parameter.dtype != torch.float32 for parameter in selected.values()):
        raise ValueError('Selected tensors must be float32')
    return selected


def restore(selected, saved):
    import torch
    state = saved.get('trainable_state')
    if not isinstance(state, dict) or set(state) != set(EXPECTED_NAMES):
        raise ValueError('Parent checkpoint tensor names mismatch')
    if sum(value.numel() for value in state.values()) != PARAMETERS:
        raise ValueError('Parent checkpoint tensor count mismatch')
    with torch.no_grad():
        for name, parameter in selected.items():
            value = state[name]
            if (value.dtype != torch.float32 or value.shape != parameter.shape or
                    not bool(torch.isfinite(value).all())):
                raise ValueError('Parent tensor invalid: ' + name)
            parameter.copy_(value)
    if not all(torch.equal(parameter.detach().cpu(), state[name])
               for name, parameter in selected.items()):
        raise ValueError('Parent tensor restore was not exact')


def train(args):
    raw = args.input.read_bytes()
    packet, rows = validate_packet(raw)
    if file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('Immutable parent checkpoint mismatch')
    if args.steps != STEPS or args.seconds != SECONDS or args.max_tokens != MAX_TOKENS or args.lr != LR:
        raise ValueError('Immutable training budget changed')
    import torch
    import transformers
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 is required; no CPU/model fallback')
    torch.set_num_threads(4)
    random.seed(SEED)
    torch.manual_seed(SEED)
    torch.cuda.manual_seed_all(SEED)
    torch.backends.cuda.matmul.allow_tf32 = False
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model_path, local_files_only=True)
    encoded = [encode(tokenizer, row) for row in rows]
    hashes = model_files(args.model_path)
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output / 'train.json').write_bytes(raw)
    net = transformers.AutoModelForCausalLM.from_pretrained(
        args.model_path, local_files_only=True, torch_dtype=torch.bfloat16,
        attn_implementation='sdpa').to('cuda').eval()
    selected = select_final_layer(net, train=False)
    saved_parent = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    parent_config = saved_parent.get('config', {})
    if (parent_config.get('model_files') != hashes or
            parent_config.get('dtype_profile') != PROFILE):
        raise ValueError('Parent model identity or dtype profile mismatch')
    base_state = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    restore(selected, saved_parent)
    parent_state = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    base_delta = math.sqrt(sum(float((parent_state[n] - base_state[n]).double().square().sum())
                               for n in EXPECTED_NAMES))
    if not math.isfinite(base_delta) or base_delta <= 0:
        raise ValueError('Parent is indistinguishable from the base model')
    for parameter in selected.values():
        parameter.requires_grad_(True)
    config = dict(schema=1, algorithm=ALGORITHM, dtype_profile=PROFILE,
                  input_sha256=PACKET_SHA, parent_sha256=PARENT_SHA,
                  model_files=hashes, seed=SEED, lr=LR, requested_updates=STEPS,
                  seconds=SECONDS, max_tokens=MAX_TOKENS,
                  train_ids=[row['id'] for row in rows],
                  task_schedule=schedule(), trainable_names=list(EXPECTED_NAMES),
                  trainable_parameters=PARAMETERS,
                  optimizer_initialization='fresh AdamW; parent optimizer/RNG not resumed',
                  optimizer_state_stored=False, optimizer_resume_supported=False,
                  checkpoint_serialization='legacy_no_zip_exact_fp32_weights',
                  parent_vs_base_parameter_delta_l2=base_delta,
                  protected_training_rows=[], protected_evaluation_rows=[47, 107],
                  gate_claim=False, quality_claim=False)
    dump(args.output / 'config.json', config)
    dump(args.output / 'encodings.json', [dict(id=row['id'], **value)
                                          for row, value in zip(rows, encoded)])
    probe_ids = torch.tensor([encoded[0]['input_ids']], device='cuda')
    with torch.no_grad(), torch.autocast('cuda', dtype=torch.bfloat16):
        parent_probe = net(input_ids=probe_ids, use_cache=False).logits[0, -1].float().cpu()
    optimizer = torch.optim.AdamW(selected.values(), lr=LR, weight_decay=0.0, foreach=False)
    started = time.monotonic()
    ledger = []
    with (args.output / 'steps.jsonl').open('x') as stream:
        for step, index in enumerate(schedule(), 1):
            if time.monotonic() - started >= SECONDS - 90:
                raise RuntimeError('Training reached the checkpoint reserve before 100 updates')
            ids = torch.tensor([encoded[index]['input_ids']], device='cuda')
            labels = torch.tensor([encoded[index]['labels']], device='cuda')
            optimizer.zero_grad(set_to_none=True)
            with torch.autocast('cuda', dtype=torch.bfloat16):
                loss = net(input_ids=ids, attention_mask=torch.ones_like(ids),
                           labels=labels, use_cache=False).loss
            if not bool(torch.isfinite(loss)):
                raise RuntimeError('Nonfinite loss at step ' + str(step))
            loss.backward()
            norms = {name: float(parameter.grad.detach().float().norm())
                     for name, parameter in selected.items()
                     if parameter.grad is not None and bool(torch.isfinite(parameter.grad).all())}
            if set(norms) != set(EXPECTED_NAMES) or not any(norms.values()):
                raise RuntimeError('Incomplete or zero finite gradient at step ' + str(step))
            norm = float(torch.nn.utils.clip_grad_norm_(selected.values(), 1.0,
                                                        error_if_nonfinite=True))
            optimizer.step()
            if any(not bool(torch.isfinite(parameter).all()) for parameter in selected.values()):
                raise RuntimeError('Nonfinite parameter after step ' + str(step))
            entry = dict(step=step, index=index, task=rows[index]['id'],
                         loss=float(loss.detach()), gradient_norm=norm,
                         gradient_norms=norms, response_tokens=encoded[index]['response_tokens'],
                         elapsed_s=time.monotonic() - started)
            stream.write(json.dumps(entry) + '\n'); stream.flush()
            print(json.dumps(entry), flush=True)
            del loss, ids, labels
            torch.cuda.empty_cache()
    if len(ledger) != 0:
        raise ValueError('Internal ledger invariant')
    metrics = [json.loads(line) for line in (args.output / 'steps.jsonl').read_text().splitlines()]
    if len(metrics) != STEPS:
        raise RuntimeError('Exactly 100 optimizer updates required')
    state = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    delta = math.sqrt(sum(float((state[n] - parent_state[n]).double().square().sum())
                          for n in EXPECTED_NAMES))
    if not math.isfinite(delta) or delta <= 0:
        raise RuntimeError('Child tensor delta is not finite and positive')
    checkpoint = args.output / 'policy_optimizer.pt'
    payload = dict(trainable_state=state, config=config, metrics=metrics)
    temporary = args.output / '.policy_optimizer.pt.tmp'
    torch.save(payload, temporary, _use_new_zipfile_serialization=False)
    os.replace(temporary, checkpoint)
    child_sha = file_sha(checkpoint)
    with torch.no_grad(), torch.autocast('cuda', dtype=torch.bfloat16):
        child_probe = net(input_ids=probe_ids, use_cache=False).logits[0, -1].float().cpu()
    for parameter in selected.values():
        parameter.zero_()
    reload = torch.load(checkpoint, map_location='cpu', weights_only=False)
    restore(selected, reload)
    with torch.no_grad(), torch.autocast('cuda', dtype=torch.bfloat16):
        reload_probe = net(input_ids=probe_ids, use_cache=False).logits[0, -1].float().cpu()
    if not torch.equal(child_probe, reload_probe):
        raise RuntimeError('Exact child logit reload failed')
    exact = all(torch.equal(parameter.detach().cpu(), state[name])
                for name, parameter in selected.items())
    if not exact:
        raise RuntimeError('Exact child tensor reload failed')
    summary = dict(kind='parent_broader_sft_training_v1', complete=True,
                   packet_sha256=PACKET_SHA, parent_sha256=PARENT_SHA,
                   child_sha256=child_sha, child_bytes=checkpoint.stat().st_size,
                   updates=len(metrics), parameter_delta_l2=delta,
                   parent_vs_base_parameter_delta_l2=base_delta,
                   reload_tensors_exact=True, reload_logits_exact=True,
                   optimizer_state_stored=False, protected_training_rows=[],
                   protected_evaluation_rows=[47, 107], gate_claim=False,
                   quality_claim=False, model_improvement_claim=False,
                   elapsed_s=time.monotonic() - started,
                   cuda_device=torch.cuda.get_device_name(),
                   torch_version=torch.__version__, transformers_version=transformers.__version__)
    dump(args.output / 'summary.json', summary)
    print(json.dumps(summary), flush=True)
    return summary


def main():
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest='mode', required=True)
    for mode in ('preflight', 'train'):
        p = sub.add_parser(mode)
        p.add_argument('--input', type=Path, required=True)
        p.add_argument('--checkpoint', type=Path, required=True)
        p.add_argument('--model-path', type=Path, required=True)
        p.add_argument('--output', type=Path)
        p.add_argument('--receipt', type=Path)
        p.add_argument('--steps', type=int, default=STEPS)
        p.add_argument('--seconds', type=int, default=SECONDS)
        p.add_argument('--max-tokens', type=int, default=MAX_TOKENS)
        p.add_argument('--lr', type=float, default=LR)
    args = parser.parse_args()
    if args.mode == 'preflight':
        preflight(args)
        return 0
    if args.output is None:
        parser.error('train requires --output')
    train(args)
    return 0


if __name__ == '__main__':
    raise SystemExit(main() or 0)
