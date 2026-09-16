"""Wide continuation-aware LoRA SFT with fixed structure/EOS token weights.

This is a bounded diagnostic after semantic preference and last-four q/v SFT
failed to move the protected SANY denominator. It uses only immutable
SANY-passing reference responses from non-protected rows, zero-initialized
low-rank adapters across layers 24--31 and all attention/MLP projections, plus
explicit continuation/EOS weighting. It never trains on protected outputs,
generated feedback, or verifier-derived rewards.
No generated feedback, verifier reward, or protected training is used.
"""
import argparse
import contextlib
import hashlib
import json
import math
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi

PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
PARENT_SHA = '87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511'
TRAIN = (42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58)
VALID = (59, 60, 61, 62, 63, 64)
PROTECTED = (47, 107)
MODULE_NAMES = {47: 'W4Od2m7p4t2', 107: 'W4Od3m0p0t0'}
EOS_IDS = (128001, 128008, 128009)
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'
STRUCTURAL_CHARS = frozenset('\n/\\[](){}=<>:|,!?\'#+-*')
BUDGET = dict(
    steps=12, accumulation=2, lr=1e-4, rank=4, alpha=8,
    base_weight=1., structural_weight=2., eos_weight=16., seed=20260916,
    training_seconds=480, max_new_tokens=2048, generation_seconds=60,
    sany_seconds=30, adapter_layers=[24, 25, 26, 27, 28, 29, 30, 31],
    adapter_targets=['q_proj', 'k_proj', 'v_proj', 'o_proj',
                    'gate_proj', 'up_proj', 'down_proj'],
    objective='wide_continuation_eos_weighted_clean_reference_sft',
)

multi.BUDGET.update(
    max_new_tokens=BUDGET['max_new_tokens'], item_seconds=BUDGET['generation_seconds'],
    sany_seconds=BUDGET['sany_seconds'], train_only=False, eval_rows=list(PROTECTED),
    gate_claim=False, quality_claim=False, generalization_claim=False,
    proof_claim=False, tlc_claim=False, nonvacuity_claim=False,
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024**2), b''):
            h.update(chunk)
    return h.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def module_name(text):
    match = re.search(r'^-+ MODULE (\w+) -+\s*$', text, re.M)
    if not match:
        raise ValueError('canonical module header required')
    return match[1]


def sany(text, output, java, jar):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    try:
        name = module_name(text)
    except ValueError:
        result = dict(status='model_reject', passed=False, reason='missing module header')
    else:
        (output / (name + '.tla')).write_text(text)
        try:
            proc = subprocess.run(
                [java, '-cp', str(Path(jar).resolve()), 'tla2sany.SANY', name + '.tla'],
                cwd=output, capture_output=True, text=True,
                timeout=BUDGET['sany_seconds'])
            log = proc.stdout + proc.stderr
            (output / 'sany.log').write_text(log)
            if re.search(r'\*\*\*\s*(?:Parse|Semantic)|Fatal errors|Parse Error|Semantic errors', log, re.I):
                result = dict(status='model_reject', passed=False, returncode=proc.returncode)
            elif re.search(r'Exception|Could not find|NoClassDef|OutOfMemory', log):
                result = dict(status='infrastructure_error', passed=None, returncode=proc.returncode)
            elif proc.returncode == 0 and 'Semantic processing of module ' + name in log:
                result = dict(status='pass', passed=True, returncode=0)
            else:
                result = dict(status='infrastructure_unknown', passed=None, returncode=proc.returncode)
        except subprocess.TimeoutExpired:
            result = dict(status='infrastructure_timeout', passed=None)
    dump(output / 'result.json', result)
    return result


def verify_manifest(args, *, require_preflight=False):
    if sha(args.packet.read_bytes()) != PACKET_SHA:
        raise ValueError('frozen packet changed')
    if file_sha(args.manifest) != args.manifest_sha256:
        raise ValueError('manifest hash mismatch')
    manifest = json.loads(args.manifest.read_text())
    if (manifest.get('kind') != 'fullmodule_wide_continuation_sft_v1' or
            manifest['packet_sha256'] != PACKET_SHA or
            manifest['parent_checkpoint_sha256'] != PARENT_SHA or
            manifest['train_rows'] != list(TRAIN) or
            manifest['validation_rows'] != list(VALID) or
            manifest['protected_rows'] != list(PROTECTED) or
            manifest['budget'] != BUDGET or
            manifest['sany_jar_sha256'] != file_sha(args.jar)):
        raise ValueError('manifest identity or budget changed')
    if len(manifest['pairs']) != len(TRAIN) + len(VALID):
        raise ValueError('reference partition is incomplete')
    if any(pair['row'] in PROTECTED for pair in manifest['pairs']):
        raise ValueError('protected-row contamination')
    preflight = None
    if require_preflight:
        if not args.preflight or not args.preflight_sha256:
            raise ValueError('CPU tokenizer preflight is required')
        if file_sha(args.preflight) != args.preflight_sha256:
            raise ValueError('preflight hash mismatch')
        preflight = json.loads(args.preflight.read_text())
        if (preflight.get('manifest_sha256') != args.manifest_sha256 or
                preflight.get('all_tokenizers_exact') is not True or
                preflight.get('nonzero_eos_per_row') is not True):
            raise ValueError('CPU preflight identity or guards failed')
    return manifest, preflight


def prepare(args):
    raw = args.packet.read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError('frozen packet changed')
    packet = json.loads(raw)
    args.output.mkdir(parents=True, exist_ok=False)
    pairs = []
    for row in TRAIN + VALID:
        source = packet['rows'][row]
        if sha(source['response'].encode()) != source['response_sha256']:
            raise ValueError('reference hash mismatch')
        result = sany(source['response'], args.output / f'controls/{row}/positive', args.java, args.jar)
        if result['passed'] is not True:
            raise ValueError(f'positive SANY control failed for {row}: {result}')
        pairs.append(dict(
            row=row, id=source['id'], split='train' if row in TRAIN else 'validation',
            response_sha256=source['response_sha256']))
    manifest = dict(
        kind='fullmodule_wide_continuation_sft_v1', packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA, train_rows=list(TRAIN),
        validation_rows=list(VALID), protected_rows=list(PROTECTED), budget=BUDGET,
        sany_jar_sha256=file_sha(args.jar), pairs=pairs,
        clean_reference_targets_only=True, generated_feedback_loaded=False,
        replay_negatives_loaded=False, protected_targets_never_train=True,
        quality_claim=False, gate_claim=False, proof_claim=False,
        generalization_claim=False, tlc_claim=False, nonvacuity_claim=False)
    dump(args.output / 'manifest.json', manifest)
    print(json.dumps(dict(prepared=len(pairs), manifest_sha256=file_sha(args.output / 'manifest.json'))))


def token_weights(tokenizer, labels):
    weights = []
    structural = 0
    eos = 0
    for label in labels:
        if label == -100:
            weights.append(0.)
            continue
        token = tokenizer.decode([int(label)], clean_up_tokenization_spaces=False)
        is_structural = bool(set(token) & STRUCTURAL_CHARS)
        is_eos = int(label) in EOS_IDS
        structural += int(is_structural)
        eos += int(is_eos)
        weights.append(BUDGET['base_weight'] +
                       BUDGET['structural_weight'] * int(is_structural) +
                       BUDGET['eos_weight'] * int(is_eos))
    return weights, structural, eos


def exact_encodings(tokenizer, packet, manifest):
    records = []
    for pair in manifest['pairs']:
        row = pair['row']
        source = packet['rows'][row]
        enc = packet['encodings'][row]
        messages = [dict(role='user', content=source['prompt']),
                    dict(role='assistant', content=source['response'])]
        rendered = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=False)
        ids = tokenizer.encode(rendered, add_special_tokens=False)
        if ids != enc['input_ids'] or sha(source['response'].encode()) != pair['response_sha256']:
            raise ValueError(f'exact tokenizer/reference identity failed for row {row}')
        weights, structural, eos = token_weights(tokenizer, enc['labels'])
        if eos <= 0:
            raise ValueError(f'row {row} has no EOS target')
        records.append(dict(row=row, split=pair['split'], input_tokens=len(ids),
                            response_tokens=enc['response_tokens'],
                            input_ids_sha256=sha(json.dumps(ids, separators=(',', ':')).encode()),
                            weights_sha256=sha(json.dumps(weights, separators=(',', ':')).encode()),
                            structural_tokens=structural, eos_tokens=eos,
                            weighted_target_mass=sum(weights)))
    return records


def preflight(args):
    manifest, _ = verify_manifest(args)
    import transformers
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    packet = json.loads(args.packet.read_text())
    records = exact_encodings(tokenizer, packet, manifest)
    model_files = lineage.helpers.model_files(args.model)
    result = dict(
        schema=1, kind='fullmodule_wide_continuation_sft_cpu_preflight_v1',
        manifest_sha256=args.manifest_sha256, packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA, model_files=model_files,
        model_files_sha256=sha(json.dumps(model_files, sort_keys=True).encode()),
        train_rows=list(TRAIN), validation_rows=list(VALID), protected_rows=list(PROTECTED),
        records=records, all_tokenizers_exact=True,
        nonzero_eos_per_row=all(r['eos_tokens'] > 0 for r in records),
        clean_reference_rows=len(records), clean_reference_sany_pass=len(records),
        generated_feedback_loaded=False, replay_negatives_loaded=False,
        protected_targets_never_train=True, quality_claim=False, gate_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False,
        nonvacuity_claim=False)
    dump(args.output, result)
    print(json.dumps(dict(preflight='pass', rows=len(records), preflight_sha256=file_sha(args.output))))


class LoRALinear:
    def __new__(cls, base, rank, alpha):
        import torch
        import torch.nn as nn
        class Impl(nn.Module):
            def __init__(self, wrapped, r, a):
                super().__init__()
                self.base = wrapped
                device = wrapped.weight.device
                self.lora_A = nn.Parameter(torch.empty(r, wrapped.in_features, device=device, dtype=torch.float32))
                self.lora_B = nn.Parameter(torch.zeros(wrapped.out_features, r, device=device, dtype=torch.float32))
                nn.init.kaiming_uniform_(self.lora_A, a=math.sqrt(5))
                self.scaling = float(a) / float(r)

            def forward(self, values):
                import torch.nn.functional as F
                base = self.base(values)
                dtype = values.dtype if values.is_floating_point() else self.lora_A.dtype
                update = F.linear(F.linear(values, self.lora_A.to(dtype)), self.lora_B.to(dtype))
                return base + update * self.scaling
        return Impl(base, rank, alpha)


def inject_adapters(net):
    import torch
    net.requires_grad_(False)
    for index in BUDGET['adapter_layers']:
        layer = net.model.layers[index]
        for target in BUDGET['adapter_targets']:
            owner = layer.self_attn if target in {'q_proj', 'k_proj', 'v_proj', 'o_proj'} else layer.mlp
            module = getattr(owner, target)
            setattr(owner, target, LoRALinear(module, BUDGET['rank'], BUDGET['alpha']))
    selected = {}
    for name, parameter in net.named_parameters():
        if '.lora_A' in name or '.lora_B' in name:
            parameter.requires_grad_(True)
            selected[name] = parameter
    expected = len(BUDGET['adapter_layers']) * len(BUDGET['adapter_targets']) * 2
    if len(selected) != expected or not selected:
        raise ValueError('unexpected adapter parameterization')
    if any(parameter.dtype != torch.float32 for parameter in selected.values()):
        raise ValueError('adapter parameters must be fp32')
    return selected


def weighted_loss(net, enc, weights, context):
    import torch
    import torch.nn.functional as F
    ids = torch.tensor([enc['input_ids']], device='cuda')
    labels = torch.tensor([enc['labels']], device='cuda')
    with context():
        result = net(input_ids=ids, attention_mask=torch.ones_like(ids), labels=None, use_cache=False)
    logits = result.logits[:, :-1, :].float()
    targets = labels[:, 1:]
    flat_loss = F.cross_entropy(logits.reshape(-1, logits.shape[-1]), targets.reshape(-1), reduction='none')
    flat_weights = torch.tensor(weights[1:], device='cuda', dtype=torch.float32)
    mask = targets.reshape(-1) != -100
    mass = flat_weights[mask].sum()
    if not torch.isfinite(mass) or float(mass) <= 0:
        raise ValueError('invalid weighted target mass')
    loss = (flat_loss[mask] * flat_weights[mask]).sum() / mass
    if not torch.isfinite(loss):
        raise ValueError('nonfinite weighted response loss')
    return loss, dict(loss=float(loss.detach()), target_mass=float(mass.detach()))


def restore_adapters(selected, state):
    import torch
    if set(selected) != set(state):
        raise ValueError('adapter parameter names mismatch')
    with torch.no_grad():
        for name, parameter in selected.items():
            tensor = state[name]
            if tensor.dtype != torch.float32 or tensor.shape != parameter.shape or not torch.isfinite(tensor).all():
                raise ValueError('adapter tensor mismatch: ' + name)
            parameter.copy_(tensor)
    if not all(torch.equal(parameter.detach().cpu(), state[name])
               for name, parameter in selected.items()):
        raise ValueError('adapter restoration failed')


def generate_protected(net, tokenizer, packet, args, phase):
    results = []
    for row in PROTECTED:
        enc = packet['encodings'][row]
        decoded = multi.decode(net, tokenizer, enc,
                               forced_prefix=f'---- MODULE {MODULE_NAMES[row]} ----\n')
        result = dict(row=row, phase=phase, **decoded)
        result['sany'] = sany(decoded['raw_reply'], args.output / f'sany/{phase}/{row}', args.java, args.jar)
        dump(args.output / f'{phase}-row-{row}.json', result)
        results.append(result)
    return results


def train(args):
    import torch
    import transformers
    manifest, preflight = verify_manifest(args, require_preflight=True)
    if file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('exact v3 parent checkpoint required')
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 required')
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output / 'manifest.json', manifest)
    packet = json.loads(args.packet.read_text())
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    records = exact_encodings(tokenizer, packet, manifest)
    encodings = {record['row']: packet['encodings'][record['row']] for record in records}
    weights = {record['row']: token_weights(tokenizer, encodings[record['row']]['labels'])[0]
               for record in records}
    net = lineage.helpers.load_policy(args.model)
    saved = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    final_state = lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(args.model))
    net.requires_grad_(False)
    selected = inject_adapters(net)
    context = lambda: torch.autocast('cuda', dtype=torch.bfloat16)
    probe_ids = encodings[TRAIN[0]]['input_ids'][:64]
    with torch.no_grad(), context():
        base_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    # B is initialized to zero, so adapter injection must preserve the parent output.
    with torch.no_grad(), context():
        injected_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(base_probe, injected_probe):
        raise ValueError('zero-initialized adapter changed parent logits')
    del final_state, saved
    initial = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    net.zero_grad(set_to_none=True)
    longest = max(TRAIN, key=lambda row: len(encodings[row]['input_ids']))
    pre_loss, pre_metric = weighted_loss(net, encodings[longest], weights[longest], context)
    pre_loss.backward()
    gradient_norms = {}
    for name, parameter in selected.items():
        if parameter.grad is None or not torch.isfinite(parameter.grad).all():
            raise ValueError('missing/nonfinite adapter gradient: ' + name)
        gradient_norms[name] = float(parameter.grad.detach().float().norm())
    if not any(gradient_norms.values()):
        raise ValueError('all adapter gradients are zero')
    gradient_preflight = dict(index=longest, loss=pre_metric['loss'], target_mass=pre_metric['target_mass'],
                              gradient_norms=gradient_norms,
                              parameters_unchanged=all(torch.equal(parameter.detach().cpu(), initial[name])
                                                        for name, parameter in selected.items()))
    dump(args.output / 'gradient-preflight.json', gradient_preflight)
    net.zero_grad(set_to_none=True)
    if not gradient_preflight['parameters_unchanged']:
        raise ValueError('gradient preflight changed adapter parameters')
    before = generate_protected(net, tokenizer, packet, args, 'restored_parent')
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET['lr'], weight_decay=0., foreach=False)
    rng = random.Random(BUDGET['seed'])
    ledger = []
    started = time.monotonic()
    for step in range(BUDGET['steps']):
        if time.monotonic() - started >= BUDGET['training_seconds']:
            break
        chosen = rng.sample(list(TRAIN), BUDGET['accumulation'])
        optimizer.zero_grad(set_to_none=True)
        metrics = []
        for row in chosen:
            loss, metric = weighted_loss(net, encodings[row], weights[row], context)
            (loss / len(chosen)).backward()
            metrics.append(dict(row=row, **metric, structural_tokens=next(r['structural_tokens'] for r in records if r['row'] == row),
                                eos_tokens=next(r['eos_tokens'] for r in records if r['row'] == row)))
        norm = float(torch.nn.utils.clip_grad_norm_(selected.values(), 1., error_if_nonfinite=True))
        if not math.isfinite(norm) or norm <= 0:
            raise ValueError('invalid adapter gradient norm')
        optimizer.step()
        if any(not torch.isfinite(parameter).all() for parameter in selected.values()):
            raise ValueError('nonfinite adapter parameter')
        entry = dict(step=step + 1, gradient_norm=norm, examples=metrics)
        ledger.append(entry)
        with (args.output / 'steps.jsonl').open('a') as stream:
            stream.write(json.dumps(entry) + '\n')
        print(json.dumps(dict(step=step + 1, loss=sum(x['loss'] for x in metrics) / len(metrics))), flush=True)
    if len(ledger) != BUDGET['steps']:
        raise ValueError('training did not complete the admitted update count')
    state = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    delta = math.sqrt(sum(float((state[name] - initial[name]).double().square().sum()) for name in state))
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError('adapter parameters did not change')
    config = dict(
        schema=1, kind=manifest['kind'], algorithm=BUDGET['objective'],
        parent_sha256=PARENT_SHA, manifest_sha256=args.manifest_sha256,
        preflight_sha256=args.preflight_sha256, model_files=lineage.helpers.model_files(args.model),
        dtype_profile=PROFILE, budget=BUDGET, adapter_only=True,
        optimizer_state_stored=False, optimizer_resume_supported=False,
        protected_targets_never_train=True, generated_feedback_loaded=False,
        replay_negatives_loaded=False, quality_claim=False, gate_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False,
        nonvacuity_claim=False)
    checkpoint = args.output / 'policy_lora.pt'
    torch.save(dict(adapter_state=state, config=config, metrics=ledger), checkpoint,
               _use_new_zipfile_serialization=False)
    with torch.no_grad(), context():
        child_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    with torch.no_grad():
        for parameter in selected.values():
            parameter.zero_()
    reloaded = torch.load(checkpoint, map_location='cpu', weights_only=False)
    restore_adapters(selected, reloaded['adapter_state'])
    with torch.no_grad(), context():
        restored_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(child_probe, restored_probe):
        raise ValueError('adapter checkpoint logit reload mismatch')
    with torch.no_grad():
        tensor_exact = all(torch.equal(parameter.detach().cpu(), state[name])
                           for name, parameter in selected.items())
    if not tensor_exact:
        raise ValueError('adapter checkpoint tensor reload mismatch')
    after = generate_protected(net, tokenizer, packet, args, 'trained_child')
    receipt = dict(
        schema=1, complete=True, kind=manifest['kind'], updates=len(ledger),
        packet_sha256=PACKET_SHA, parent_checkpoint_sha256=PARENT_SHA,
        manifest_sha256=args.manifest_sha256, preflight_sha256=args.preflight_sha256,
        checkpoint_sha256=file_sha(checkpoint), checkpoint_bytes=checkpoint.stat().st_size,
        adapter_parameter_count=sum(parameter.numel() for parameter in selected.values()),
        adapter_parameter_tensors=len(selected), parameter_delta_l2=delta,
        gradient_preflight=gradient_preflight, before_protected=before, after_protected=after,
        reference_sany_pass_count=len(manifest['pairs']), train_rows=list(TRAIN),
        validation_rows=list(VALID), protected_rows=list(PROTECTED),
        reload_tensors_exact=True, reload_logits_exact=True, adapter_only=True,
        optimizer_state_stored=False, optimizer_resume_supported=False,
        generated_feedback_loaded=False, replay_negatives_loaded=False,
        protected_targets_never_train=True, quality_claim=False, gate_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False,
        nonvacuity_claim=False, tlaps_claim=False)
    dump(args.output / 'receipt.json', receipt)
    print(json.dumps(dict(complete=True, updates=len(ledger), parameter_delta_l2=delta,
                          checkpoint_sha256=receipt['checkpoint_sha256'])), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('prepare', 'preflight', 'train'))
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--jar', type=Path, required=True)
    parser.add_argument('--java', default='java')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--manifest-sha256')
    parser.add_argument('--preflight', type=Path)
    parser.add_argument('--preflight-sha256')
    parser.add_argument('--checkpoint', type=Path)
    parser.add_argument('--model', type=Path)
    args = parser.parse_args()
    if args.mode in ('preflight', 'train') and not all((args.manifest, args.manifest_sha256, args.model)):
        parser.error(f'{args.mode} requires --manifest, --manifest-sha256 and --model')
    if args.mode == 'train' and not all((args.preflight, args.preflight_sha256, args.checkpoint)):
        parser.error('train requires --preflight, --preflight-sha256 and --checkpoint')
    if args.mode == 'prepare':
        prepare(args)
    elif args.mode == 'preflight':
        preflight(args)
    else:
        train(args)
