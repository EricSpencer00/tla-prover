"""Full-sequence contrastive LoRA diagnostic over deterministic SANY corruptions.

Clean references and deterministic one-edit corruptions are screened by SANY on
non-protected rows. Training minimizes weighted clean-response NLL while making
the complete corrupted response less likely by a fixed margin. No generated
feedback, verifier reward, or protected training is used.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multilayer_structural_sft_train as helper

PACKET_SHA = helper.PACKET_SHA
PARENT_SHA = helper.PARENT_SHA
TRAIN = helper.TRAIN
VALID = helper.VALID
PROTECTED = helper.PROTECTED
MODULE_NAMES = helper.MODULE_NAMES
EOS_IDS = helper.EOS_IDS
STRUCTURAL_CHARS = helper.STRUCTURAL_CHARS
PROFILE = helper.PROFILE
BUDGET = dict(
    steps=16, accumulation=2, lr=2e-4, rank=8, alpha=16,
    base_weight=1., structural_weight=4., eos_weight=8., margin=.25,
    contrastive_weight=.5, seed=20260915, training_seconds=480,
    max_new_tokens=2048, generation_seconds=60, sany_seconds=30,
    adapter_layers=[28, 29, 30, 31], adapter_targets=['q_proj', 'v_proj'],
    objective='fullsequence_clean_vs_sany_screened_corruption_contrastive_lora')


def sha(data):
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024**2), b''):
            h.update(chunk)
    return h.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def corruptions(text):
    result = []
    patterns = [
        ('definition_equals', r'(?m)^(\w+) ==', lambda m: m[1] + ' ='),
        ('membership_keyword', r'\\in\b', lambda m: 'IN'),
        ('declaration_comma', r'(?m)^(VARIABLES? [^\n,]+),', lambda m: m[1]),
        ('config_in_module', r'(?m)^={4,}\s*$', lambda m: 'SPECIFICATION Init\n' + m[0]),
    ]
    for kind, pattern, replace in patterns:
        bad, count = re.subn(pattern, replace, text, count=1)
        if count:
            result.append((kind, bad))
    return result


def prepare(args):
    if sha(args.packet.read_bytes()) != PACKET_SHA:
        raise ValueError('frozen packet changed')
    packet = json.loads(args.packet.read_text())
    args.output.mkdir(parents=True, exist_ok=False)
    pairs = []
    for row in TRAIN + VALID:
        source = packet['rows'][row]
        if sha(source['response']) != source['response_sha256']:
            raise ValueError('reference hash mismatch')
        positive = helper.sany(source['response'], args.output / f'controls/{row}/positive', args.java, args.jar)
        if positive['passed'] is not True:
            raise ValueError(f'positive SANY control failed for {row}: {positive}')
        for kind, negative in corruptions(source['response']):
            checked = helper.sany(negative, args.output / f'controls/{row}/{kind}', args.java, args.jar)
            if checked['passed'] is not False:
                raise ValueError(f'negative SANY control not rejected: {row}/{kind}')
            pairs.append(dict(row=row, id=source['id'], split='train' if row in TRAIN else 'validation',
                              kind=kind, positive_sha256=source['response_sha256'],
                              negative_sha256=sha(negative), negative=negative))
    if len(pairs) != 87:
        raise ValueError(f'unexpected screened corruption count: {len(pairs)}')
    manifest = dict(kind='fullsequence_contrastive_lora_v1', packet_sha256=PACKET_SHA,
                    parent_checkpoint_sha256=PARENT_SHA, train_rows=list(TRAIN), validation_rows=list(VALID),
                    protected_rows=list(PROTECTED), budget=BUDGET, sany_jar_sha256=file_sha(args.jar),
                    pairs=pairs, clean_reference_targets_only=True, corruption_targets_deterministic=True,
                    generated_feedback_loaded=False, replay_negatives_loaded=False,
                    protected_targets_never_train=True, quality_claim=False, gate_claim=False,
                    proof_claim=False, generalization_claim=False, tlc_claim=False, nonvacuity_claim=False)
    dump(args.output / 'manifest.json', manifest)
    print(json.dumps(dict(prepared=len(pairs), manifest_sha256=file_sha(args.output / 'manifest.json'))))


def token_weights(tokenizer, labels):
    values = []
    structural = eos = 0
    for label in labels:
        if label == -100:
            values.append(0.)
            continue
        token = tokenizer.decode([int(label)], clean_up_tokenization_spaces=False)
        structural += int(bool(set(token) & STRUCTURAL_CHARS))
        eos += int(int(label) in EOS_IDS)
        values.append(BUDGET['base_weight'] + BUDGET['structural_weight'] * int(bool(set(token) & STRUCTURAL_CHARS)) +
                      BUDGET['eos_weight'] * int(int(label) in EOS_IDS))
    return values, structural, eos


def verify_manifest(args, require_preflight=False):
    if sha(args.packet.read_bytes()) != PACKET_SHA or file_sha(args.manifest) != args.manifest_sha256:
        raise ValueError('packet or manifest hash mismatch')
    manifest = json.loads(args.manifest.read_text())
    if (manifest.get('kind') != 'fullsequence_contrastive_lora_v1' or
            manifest['packet_sha256'] != PACKET_SHA or manifest['parent_checkpoint_sha256'] != PARENT_SHA or
            manifest['train_rows'] != list(TRAIN) or manifest['validation_rows'] != list(VALID) or
            manifest['protected_rows'] != list(PROTECTED) or manifest['budget'] != BUDGET or
            manifest['sany_jar_sha256'] != file_sha(args.jar) or len(manifest['pairs']) != 87):
        raise ValueError('manifest identity, budget or partition changed')
    if any(pair['row'] in PROTECTED for pair in manifest['pairs']):
        raise ValueError('protected-row contamination')
    preflight = None
    if require_preflight:
        if not args.preflight or not args.preflight_sha256 or file_sha(args.preflight) != args.preflight_sha256:
            raise ValueError('CPU preflight is missing or hash-mismatched')
        preflight = json.loads(args.preflight.read_text())
        if (preflight.get('manifest_sha256') != args.manifest_sha256 or
                preflight.get('all_tokenizers_exact') is not True or
                preflight.get('all_corruption_tokenizers_exact') is not True or
                preflight.get('nonzero_eos_per_row') is not True):
            raise ValueError('CPU preflight guards failed')
    return manifest, preflight


def build_pairs(tokenizer, packet, manifest):
    result = []
    for pair in manifest['pairs']:
        row = pair['row']
        source = packet['rows'][row]
        frozen = packet['encodings'][row]
        prompt = tokenizer.apply_chat_template([dict(role='user', content=source['prompt'])],
                                                tokenize=False, add_generation_prompt=True)
        prompt_ids = tokenizer.encode(prompt, add_special_tokens=False)
        if prompt_ids != frozen['input_ids'][:frozen['prompt_tokens']]:
            raise ValueError(f'prompt tokenizer mismatch for {row}')
        def encode(answer):
            rendered = tokenizer.apply_chat_template(
                [dict(role='user', content=source['prompt']), dict(role='assistant', content=answer)],
                tokenize=False, add_generation_prompt=False)
            return tokenizer.encode(rendered, add_special_tokens=False)
        good_ids = encode(source['response'])
        bad_ids = encode(pair['negative'])
        if good_ids != frozen['input_ids'] or bad_ids[:len(prompt_ids)] != prompt_ids:
            raise ValueError(f'full-sequence tokenizer mismatch for {row}/{pair["kind"]}')
        if sha(pair['negative']) != pair['negative_sha256']:
            raise ValueError('negative text hash mismatch')
        good_weights, gs, ge = token_weights(tokenizer, frozen['labels'])
        bad_labels = [-100] * len(prompt_ids) + bad_ids[len(prompt_ids):]
        bad_weights, bs, be = token_weights(tokenizer, bad_labels)
        if ge <= 0 or be <= 0:
            raise ValueError(f'missing EOS target in {row}/{pair["kind"]}')
        result.append(dict(row=row, kind=pair['kind'], split=pair['split'],
                          good=dict(input_ids=good_ids, labels=frozen['labels'], weights=good_weights),
                          bad=dict(input_ids=bad_ids, labels=bad_labels, weights=bad_weights),
                          good_structural_tokens=gs, bad_structural_tokens=bs,
                          good_eos_tokens=ge, bad_eos_tokens=be))
    return result


def preflight(args):
    manifest, _ = verify_manifest(args)
    import transformers
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    packet = json.loads(args.packet.read_text())
    pairs = build_pairs(tokenizer, packet, manifest)
    model_files = lineage.helpers.model_files(args.model)
    result = dict(schema=1, kind='fullsequence_contrastive_lora_cpu_preflight_v1',
                  manifest_sha256=args.manifest_sha256, packet_sha256=PACKET_SHA,
                  parent_checkpoint_sha256=PARENT_SHA, model_files=model_files,
                  model_files_sha256=sha(json.dumps(model_files, sort_keys=True).encode()),
                  train_rows=list(TRAIN), validation_rows=list(VALID), protected_rows=list(PROTECTED),
                  records=[dict(row=x['row'], kind=x['kind'], split=x['split'],
                                good_input_tokens=len(x['good']['input_ids']),
                                bad_input_tokens=len(x['bad']['input_ids']),
                                good_structural_tokens=x['good_structural_tokens'],
                                bad_structural_tokens=x['bad_structural_tokens'],
                                good_eos_tokens=x['good_eos_tokens'], bad_eos_tokens=x['bad_eos_tokens']) for x in pairs],
                  all_tokenizers_exact=True, all_corruption_tokenizers_exact=True,
                  nonzero_eos_per_row=all(x['good_eos_tokens'] > 0 and x['bad_eos_tokens'] > 0 for x in pairs),
                  clean_reference_rows=22, clean_reference_sany_pass=22,
                  corruption_pairs=87, corruption_sany_screened=87,
                  generated_feedback_loaded=False, replay_negatives_loaded=False,
                  protected_targets_never_train=True, quality_claim=False, gate_claim=False,
                  proof_claim=False, generalization_claim=False, tlc_claim=False, nonvacuity_claim=False)
    dump(args.output, result)
    print(json.dumps(dict(preflight='pass', rows=len(pairs), preflight_sha256=file_sha(args.output))))


def weighted_nll(net, example, context):
    import torch
    import torch.nn.functional as F
    ids = torch.tensor([example['input_ids']], device='cuda')
    labels = torch.tensor([example['labels']], device='cuda')
    with context():
        logits = net(input_ids=ids, attention_mask=torch.ones_like(ids), labels=None,
                     use_cache=False).logits[:, :-1].float()
    targets = labels[:, 1:]
    values = F.cross_entropy(logits.reshape(-1, logits.shape[-1]), targets.reshape(-1), reduction='none')
    weights = torch.tensor(example['weights'][1:], device='cuda', dtype=torch.float32)
    mask = targets.reshape(-1) != -100
    mass = weights[mask].sum()
    if not torch.isfinite(mass) or float(mass) <= 0:
        raise ValueError('invalid weighted target mass')
    loss = (values[mask] * weights[mask]).sum() / mass
    if not torch.isfinite(loss):
        raise ValueError('nonfinite weighted NLL')
    return loss, float(mass.detach())


def train(args):
    import random
    import torch
    import transformers
    manifest, _ = verify_manifest(args, require_preflight=True)
    if file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('exact v3 parent checkpoint required')
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 required')
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output / 'manifest.json', manifest)
    packet = json.loads(args.packet.read_text())
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    pairs = build_pairs(tokenizer, packet, manifest)
    records = [p for p in pairs if p['split'] == 'train']
    net = lineage.helpers.load_policy(args.model)
    saved = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(args.model))
    del saved
    context = lambda: torch.autocast('cuda', dtype=torch.bfloat16)
    probe_ids = records[0]['good']['input_ids'][:64]
    with torch.no_grad(), context():
        base_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    selected = helper.inject_adapters(net)
    with torch.no_grad(), context():
        injected_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(base_probe, injected_probe):
        raise ValueError('zero-initialized adapter changed parent logits')
    initial = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    net.zero_grad(set_to_none=True)
    longest = max(records, key=lambda x: len(x['good']['input_ids']))
    probe_loss, probe_mass = weighted_nll(net, longest['good'], context)
    probe_loss.backward()
    gradient_norms = {name: float(parameter.grad.detach().float().norm())
                      for name, parameter in selected.items()
                      if parameter.grad is not None and torch.isfinite(parameter.grad).all()}
    if len(gradient_norms) != len(selected) or not any(gradient_norms.values()):
        raise ValueError('missing/nonfinite adapter gradient')
    preflight = dict(row=longest['row'], loss=float(probe_loss.detach()), target_mass=probe_mass,
                     gradient_norms=gradient_norms, parameters_unchanged=all(
                         torch.equal(parameter.detach().cpu(), initial[name]) for name, parameter in selected.items()))
    dump(args.output / 'gradient-preflight.json', preflight)
    net.zero_grad(set_to_none=True)
    if not preflight['parameters_unchanged']:
        raise ValueError('gradient preflight changed parameters')
    before = helper.generate_protected(net, tokenizer, packet, args, 'restored_parent')
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET['lr'], weight_decay=0., foreach=False)
    rng = random.Random(BUDGET['seed'])
    ledger = []
    for step in range(BUDGET['steps']):
        chosen = rng.sample(records, BUDGET['accumulation'])
        optimizer.zero_grad(set_to_none=True)
        metrics = []
        for pair in chosen:
            good_loss, good_mass = weighted_nll(net, pair['good'], context)
            bad_loss, bad_mass = weighted_nll(net, pair['bad'], context)
            gap = bad_loss - good_loss
            loss = good_loss + BUDGET['contrastive_weight'] * torch.nn.functional.softplus(BUDGET['margin'] - gap)
            if not torch.isfinite(loss):
                raise ValueError('nonfinite contrastive loss')
            (loss / len(chosen)).backward()
            metrics.append(dict(row=pair['row'], kind=pair['kind'], loss=float(loss.detach()),
                                good_nll=float(good_loss.detach()), bad_nll=float(bad_loss.detach()),
                                nll_gap=float(gap.detach()), good_mass=good_mass, bad_mass=bad_mass))
        norm = float(torch.nn.utils.clip_grad_norm_(selected.values(), 1., error_if_nonfinite=True))
        if not math.isfinite(norm) or norm <= 0:
            raise ValueError('invalid contrastive gradient')
        optimizer.step()
        if any(not torch.isfinite(parameter).all() for parameter in selected.values()):
            raise ValueError('nonfinite adapter parameter')
        entry = dict(step=step + 1, gradient_norm=norm, examples=metrics)
        ledger.append(entry)
        with (args.output / 'steps.jsonl').open('a') as stream:
            stream.write(json.dumps(entry) + '\n')
        print(json.dumps(dict(step=step + 1, loss=sum(x['loss'] for x in metrics) / len(metrics))), flush=True)
    state = {name: parameter.detach().cpu().clone() for name, parameter in selected.items()}
    delta = math.sqrt(sum(float((state[name] - initial[name]).double().square().sum()) for name in state))
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError('adapter parameters did not change')
    config = dict(schema=1, kind=manifest['kind'], algorithm=BUDGET['objective'], parent_sha256=PARENT_SHA,
                  manifest_sha256=args.manifest_sha256, preflight_sha256=args.preflight_sha256,
                  model_files=lineage.helpers.model_files(args.model), dtype_profile=PROFILE, budget=BUDGET,
                  adapter_only=True, optimizer_state_stored=False, optimizer_resume_supported=False,
                  protected_targets_never_train=True, generated_feedback_loaded=False,
                  replay_negatives_loaded=False, quality_claim=False, gate_claim=False, proof_claim=False,
                  generalization_claim=False, tlc_claim=False, nonvacuity_claim=False)
    checkpoint = args.output / 'policy_lora.pt'
    torch.save(dict(adapter_state=state, config=config, metrics=ledger), checkpoint, _use_new_zipfile_serialization=False)
    with torch.no_grad(), context():
        child_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
        for parameter in selected.values():
            parameter.zero_()
    reloaded = torch.load(checkpoint, map_location='cpu', weights_only=False)
    helper.restore_adapters(selected, reloaded['adapter_state'])
    with torch.no_grad(), context():
        restored_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(child_probe, restored_probe):
        raise ValueError('adapter checkpoint logit reload mismatch')
    if not all(torch.equal(parameter.detach().cpu(), state[name]) for name, parameter in selected.items()):
        raise ValueError('adapter checkpoint tensor reload mismatch')
    after = helper.generate_protected(net, tokenizer, packet, args, 'trained_child')
    receipt = dict(schema=1, complete=True, kind=manifest['kind'], updates=len(ledger),
                   packet_sha256=PACKET_SHA, parent_checkpoint_sha256=PARENT_SHA,
                   manifest_sha256=args.manifest_sha256, preflight_sha256=args.preflight_sha256,
                   checkpoint_sha256=file_sha(checkpoint), checkpoint_bytes=checkpoint.stat().st_size,
                   adapter_parameter_count=sum(parameter.numel() for parameter in selected.values()),
                   adapter_parameter_tensors=len(selected), parameter_delta_l2=delta,
                   gradient_preflight=preflight, before_protected=before, after_protected=after,
                   reference_sany_pass_count=22, train_rows=list(TRAIN), validation_rows=list(VALID),
                   protected_rows=list(PROTECTED), reload_tensors_exact=True, reload_logits_exact=True,
                   adapter_only=True, optimizer_state_stored=False, optimizer_resume_supported=False,
                   generated_feedback_loaded=False, replay_negatives_loaded=False,
                   protected_targets_never_train=True, quality_claim=False, gate_claim=False, proof_claim=False,
                   generalization_claim=False, tlc_claim=False, nonvacuity_claim=False, tlaps_claim=False)
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
