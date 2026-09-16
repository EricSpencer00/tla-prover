"""Bounded broad clean-reference SFT for full-module TLA+ generation.

This diagnostic tests whether source-separated W4 diversity can improve the
exact protected generation contract after several narrow interventions failed.
Only immutable non-protected W4 references outside the frozen validation rows
are used as training targets.  A fixed subset of the earlier narrow training
rows is retained as anchors.  No generated feedback, replay negatives,
protected targets, or protected model selection enters training.
"""

import argparse
import hashlib
import json
import math
import random
import re
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_sany_feedback_correction_train as common
from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi

PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
PARENT_SHA = '87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511'
W4_ROWS = tuple(i for i in range(42, 169))
VALID = (59, 60, 61, 62, 63, 64)
PROTECTED = (47, 107)
TRAIN = tuple(i for i in W4_ROWS if i not in VALID and i not in PROTECTED)
ANCHORS = tuple(i for i in range(42, 59) if i != 47)
REFERENCE_ROWS = TRAIN + VALID
MODULE_NAMES = {47: 'W4Od2m7p4t2', 107: 'W4Od3m0p0t0'}
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'

BUDGET = dict(
    steps=32,
    accumulation=1,
    lr=1e-6,
    rank=4,
    alpha=8,
    anchor_probability=0.35,
    seed=20260916,
    training_seconds=480,
    max_new_tokens=2048,
    generation_seconds=60,
    sany_seconds=30,
    adapter_layers=[28, 29, 30, 31],
    adapter_targets=['q_proj', 'k_proj', 'v_proj', 'o_proj',
                     'gate_proj', 'up_proj', 'down_proj'],
    objective='broad_source_separated_clean_w4_sft_with_retention_anchors',
)

multi.BUDGET.update(
    max_new_tokens=BUDGET['max_new_tokens'],
    item_seconds=BUDGET['generation_seconds'],
    sany_seconds=BUDGET['sany_seconds'],
    train_only=False,
    eval_rows=list(PROTECTED),
    gate_claim=False,
    quality_claim=False,
    generalization_claim=False,
    proof_claim=False,
    tlc_claim=False,
    nonvacuity_claim=False,
)


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


def exact_chat(tokenizer, prompt, response):
    rendered = tokenizer.apply_chat_template(
        [dict(role='user', content=prompt), dict(role='assistant', content=response)],
        tokenize=False, add_generation_prompt=False)
    ids = tokenizer.encode(rendered, add_special_tokens=False)
    prompt_rendered = tokenizer.apply_chat_template(
        [dict(role='user', content=prompt)], tokenize=False, add_generation_prompt=True)
    prompt_ids = tokenizer.encode(prompt_rendered, add_special_tokens=False)
    if ids[:len(prompt_ids)] != prompt_ids:
        raise ValueError('assistant response is not an exact chat-template suffix')
    labels = [-100] * len(prompt_ids) + ids[len(prompt_ids):]
    return dict(input_ids=ids, labels=labels, prompt_tokens=len(prompt_ids),
                response_tokens=len(ids) - len(prompt_ids))


def packet_rows(raw):
    if sha(raw) != PACKET_SHA:
        raise ValueError('frozen packet changed')
    packet = json.loads(raw)
    rows, encodings = packet.get('rows'), packet.get('encodings')
    if not isinstance(rows, list) or not isinstance(encodings, list) or len(rows) != 169 or len(encodings) != 169:
        raise ValueError('complete immutable packet required')
    if set(TRAIN) & set(VALID) or set(TRAIN) & set(PROTECTED) or set(VALID) & set(PROTECTED):
        raise ValueError('row partitions overlap')
    for row in W4_ROWS:
        source, encoding = rows[row], encodings[row]
        if not source.get('id', '').startswith('w4-fullmodule:') or source.get('split') != 'train':
            raise ValueError(f'row {row} is not an exact W4 training reference')
        if (sha(source.get('prompt', '').encode()) != source.get('prompt_sha256') or
                sha(source.get('response', '').encode()) != source.get('response_sha256') or
                encoding.get('id') != source.get('id') or
                encoding.get('prompt_sha256') != source.get('prompt_sha256') or
                encoding.get('response_sha256') != source.get('response_sha256')):
            raise ValueError(f'row {row} text identity mismatch')
    return packet, rows


def reference_rows(packet, rows):
    return [dict(row=i, id=rows[i]['id'], split='train', prompt_sha256=rows[i]['prompt_sha256'],
                 response_sha256=rows[i]['response_sha256'], train=i in TRAIN,
                 validation=i in VALID, anchor=i in ANCHORS)
            for i in REFERENCE_ROWS]


def verify_manifest(args, require_preflight=False):
    if file_sha(args.packet) != PACKET_SHA:
        raise ValueError('frozen packet mismatch')
    if file_sha(args.manifest) != args.manifest_sha256:
        raise ValueError('manifest hash mismatch')
    manifest = json.loads(args.manifest.read_bytes())
    if (manifest.get('kind') != 'fullmodule_broad_clean_sft_v1' or
            manifest.get('packet_sha256') != PACKET_SHA or
            manifest.get('parent_checkpoint_sha256') != PARENT_SHA or
            manifest.get('train_rows') != list(TRAIN) or
            manifest.get('validation_rows') != list(VALID) or
            manifest.get('protected_rows') != list(PROTECTED) or
            manifest.get('anchor_rows') != list(ANCHORS) or
            manifest.get('budget') != BUDGET or
            manifest.get('reference_count') != len(REFERENCE_ROWS)):
        raise ValueError('manifest identity or budget changed')
    if any(r['row'] in PROTECTED for r in manifest.get('references', [])):
        raise ValueError('protected row contamination')
    if len(manifest.get('references', [])) != len(REFERENCE_ROWS):
        raise ValueError('complete non-protected W4 reference inventory required')
    preflight = None
    if require_preflight:
        if not args.preflight or not args.preflight_sha256:
            raise ValueError('CPU tokenizer preflight required')
        if file_sha(args.preflight) != args.preflight_sha256:
            raise ValueError('preflight hash mismatch')
        preflight = json.loads(args.preflight.read_bytes())
        if (preflight.get('manifest_sha256') != args.manifest_sha256 or
                preflight.get('all_tokenizers_exact') is not True or
                preflight.get('nonzero_eos_per_row') is not True):
            raise ValueError('CPU preflight guards failed')
    return manifest, preflight


def prepare(args):
    packet, rows = packet_rows(args.packet.read_bytes())
    args.output.mkdir(parents=True, exist_ok=False)
    controls = []
    for row in REFERENCE_ROWS:
        source = rows[row]
        result = common.sany_check(source['response'], args.output / f'controls/{row}', args.java, args.jar)
        if result.get('passed') is not True:
            raise ValueError(f'reference SANY control failed for row {row}: {result}')
        controls.append(dict(row=row, status=result['status']))
    manifest = dict(
        schema=1,
        kind='fullmodule_broad_clean_sft_v1',
        packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA,
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        anchor_rows=list(ANCHORS),
        reference_count=len(REFERENCE_ROWS),
        references=reference_rows(packet, rows),
        budget=BUDGET,
        sany_jar_sha256=file_sha(args.jar),
        controls=controls,
        clean_reference_targets_only=True,
        generated_feedback_loaded=False,
        replay_negatives_loaded=False,
        protected_targets_never_train=True,
        validation_targets_never_train=True,
        training_authorized=True,
        quality_claim=False,
        model_improvement_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(args.output / 'manifest.json', manifest)
    dump(args.output / 'prepare-controls.json', dict(
        controls_ok=True,
        reference_controls=len(REFERENCE_ROWS),
        train_reference_count=len(TRAIN),
        validation_reference_count=len(VALID),
        protected_rows=list(PROTECTED),
        protected_rows_touched=False,
    ))
    print(json.dumps(dict(prepared=len(REFERENCE_ROWS), train=len(TRAIN), validation=len(VALID),
                          manifest_sha256=file_sha(args.output / 'manifest.json'))))


def preflight(args):
    manifest, _ = verify_manifest(args)
    import transformers
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    packet, rows = packet_rows(args.packet.read_bytes())
    records = []
    for row in REFERENCE_ROWS:
        source = rows[row]
        enc = exact_chat(tokenizer, source['prompt'], source['response'])
        records.append(dict(row=row, train=row in TRAIN, validation=row in VALID,
                            anchor=row in ANCHORS, prompt_tokens=enc['prompt_tokens'],
                            response_tokens=enc['response_tokens'],
                            input_ids_sha256=sha(json.dumps(enc['input_ids'], separators=(',', ':')).encode()),
                            labels_sha256=sha(json.dumps(enc['labels'], separators=(',', ':')).encode())))
    model_files = lineage.helpers.model_files(args.model)
    result = dict(
        schema=1,
        kind='fullmodule_broad_clean_sft_cpu_preflight_v1',
        manifest_sha256=args.manifest_sha256,
        packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA,
        model_files=model_files,
        model_files_sha256=sha(json.dumps(model_files, sort_keys=True).encode()),
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        anchor_rows=list(ANCHORS),
        references=records,
        all_tokenizers_exact=True,
        nonzero_eos_per_row=all(r['response_tokens'] > 0 for r in records),
        reference_count=len(records),
        train_reference_count=len(TRAIN),
        validation_reference_count=len(VALID),
        generated_feedback_loaded=False,
        replay_negatives_loaded=False,
        protected_targets_never_train=True,
        validation_targets_never_train=True,
        model_weights_loaded=False,
        cuda_touched=False,
        training_authorized=True,
        quality_claim=False,
        model_improvement_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(args.output, result)
    print(json.dumps(dict(preflight='pass', references=len(records), train=len(TRAIN),
                          validation=len(VALID), preflight_sha256=file_sha(args.output))))


class LoRALinear:
    def __new__(cls, base, rank, alpha):
        import torch.nn as nn
        import torch.nn.functional as F
        import torch

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
                base = self.base(values)
                dtype = values.dtype if values.is_floating_point() else self.lora_A.dtype
                update = F.linear(F.linear(values, self.lora_A.to(dtype)), self.lora_B.to(dtype))
                return base + update * self.scaling

        return Impl(base, rank, alpha)


def inject_adapters(net):
    net.requires_grad_(False)
    for index in BUDGET['adapter_layers']:
        layer = net.model.layers[index]
        for target in BUDGET['adapter_targets']:
            owner = layer.self_attn if target in {'q_proj', 'k_proj', 'v_proj', 'o_proj'} else layer.mlp
            setattr(owner, target, LoRALinear(getattr(owner, target), BUDGET['rank'], BUDGET['alpha']))
    selected = {name: p for name, p in net.named_parameters()
                if '.lora_A' in name or '.lora_B' in name}
    expected = len(BUDGET['adapter_layers']) * len(BUDGET['adapter_targets']) * 2
    if len(selected) != expected or any(p.dtype != __import__('torch').float32 for p in selected.values()):
        raise ValueError('unexpected adapter parameterization')
    return selected


def validate_inputs(args):
    manifest, preflight_value = verify_manifest(args, require_preflight=True)
    if file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('exact parent checkpoint required')
    packet, rows = packet_rows(args.packet.read_bytes())
    if preflight_value.get('reference_count') != len(REFERENCE_ROWS):
        raise ValueError('preflight reference count drift')
    return manifest, packet, rows


def train(args):
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(BUDGET['seed'])
    random.seed(BUDGET['seed'])
    manifest, packet, rows = validate_inputs(args)
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output / 'manifest.json', manifest)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    encodings = {row: exact_chat(tokenizer, rows[row]['prompt'], rows[row]['response'])
                 for row in TRAIN + VALID + PROTECTED}
    net = lineage.helpers.load_policy(args.model)
    saved = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(args.model))
    del saved
    selected = inject_adapters(net)
    context = lambda: torch.autocast('cuda', dtype=torch.bfloat16)
    probe_ids = encodings[ANCHORS[0]]['input_ids'][:64]
    with torch.no_grad(), context():
        parent_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
        injected_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(parent_probe, injected_probe):
        raise ValueError('zero-initialized adapter changed parent logits')
    initial = {name: p.detach().cpu().clone() for name, p in selected.items()}

    tasks = {row: multi.stage_task(multi.checker_task(packet, rows[row]), args.output, str(row))
             for row in PROTECTED}
    sany_identity = multi.sany.identity(list(tasks.values()))

    def generate(row, phase):
        forced = f'---- MODULE {MODULE_NAMES[row]} ----\n'
        decoded = multi.decode(net, tokenizer, encodings[row], forced_prefix=forced)
        result = dict(row=row, phase=phase, **decoded)
        result['sany'] = multi.sany.check(
            tasks[row], decoded['raw_reply'], args.output / f'sany/{phase}/{row}', sany_identity,
            timeout=BUDGET['sany_seconds'])
        dump(args.output / f'{phase}-row-{row}.json', result)
        return result

    before = [generate(row, 'restored_parent') for row in PROTECTED]

    def validation_metrics():
        values = []
        for row in VALID:
            loss, metric = common.teacher_loss(net, encodings[row], context=context)
            values.append(dict(row=row, **metric))
            del loss
        return values

    validation_before = validation_metrics()
    for parameter in selected.values():
        parameter.requires_grad_(True)
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET['lr'], weight_decay=0., foreach=False)
    rng = random.Random(BUDGET['seed'])
    broad_only = [row for row in TRAIN if row not in ANCHORS]
    ledger = []
    started = time.monotonic()
    for step in range(1, BUDGET['steps'] + 1):
        if time.monotonic() - started >= BUDGET['training_seconds']:
            break
        row = rng.choice(ANCHORS if rng.random() < BUDGET['anchor_probability'] else broad_only)
        optimizer.zero_grad(set_to_none=True)
        loss, metric = common.teacher_loss(net, encodings[row], context=context)
        loss.backward()
        grad = float(torch.nn.utils.clip_grad_norm_(selected.values(), 1., error_if_nonfinite=True))
        if not math.isfinite(grad) or grad <= 0:
            raise ValueError('nonfinite/zero broad SFT gradient')
        optimizer.step()
        if any(not bool(torch.isfinite(p).all()) for p in selected.values()):
            raise ValueError('nonfinite adapter after broad SFT update')
        entry = dict(step=step, row=row, anchor=row in ANCHORS, **metric, gradient_norm=grad)
        ledger.append(entry)
        with (args.output / 'steps.jsonl').open('a') as stream:
            stream.write(json.dumps(entry) + '\n')
        print(json.dumps(entry), flush=True)
    if len(ledger) != BUDGET['steps']:
        raise ValueError('executed update count differs from admitted broad SFT budget')

    state = {name: p.detach().cpu().clone() for name, p in selected.items()}
    delta = sum(float((state[name] - initial[name]).double().square().sum()) for name in state) ** .5
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError('broad SFT adapter did not change finitely')
    config = dict(kind=manifest['kind'], model_files=lineage.helpers.model_files(args.model),
                  dtype_profile=PROFILE, parent_sha256=PARENT_SHA,
                  manifest_sha256=args.manifest_sha256, budget=BUDGET,
                  optimizer_state_stored=False, optimizer_resume_supported=False)
    checkpoint = args.output / 'policy_lora.pt'
    common.save_exact(torch, state, config, ledger, checkpoint)
    with torch.no_grad(), context():
        child_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
        for parameter in selected.values():
            parameter.zero_()
        reloaded = torch.load(checkpoint, map_location='cpu', weights_only=False)
        common.restore_adapters(selected, reloaded['trainable_state'])
        reload_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(child_probe, reload_probe):
        raise ValueError('checkpoint logit reload mismatch')
    reload_tensors_exact = all(torch.equal(p.detach().cpu(), state[n]) for n, p in selected.items())
    if not reload_tensors_exact:
        raise ValueError('checkpoint tensor reload mismatch')
    for parameter in selected.values():
        parameter.requires_grad_(False)
    del reloaded, optimizer
    validation_after = validation_metrics()
    after = [generate(row, 'trained_child') for row in PROTECTED]
    receipt = dict(
        complete=True,
        kind=manifest['kind'],
        updates=len(ledger),
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        anchor_rows=list(ANCHORS),
        protected_rows=list(PROTECTED),
        parameter_delta_l2=delta,
        child_sha256=file_sha(checkpoint),
        adapter_parameter_count=sum(p.numel() for p in selected.values()),
        adapter_parameter_tensors=len(selected),
        reload_tensors_exact=reload_tensors_exact,
        reload_logits_exact=True,
        preflight_sha256=file_sha(args.preflight),
        sany_identity=sany_identity,
        before_protected=before,
        after_protected=after,
        validation_before=validation_before,
        validation_after=validation_after,
        generated_feedback_used_for_training=False,
        replay_negatives_loaded=False,
        protected_targets_never_train=True,
        validation_targets_never_train=True,
        clean_reference_targets_only=True,
        model_improvement_claim=False,
        quality_claim=False,
        gate_claim=False,
        proof_claim=False,
        generalization_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(args.output / 'receipt.json', receipt)
    print(json.dumps(dict(complete=True, updates=len(ledger), parameter_delta_l2=delta,
                          checkpoint_sha256=receipt['child_sha256'])), flush=True)


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
    parser.add_argument('--model', type=Path, required=True)
    args = parser.parse_args()
    if args.mode == 'prepare':
        prepare(args)
    elif args.mode == 'preflight':
        if not args.manifest or not args.manifest_sha256:
            parser.error('preflight requires manifest and manifest-sha256')
        preflight(args)
    else:
        if not all((args.manifest, args.manifest_sha256, args.preflight,
                    args.preflight_sha256, args.checkpoint)):
            parser.error('train requires manifest, preflight, and checkpoint')
        train(args)
