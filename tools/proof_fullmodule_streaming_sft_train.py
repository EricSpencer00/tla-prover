"""Bounded matched-prefix streaming SFT and protected SANY diagnostic.

The preceding streaming run exposed a train/eval contract mismatch: its
training examples requested named structural parts, while protected decoding
requested an unconstrained continuation from the current assembled prefix.
This worker trains on exact continuation segments using the identical
prefix/state prompt that protected decoding uses. Segments are concatenated
exactly as emitted and sent to pinned SANY; no text repair, target insertion,
verifier feedback, or replay negative is allowed.
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

PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
PARENT_SHA = '87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511'
PROBE_SHA = 'd88053f871c23d8fe9c623e80c4d28d8fbc662214b0f0d3b024cb2ae0cab94b9'
W4_ROWS = tuple(range(42, 169))
VALID = (59, 60, 61, 62, 63, 64)
PROTECTED = (47, 107)
TRAIN = tuple(i for i in W4_ROWS if i not in VALID and i not in PROTECTED)
REFERENCE_ROWS = TRAIN + VALID
ANCHORS = tuple(i for i in range(42, 59) if i != 47)
MODULE_NAMES = {47: 'W4Od2m7p4t2', 107: 'W4Od3m0p0t0'}

EXPERIMENT_KIND = 'fullmodule_streaming_sanitized_prompt_sft_v1'
BUDGET = dict(
    steps=48, accumulation=1, lr=2e-6, rank=4, alpha=8, seed=20260918,
    training_seconds=600, max_new_tokens=768, generation_seconds=10,
    sany_seconds=30, stream_segments=4, adapter_layers=[28, 29, 30, 31],
    adapter_targets=['q_proj', 'k_proj', 'v_proj', 'o_proj',
                     'gate_proj', 'up_proj', 'down_proj'],
    objective='streaming_lossless_sanitized_prompt_sft',
)
def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    digest = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(8 * 1024 * 1024), b''):
            digest.update(chunk)
    return digest.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def source_pins():
    names = (
        'tools/proof_fullmodule_streaming_sft_train.py',
        'tools/proof_fullmodule_structure_first_probe.py',
        'tools/proof_fullmodule_broad_clean_sft_train.py',
        'tools/proof_fullmodule_multiexample_probe.py',
        'tools/proof_fullmodule_sany_feedback_correction_train.py',
        'tools/proof_fullmodule_learning_train.py',
        'tools/proof_cuda_train.py',
        'tools/proof_fullmodule_streaming_parser_admission.py',
    )
    return {name: file_sha(ROOT / name) for name in names}


def load_packet(path):
    raw = Path(path).read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError('exact immutable full-module packet required')
    packet = json.loads(raw)
    rows, encodings = packet.get('rows'), packet.get('encodings')
    if (not isinstance(rows, list) or not isinstance(encodings, list) or
            len(rows) != 169 or len(encodings) != 169):
        raise ValueError('complete 169-row packet required')
    for row in (*TRAIN, *VALID):
        value, encoding = rows[row], encodings[row]
        if (value.get('split') != 'train' or encoding.get('id') != value.get('id') or
                sha(value.get('prompt', '').encode()) != value.get('prompt_sha256') or
                sha(value.get('response', '').encode()) != value.get('response_sha256') or
                value.get('source_sha256') != value.get('response_sha256') or
                encoding.get('prompt_sha256') != value.get('prompt_sha256') or
                encoding.get('response_sha256') != value.get('response_sha256')):
            raise ValueError(f'clean row {row} identity changed')
    for row in PROTECTED:
        value = rows[row]
        if (value.get('split') != 'train' or
                not value.get('id', '').startswith('w4-fullmodule:') or
                not re.fullmatch(r'[0-9a-f]{64}', value.get('response_sha256', ''))):
            raise ValueError(f'protected row {row} metadata changed')
    return packet, rows


def load_probe(path):
    if file_sha(path) != PROBE_SHA:
        raise ValueError('exact CPU structure-first admission artifact required')
    value = json.loads(Path(path).read_bytes())
    if (value.get('packet_sha256') != PACKET_SHA or
            value.get('representation_admitted') is not True or
            value.get('all_reconstructions_exact') is not True or
            value.get('all_strict_sequential_horizon_reductions') is not True or
            value.get('controls_ok') is not True or
            value.get('reference_rows') != list(REFERENCE_ROWS)):
        raise ValueError('CPU structure-first admission guards failed')
    structures = {item['row']: item for item in value.get('structures', [])}
    if len(structures) != len(REFERENCE_ROWS) or set(structures) != set(REFERENCE_ROWS):
        raise ValueError('complete clean structure inventory required')
    return value, structures


def stream_segments(response, structure, count=BUDGET['stream_segments']):
    """Group lossless structural parts into a fixed number of stream targets."""
    parts = structure['parts']
    if not parts or ''.join(response[p['start_char']:p['end_char']] for p in parts) != response:
        raise ValueError('structure is not a lossless response partition')
    count = min(int(count), len(parts))
    if count <= 0:
        raise ValueError('stream must contain at least one part')
    groups = [[] for _ in range(count)]
    for index, part in enumerate(parts):
        groups[min(index * count // len(parts), count - 1)].append(part)
    result = [''.join(response[p['start_char']:p['end_char']] for p in group)
              for group in groups]
    if any(not segment for segment in result) or ''.join(result) != response:
        raise AssertionError('stream segmentation is not nonempty and lossless')
    return result


def prompt_only(tokenizer, prompt):
    rendered = tokenizer.apply_chat_template(
        [dict(role='user', content=prompt)], tokenize=False, add_generation_prompt=True)
    ids = tokenizer.encode(rendered, add_special_tokens=False)
    if not ids:
        raise ValueError('empty structure-first prompt encoding')
    return dict(input_ids=ids, labels=[-100] * len(ids),
                prompt_tokens=len(ids), response_tokens=0)


def stream_prompt(source_prompt, module_name, segment, prefix=''):
    text = (
        '\n\n=== LOSSLESS STREAMING MODULE CONTRACT ===\n'
        'Emit only the exact continuation of the module byte stream. Do not '
        'repeat any prefix, add markdown, or explain. Emit no synthetic text '
        'when the prefix is incomplete. The stream must end with the complete '
        'module footer. The task already names the module; begin the assistant '
        'response with the exact bytes required by that task.\n')
    if prefix:
        text += 'CURRENT EXACT PREFIX:\n' + prefix + '\n'
        text += 'Continue immediately after the prefix.\n'
    else:
        text += 'Begin with the exact module header line.\n'
    return source_prompt + text


def exact_chat(tokenizer, prompt, response):
    rendered = tokenizer.apply_chat_template(
        [dict(role='user', content=prompt), dict(role='assistant', content=response)],
        tokenize=False, add_generation_prompt=False)
    ids = tokenizer.encode(rendered, add_special_tokens=False)
    prefix = tokenizer.apply_chat_template(
        [dict(role='user', content=prompt)], tokenize=False, add_generation_prompt=True)
    prefix_ids = tokenizer.encode(prefix, add_special_tokens=False)
    if ids[:len(prefix_ids)] != prefix_ids:
        raise ValueError('assistant response is not an exact chat-template suffix')
    return dict(input_ids=ids, labels=[-100] * len(prefix_ids) + ids[len(prefix_ids):],
                prompt_tokens=len(prefix_ids), response_tokens=len(ids) - len(prefix_ids))


def schedule(structures):
    selected_rows = [TRAIN[i * len(TRAIN) // BUDGET['steps']]
                     for i in range(BUDGET['steps'])]
    result = []
    for step, row in enumerate(selected_rows, 1):
        segment_count = min(BUDGET['stream_segments'],
                            len(structures[row]['parts']))
        if segment_count <= 0:
            raise ValueError(f'row {row} has no structural parts')
        segment = (step * 7 + row) % segment_count
        result.append(dict(step=step, row=row, segment=segment,
                           segment_count=segment_count))
    return result


def target_for(row, segment, rows, structures):
    response = rows[row]['response']
    segments = stream_segments(response, structures[row])
    if not 0 <= int(segment) < len(segments):
        raise ValueError(f'stream segment {segment} missing for row {row}')
    return segments[int(segment)]


def prefix_for(row, segment, rows, structures):
    response = rows[row]['response']
    segments = stream_segments(response, structures[row])
    if not 0 <= int(segment) <= len(segments):
        raise ValueError(f'stream prefix {segment} missing for row {row}')
    return ''.join(segments[:int(segment)])


def manifest_value(rows, structures, probe):
    entries = schedule(structures)
    for entry in entries:
        structure = structures[entry['row']]
        target = target_for(entry['row'], entry['segment'], rows, structures)
        prefix = prefix_for(entry['row'], entry['segment'], rows, structures)
        prompt = stream_prompt(rows[entry['row']]['prompt'],
                               structure['module_name'], entry['segment'], prefix)
        entry.update(target_sha256=sha(target.encode()),
                     target_char_count=len(target), prefix_char_count=len(prefix),
                     prefix_sha256=sha(prefix.encode()), prompt_sha256=sha(prompt.encode()))
    return dict(
        schema=1, kind=EXPERIMENT_KIND,
        packet_sha256=PACKET_SHA, structure_probe_sha256=PROBE_SHA,
        parent_checkpoint_sha256=PARENT_SHA, train_rows=list(TRAIN),
        validation_rows=list(VALID), protected_rows=list(PROTECTED),
        anchor_rows=list(ANCHORS), budget=BUDGET, schedule=entries,
        schedule_sha256=sha(json.dumps(entries, separators=(',', ':')).encode()),
        source_sha256=source_pins(),
        structure_stats=dict(
            reference_count=probe['reference_count'],
            median_sequential_horizon_ratio=probe['median_sequential_horizon_ratio'],
            max_sequential_horizon_ratio=probe['max_sequential_horizon_ratio']),
        clean_reference_targets_only=True,
        planner_target_is_derived_structure_only=False,
        generated_feedback_loaded=False, replay_negatives_loaded=False,
        protected_targets_never_train=True, validation_targets_never_train=True,
        model_weights_loaded=False, cuda_touched=False, optimizer_updates=0,
        training_authorized=True, quality_claim=False,
        model_improvement_claim=False, gate_claim=False, proof_claim=False,
        generalization_claim=False, tlc_claim=False, nonvacuity_claim=False)


def build_manifest(args):
    packet, rows = load_packet(args.packet)
    probe, structures = load_probe(args.probe)
    result = manifest_value(rows, structures, probe)
    dump(args.output, result)
    print(json.dumps(dict(prepared=True, steps=len(result['schedule']),
                          manifest_sha256=file_sha(args.output))))


def verify_manifest(args):
    packet, rows = load_packet(args.packet)
    probe, structures = load_probe(args.probe)
    if file_sha(args.manifest) != args.manifest_sha256:
        raise ValueError('manifest hash mismatch')
    manifest = json.loads(Path(args.manifest).read_bytes())
    if manifest != manifest_value(rows, structures, probe):
        raise ValueError('manifest identity or schedule changed')
    return packet, rows, structures, manifest


def preflight(args):
    packet, rows, structures, manifest = verify_manifest(args)
    import transformers
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    records = []
    for entry in manifest['schedule']:
        structure = structures[entry['row']]
        target = target_for(entry['row'], entry['segment'], rows, structures)
        prefix = prefix_for(entry['row'], entry['segment'], rows, structures)
        prompt = stream_prompt(rows[entry['row']]['prompt'],
                               structure['module_name'], entry['segment'], prefix)
        if (sha(target.encode()) != entry['target_sha256'] or
                sha(prefix.encode()) != entry['prefix_sha256'] or
                sha(prompt.encode()) != entry['prompt_sha256']):
            raise ValueError(f'schedule source identity changed at step {entry["step"]}')
        encoded = exact_chat(tokenizer, prompt, target)
        if encoded['response_tokens'] <= 0 or encoded != exact_chat(tokenizer, prompt, target):
            raise ValueError(f'non-deterministic or empty target at step {entry["step"]}')
        records.append(dict(
            step=entry['step'], row=entry['row'], segment=entry['segment'],
            segment_count=entry['segment_count'], prefix_sha256=entry['prefix_sha256'],
            target_sha256=entry['target_sha256'], prompt_sha256=entry['prompt_sha256'],
            target_char_count=len(target), prefix_char_count=len(prefix),
            prompt_tokens=encoded['prompt_tokens'],
            response_tokens=encoded['response_tokens'],
            input_ids_sha256=sha(json.dumps(encoded['input_ids'], separators=(',', ':')).encode()),
            labels_sha256=sha(json.dumps(encoded['labels'], separators=(',', ':')).encode())))
    result = dict(
        schema=1, kind=f'{EXPERIMENT_KIND}_cpu_preflight',
        manifest_sha256=args.manifest_sha256, packet_sha256=PACKET_SHA,
        structure_probe_sha256=PROBE_SHA, parent_checkpoint_sha256=PARENT_SHA,
        records=records, record_count=len(records), all_tokenizers_exact=True,
        nonzero_targets_per_step=True, model_weights_loaded=False,
        cuda_touched=False, optimizer_updates=0, generated_feedback_loaded=False,
        replay_negatives_loaded=False, protected_targets_never_train=True,
        validation_targets_never_train=True, training_authorized=True,
        quality_claim=False, model_improvement_claim=False, gate_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False,
        nonvacuity_claim=False)
    dump(args.output, result)
    print(json.dumps(dict(preflight='pass', records=len(records),
                          preflight_sha256=file_sha(args.output))))


def validate_preflight(args):
    if file_sha(args.preflight) != args.preflight_sha256:
        raise ValueError('preflight hash mismatch')
    value = json.loads(Path(args.preflight).read_bytes())
    if (value.get('manifest_sha256') != args.manifest_sha256 or
            value.get('record_count') != BUDGET['steps'] or
            value.get('all_tokenizers_exact') is not True or
            value.get('nonzero_targets_per_step') is not True or
            value.get('model_weights_loaded') is not False or
            value.get('cuda_touched') is not False or
            value.get('optimizer_updates') != 0):
        raise ValueError('CPU structure-first preflight guards failed')
    by_step = {item['step']: item for item in value['records']}
    if set(by_step) != set(range(1, BUDGET['steps'] + 1)):
        raise ValueError('complete preflight step inventory required')
    if any(not isinstance(item.get('segment'), int) or
           not isinstance(item.get('segment_count'), int) or
           not isinstance(item.get('prefix_sha256'), str)
           for item in value['records']):
        raise ValueError('matched-prefix segment identity missing')
    return value, by_step


def make_eval_tasks(packet, rows, output):
    from tools import proof_fullmodule_multiexample_probe as multi
    tasks = {row: multi.stage_task(
        multi.checker_task(packet, rows[row]), output, f'reference/{row}')
        for row in PROTECTED}
    return tasks, multi.sany.identity(list(tasks.values()))


def evaluate_protected(net, tokenizer, rows, output, phase, tasks, sany_identity):
    from tools import proof_fullmodule_multiexample_probe as multi
    from tools.proof_fullmodule_streaming_parser_admission import ModuleStream
    results = {}
    for row in PROTECTED:
        source, module = rows[row], MODULE_NAMES[row]
        stream = ModuleStream()
        assembled, parts = '', []
        plan = dict(raw_reply='', raw_reply_sha256=sha(b''), output_tokens=0,
                    finish_reason='not_used', deadline_exceeded=False,
                    elapsed_seconds=0.)
        item = dict(row=row, phase=phase, module_name=module,
                    stream_contract='matched_prefix_state_v1', plan=plan)
        for segment in range(BUDGET['stream_segments']):
            prompt = stream_prompt(source['prompt'], module, segment, assembled)
            generated = multi.decode(
                net, tokenizer, prompt_only(tokenizer, prompt))
            parts.append(dict(segment=segment, generation=generated))
            try:
                stream.feed(generated['raw_reply'])
            except ValueError as exc:
                item['stream_reject'] = str(exc)
                break
            assembled = stream.text
            if generated['finish_reason'] == 'eos':
                try:
                    stream.finish()
                except ValueError as exc:
                    item['stream_reject'] = str(exc)
                break
        item['parts'] = parts
        item['assembled_sha256'] = sha(assembled.encode()) if assembled else None
        item['assembled_char_count'] = len(assembled)
        complete = False
        if 'stream_reject' not in item:
            try:
                stream.finish()
                complete = True
            except ValueError as exc:
                item['stream_reject'] = str(exc)
        if complete:
            item['sany'] = multi.sany.check(
                tasks[row], assembled, output / f'sany_candidate/{phase}/{row}',
                sany_identity, timeout=BUDGET['sany_seconds'])
        else:
            item['sany'] = None
        dump(output / f'{phase}-row-{row}.json', item)
        results[str(row)] = item
    return results


def train(args):
    import torch
    import transformers
    from tools import proof_fullmodule_broad_clean_sft_train as base
    from tools import proof_fullmodule_multiexample_probe as multi
    from tools import proof_fullmodule_sany_feedback_correction_train as common
    from tools import proof_fullmodule_learning_train as lineage
    base.BUDGET = dict(base.BUDGET, **BUDGET)
    multi.BUDGET.update(
        max_new_tokens=BUDGET['max_new_tokens'],
        item_seconds=BUDGET['generation_seconds'],
        sany_seconds=BUDGET['sany_seconds'], train_only=False,
        eval_rows=list(PROTECTED), gate_claim=False, quality_claim=False,
        generalization_claim=False, proof_claim=False, tlc_claim=False,
        nonvacuity_claim=False)
    torch.set_num_threads(4)
    torch.manual_seed(BUDGET['seed'])
    random.seed(BUDGET['seed'])
    if file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('exact parent checkpoint required')
    packet, rows, structures, manifest = verify_manifest(args)
    preflight, preflight_by_step = validate_preflight(args)
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 required')
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output / 'manifest.json', manifest)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    encodings = []
    for entry in manifest['schedule']:
        structure = structures[entry['row']]
        target = target_for(entry['row'], entry['segment'], rows, structures)
        prefix = prefix_for(entry['row'], entry['segment'], rows, structures)
        prompt = stream_prompt(rows[entry['row']]['prompt'],
                               structure['module_name'], entry['segment'], prefix)
        encoded = base.exact_chat(tokenizer, prompt, target)
        record = preflight_by_step[entry['step']]
        if (sha(prompt.encode()) != record['prompt_sha256'] or
                sha(target.encode()) != record['target_sha256'] or
                sha(prefix.encode()) != record['prefix_sha256'] or
                sha(json.dumps(encoded['input_ids'], separators=(',', ':')).encode()) != record['input_ids_sha256'] or
                sha(json.dumps(encoded['labels'], separators=(',', ':')).encode()) != record['labels_sha256']):
            raise ValueError(f'actual worker tokenizer differs at step {entry["step"]}')
        encodings.append(encoded)

    net = lineage.helpers.load_policy(str(args.model))
    saved = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(args.model))
    del saved
    selected = base.inject_adapters(net)
    context = lambda: torch.autocast('cuda', dtype=torch.bfloat16)
    probe_ids = encodings[0]['input_ids'][:64]
    initial = {name: parameter.detach().cpu().clone()
               for name, parameter in selected.items()}
    with torch.no_grad(), context():
        parent_probe = net(
            input_ids=torch.tensor([probe_ids], device='cuda'),
            use_cache=False).logits[:, -1].float().cpu()
    if not bool(torch.isfinite(parent_probe).all()):
        raise ValueError('nonfinite parent probe')

    tasks, sany_identity = make_eval_tasks(packet, rows, args.output)
    before = evaluate_protected(net, tokenizer, rows, args.output,
                                'restored_parent', tasks, sany_identity)
    validation_before = []
    for row in VALID:
        loss, metric = common.teacher_loss(
            net, base.exact_chat(tokenizer, rows[row]['prompt'], rows[row]['response']),
            context=context)
        validation_before.append(dict(row=row, **metric))
        del loss

    for parameter in selected.values():
        parameter.requires_grad_(True)
    optimizer = torch.optim.AdamW(
        selected.values(), lr=BUDGET['lr'], weight_decay=0., foreach=False)
    ledger, started = [], time.monotonic()
    for step, entry in enumerate(manifest['schedule'], 1):
        if time.monotonic() - started >= BUDGET['training_seconds']:
            raise RuntimeError('structure-first training budget expired')
        optimizer.zero_grad(set_to_none=True)
        loss, metric = common.teacher_loss(net, encodings[step - 1], context=context)
        loss.backward()
        grad = float(torch.nn.utils.clip_grad_norm_(
            selected.values(), 1., error_if_nonfinite=True))
        if not math.isfinite(grad) or grad <= 0:
            raise ValueError(f'nonfinite or zero gradient at step {step}')
        optimizer.step()
        if any(not bool(torch.isfinite(parameter).all())
               for parameter in selected.values()):
            raise ValueError(f'nonfinite adapter after step {step}')
        item = dict(step=step, row=entry['row'], segment=entry['segment'],
                    segment_count=entry['segment_count'],
                    target_sha256=entry['target_sha256'], loss=metric['loss'],
                    target_top1=metric['target_top1'],
                    target_tokens=metric['target_tokens'], gradient_norm=grad)
        ledger.append(item)
        with (args.output / 'steps.jsonl').open('a') as stream:
            stream.write(json.dumps(item) + '\n')
        print(json.dumps(item), flush=True)
    if len(ledger) != BUDGET['steps']:
        raise ValueError('executed update count differs from admitted schedule')

    state = {name: parameter.detach().cpu().clone()
             for name, parameter in selected.items()}
    delta = math.sqrt(sum(float((state[name] - initial[name]).double().square().sum())
                          for name in state))
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError('structure-first child did not change finitely')
    config = dict(
        kind=EXPERIMENT_KIND,
        algorithm='matched-prefix lossless stream response-only SFT; fresh AdamW',
        packet_sha256=PACKET_SHA, parent_sha256=PARENT_SHA,
        structure_probe_sha256=PROBE_SHA, manifest_sha256=args.manifest_sha256,
        budget=BUDGET, source_sha256=manifest['source_sha256'],
        model_files=lineage.helpers.model_files(args.model),
        dtype_profile='frozen bf16 base with float32 final transformer layer; bf16 autocast',
        optimizer_state_stored=False, generated_feedback_loaded=False,
        replay_negatives_loaded=False, protected_targets_never_train=True,
        validation_targets_never_train=True, gate_claim=False, quality_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False,
        nonvacuity_claim=False)
    checkpoint = args.output / 'policy_lora.pt'
    common.save_exact(torch, state, config, ledger, checkpoint)
    with torch.no_grad(), context():
        child_probe = net(
            input_ids=torch.tensor([probe_ids], device='cuda'),
            use_cache=False).logits[:, -1].float().cpu()
        for parameter in selected.values():
            parameter.zero_()
        reloaded = torch.load(checkpoint, map_location='cpu', weights_only=False)
        common.restore_adapters(selected, reloaded['trainable_state'])
        reload_probe = net(
            input_ids=torch.tensor([probe_ids], device='cuda'),
            use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(child_probe, reload_probe):
        raise ValueError('checkpoint logit reload mismatch')
    if not all(torch.equal(parameter.detach().cpu(), state[name])
               for name, parameter in selected.items()):
        raise ValueError('checkpoint tensor reload mismatch')

    validation_after = []
    for row in VALID:
        loss, metric = common.teacher_loss(
            net, base.exact_chat(tokenizer, rows[row]['prompt'], rows[row]['response']),
            context=context)
        validation_after.append(dict(row=row, **metric))
        del loss
    after = evaluate_protected(net, tokenizer, rows, args.output,
                               'trained_child', tasks, sany_identity)
    receipt = dict(
        schema=1, kind=EXPERIMENT_KIND, complete=True,
        packet_sha256=PACKET_SHA, structure_probe_sha256=PROBE_SHA,
        parent_checkpoint_sha256=PARENT_SHA, manifest_sha256=args.manifest_sha256,
        preflight_sha256=args.preflight_sha256, updates=len(ledger),
        schedule=manifest['schedule'], checkpoint_sha256=file_sha(checkpoint),
        parameter_delta_l2=delta, adapter_parameter_tensors=len(selected),
        adapter_parameter_count=sum(parameter.numel() for parameter in selected.values()),
        reload_tensors_exact=True, reload_logits_exact=True,
        before_protected=before, after_protected=after,
        validation_before=validation_before, validation_after=validation_after,
        sany_identity=sany_identity, preflight=preflight,
        generated_feedback_used_for_training=False, replay_negatives_loaded=False,
        protected_targets_never_train=True, validation_targets_never_train=True,
        clean_reference_targets_only=True, planner_target_is_derived_structure_only=False,
        model_improvement_claim=False, quality_claim=False, gate_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False,
        nonvacuity_claim=False)
    dump(args.output / 'receipt.json', receipt)
    print(json.dumps(dict(complete=True, updates=len(ledger),
                          checkpoint_sha256=receipt['checkpoint_sha256']),
               ), flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('prepare', 'preflight', 'train'))
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--probe', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--jar', type=Path, default=ROOT / 'tools/tla2tools.jar')
    parser.add_argument('--java', default='java')
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--manifest-sha256')
    parser.add_argument('--preflight', type=Path)
    parser.add_argument('--preflight-sha256')
    parser.add_argument('--checkpoint', type=Path)
    parser.add_argument('--model', type=Path, required=True)
    args = parser.parse_args()
    if args.mode == 'prepare':
        build_manifest(args)
    elif args.mode == 'preflight':
        if not args.manifest or not args.manifest_sha256:
            parser.error('preflight requires manifest and manifest-sha256')
        preflight(args)
    else:
        if not all((args.manifest, args.manifest_sha256, args.preflight,
                    args.preflight_sha256, args.checkpoint)):
            parser.error('train requires manifest, preflight, and checkpoint')
        train(args)


if __name__ == '__main__':
    main()
