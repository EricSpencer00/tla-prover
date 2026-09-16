"""Bounded structure-first SFT and protected SANY diagnostic.

The CPU admission probe proves that clean full modules have a lossless
representation with substantially shorter sequential operator spans. This
worker tests that representation with a model-emitted structure plan followed
by one model response per planned module part. Parts are concatenated exactly
as emitted and sent to pinned SANY; no text repair, target insertion,
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

EXPERIMENT_KIND = 'fullmodule_structure_first_sft_v2'
PLAN_PREFIX = 'STRUCTURE-FIRST PLAN\nMODULE: '
PLAN_STOP = 'END PLAN\n'
BUDGET = dict(
    steps=48, accumulation=1, lr=2e-6, rank=4, alpha=8, seed=20260916,
    training_seconds=600, max_new_tokens=768, generation_seconds=10,
    sany_seconds=30, planner_forced_prefix=True,
    planner_forced_eos_after=PLAN_STOP, adapter_layers=[28, 29, 30, 31],
    adapter_targets=['q_proj', 'k_proj', 'v_proj', 'o_proj',
                     'gate_proj', 'up_proj', 'down_proj'],
    objective='structure_first_planner_and_lossless_part_sft',
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
        'tools/proof_fullmodule_structure_first_sft_train.py',
        'tools/proof_fullmodule_structure_first_probe.py',
        'tools/proof_fullmodule_broad_clean_sft_train.py',
        'tools/proof_fullmodule_multiexample_probe.py',
        'tools/proof_fullmodule_sany_feedback_correction_train.py',
        'tools/proof_fullmodule_learning_train.py',
        'tools/proof_cuda_train.py',
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


def plan_text(module_name, structure):
    lines = ['STRUCTURE-FIRST PLAN', f'MODULE: {module_name}']
    for part in structure['parts']:
        lines.append(f"PART: {part['id'] if part['kind'] == 'operator' else part['kind']}")
    lines.append('END PLAN')
    return '\n'.join(lines) + '\n'


def parse_plan(text, expected_module):
    if not isinstance(text, str) or '\x60\x60\x60' in text:
        raise ValueError('plan contains markdown or is not text')
    lines = text.splitlines()
    if len(lines) < 5 or lines[0] != 'STRUCTURE-FIRST PLAN' or lines[-1] != 'END PLAN':
        raise ValueError('plan envelope mismatch')
    if lines[1] != f'MODULE: {expected_module}':
        raise ValueError('plan module mismatch')
    parts = []
    for line in lines[2:-1]:
        match = re.fullmatch(
            r'PART: (header|declarations|footer|operator-([0-9]{3})-([A-Za-z_][A-Za-z0-9_]*))',
            line)
        if not match:
            raise ValueError('plan part syntax mismatch')
        raw_id = match.group(1)
        if raw_id.startswith('operator-'):
            parts.append(dict(id=raw_id, kind='operator',
                              operator_name=match.group(3), index=int(match.group(2))))
        else:
            parts.append(dict(id=raw_id, kind=raw_id, operator_name=None))
    if (not parts or parts[0]['kind'] != 'header' or
            parts[1]['kind'] != 'declarations' or parts[-1]['kind'] != 'footer'):
        raise ValueError('plan must begin with header/declarations and end with footer')
    operators = [part for part in parts if part['kind'] == 'operator']
    if not operators or [part['index'] for part in operators] != list(range(len(operators))):
        raise ValueError('plan operator indices must be contiguous')
    if len(parts) > 40:
        raise ValueError('plan contains too many parts')
    return parts


def prompt_only(tokenizer, prompt):
    rendered = tokenizer.apply_chat_template(
        [dict(role='user', content=prompt)], tokenize=False, add_generation_prompt=True)
    ids = tokenizer.encode(rendered, add_special_tokens=False)
    if not ids:
        raise ValueError('empty structure-first prompt encoding')
    return dict(input_ids=ids, labels=[-100] * len(ids),
                prompt_tokens=len(ids), response_tokens=0)


class ForceEosAfterPlan:
    """Force the configured EOS after the model emits the plan terminator."""

    def __init__(self, suffix_ids, eos_token_id, prompt_tokens):
        self.suffix_ids = tuple(int(x) for x in suffix_ids)
        self.eos_token_id = int(eos_token_id)
        self.prompt_tokens = int(prompt_tokens)
        if not self.suffix_ids or self.eos_token_id < 0:
            raise ValueError('plan EOS control requires a non-empty suffix and EOS')

    def __call__(self, input_ids, scores):
        for row, ids in enumerate(input_ids.tolist()):
            generated = ids[self.prompt_tokens:]
            if (len(generated) >= len(self.suffix_ids) and
                    generated[-len(self.suffix_ids):] == list(self.suffix_ids)):
                scores[row, :] = float('-inf')
                scores[row, self.eos_token_id] = 0.0
        return scores


def decode_plan(net, tokenizer, enc, module_name, budget, multi):
    """Generate a plan with model-emitted content and a lossless EOS boundary."""
    import torch
    prompt_tokens = int(enc['prompt_tokens'])
    prompt_ids = list(enc['input_ids'][:prompt_tokens])
    prefix = PLAN_PREFIX + module_name + '\n'
    prefix_ids = tokenizer.encode(prefix, add_special_tokens=False)
    suffix_ids = tokenizer.encode(PLAN_STOP, add_special_tokens=False)
    eos_id = tokenizer.eos_token_id
    if not prefix_ids or not suffix_ids or eos_id is None:
        raise ValueError('plan control tokenization is incomplete')
    ids = torch.tensor([prompt_ids + prefix_ids], device='cuda')
    try:
        from transformers import LogitsProcessorList
        processors = LogitsProcessorList([ForceEosAfterPlan(
            suffix_ids, eos_id, prompt_tokens)])
    except ImportError:
        processors = [ForceEosAfterPlan(suffix_ids, eos_id, prompt_tokens)]
    started = time.monotonic()
    with torch.inference_mode(), multi.lineage.helpers.autocast('cuda'):
        result = net.generate(
            input_ids=ids, attention_mask=torch.ones_like(ids), do_sample=False,
            temperature=1.0, top_p=1.0, num_beams=1, num_return_sequences=1,
            max_new_tokens=budget['max_new_tokens'] + len(prefix_ids),
            max_time=budget['generation_seconds'], logits_processor=processors,
            no_repeat_ngram_size=8,
            pad_token_id=tokenizer.pad_token_id or tokenizer.eos_token_id)
    torch.cuda.synchronize()
    elapsed = time.monotonic() - started
    tokens = multi.lineage.common.trim_output(
        result[0, prompt_tokens:].tolist(), set(multi.lineage.common.EOS_IDS))
    reply = multi.lineage.common.decode_reply(tokenizer, tokens)
    return multi.output_fields(
        tokens, reply, elapsed, budget=budget['max_new_tokens'] + len(prefix_ids))


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


def stage_prompt(source_prompt, module_name, request, plan=None, prefix=''):
    text = (
        '\n\n=== STRUCTURE-FIRST GENERATION CONTRACT ===\n'
        'The final answer is assembled from exact model-emitted parts and '
        'checked by the owned SANY parser. Return only the requested part, '
        'with no markdown, explanation, or repeated context.\n'
        f'MODULE: {module_name}\nREQUESTED PART: {request}\n')
    if plan is not None:
        text += 'PLAN:\n' + plan + '\n'
    if prefix:
        text += ('CURRENT ASSEMBLED PREFIX (context only; do not repeat it):\n'
                 + prefix + '\n')
    if request == 'plan':
        text += ('Return exactly a STRUCTURE-FIRST PLAN with the module name, '
                 'one header, one declarations part, every operator in order, '
                 'and one footer part.\n')
    elif request == 'header':
        text += 'Return the complete module header part, including its exact module header line.\n'
    elif request == 'declarations':
        text += 'Return the complete declarations part before the first top-level operator.\n'
    elif request == 'footer':
        text += 'Return the complete module footer part.\n'
    else:
        text += 'Return the complete requested top-level operator block.\n'
    return source_prompt + text


def schedule(structures):
    selected_rows = [TRAIN[i * len(TRAIN) // BUDGET['steps']]
                     for i in range(BUDGET['steps'])]
    result = []
    for step, row in enumerate(selected_rows, 1):
        structure = structures[row]
        if step % 5 == 0:
            request = 'plan'
        else:
            request = structure['parts'][(step * 7 + row) % len(structure['parts'])]['id']
        result.append(dict(step=step, row=row, request=request, part_id=request))
    return result


def target_for(row, request, rows, structures):
    structure = structures[row]
    if request == 'plan':
        return plan_text(structure['module_name'], structure)
    part = next((part for part in structure['parts'] if part['id'] == request), None)
    if part is None:
        raise ValueError(f'part {request} missing for row {row}')
    response = rows[row]['response']
    return response[part['start_char']:part['end_char']]


def manifest_value(rows, structures, probe):
    entries = schedule(structures)
    for entry in entries:
        structure = structures[entry['row']]
        target = target_for(entry['row'], entry['request'], rows, structures)
        prompt = stage_prompt(
            rows[entry['row']]['prompt'], structure['module_name'], entry['request'],
            plan=plan_text(structure['module_name'], structure)
            if entry['request'] != 'plan' else None)
        entry.update(target_sha256=sha(target.encode()),
                     target_char_count=len(target), prompt_sha256=sha(prompt.encode()))
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
        planner_target_is_derived_structure_only=True,
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
        target = target_for(entry['row'], entry['request'], rows, structures)
        prompt = stage_prompt(
            rows[entry['row']]['prompt'], structure['module_name'], entry['request'],
            plan=plan_text(structure['module_name'], structure)
            if entry['request'] != 'plan' else None)
        if (sha(target.encode()) != entry['target_sha256'] or
                sha(prompt.encode()) != entry['prompt_sha256']):
            raise ValueError(f'schedule source identity changed at step {entry["step"]}')
        encoded = exact_chat(tokenizer, prompt, target)
        if encoded['response_tokens'] <= 0 or encoded != exact_chat(tokenizer, prompt, target):
            raise ValueError(f'non-deterministic or empty target at step {entry["step"]}')
        records.append(dict(
            step=entry['step'], row=entry['row'], request=entry['request'],
            target_sha256=entry['target_sha256'], prompt_sha256=entry['prompt_sha256'],
            target_char_count=len(target), prompt_tokens=encoded['prompt_tokens'],
            response_tokens=encoded['response_tokens'],
            input_ids_sha256=sha(json.dumps(encoded['input_ids'], separators=(',', ':')).encode()),
            labels_sha256=sha(json.dumps(encoded['labels'], separators=(',', ':')).encode())))
    result = dict(
        schema=1, kind='fullmodule_structure_first_sft_cpu_preflight_v1',
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
    return value, by_step


def make_eval_tasks(packet, rows, output):
    from tools import proof_fullmodule_multiexample_probe as multi
    tasks = {row: multi.stage_task(
        multi.checker_task(packet, rows[row]), output, f'reference/{row}')
        for row in PROTECTED}
    return tasks, multi.sany.identity(list(tasks.values()))


def evaluate_protected(net, tokenizer, rows, output, phase, tasks, sany_identity):
    from tools import proof_fullmodule_multiexample_probe as multi
    results = {}
    for row in PROTECTED:
        source, module = rows[row], MODULE_NAMES[row]
        plan = decode_plan(
            net, tokenizer,
            prompt_only(tokenizer, stage_prompt(source['prompt'], module, 'plan')),
            module, BUDGET, multi)
        item = dict(row=row, phase=phase, module_name=module, plan=plan)
        assembled, parts, planned = '', [], None
        if plan['finish_reason'] == 'eos':
            try:
                planned = parse_plan(plan['raw_reply'], module)
            except ValueError as exc:
                item['plan_reject'] = str(exc)
        else:
            item['plan_reject'] = 'plan did not terminate with EOS'
        if planned is not None:
            for request in planned:
                prompt = stage_prompt(
                    source['prompt'], module, request['id'],
                    plan=plan['raw_reply'], prefix=assembled)
                forced = f'---- MODULE {module} ----\n' if request['kind'] == 'header' else None
                generated = multi.decode(
                    net, tokenizer, prompt_only(tokenizer, prompt),
                    forced_prefix=forced)
                parts.append(dict(request=request, generation=generated))
                if generated['finish_reason'] != 'eos':
                    item['part_reject'] = f"{request['id']} did not terminate with EOS"
                    break
                assembled += generated['raw_reply']
        item['parts'] = parts
        item['assembled_sha256'] = sha(assembled.encode()) if assembled else None
        item['assembled_char_count'] = len(assembled)
        if planned is not None and len(parts) == len(planned):
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
        target = target_for(entry['row'], entry['request'], rows, structures)
        prompt = stage_prompt(
            rows[entry['row']]['prompt'], structure['module_name'], entry['request'],
            plan=plan_text(structure['module_name'], structure)
            if entry['request'] != 'plan' else None)
        encoded = base.exact_chat(tokenizer, prompt, target)
        record = preflight_by_step[entry['step']]
        if (sha(prompt.encode()) != record['prompt_sha256'] or
                sha(target.encode()) != record['target_sha256'] or
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
        item = dict(step=step, row=entry['row'], request=entry['request'],
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
        algorithm='planner plus lossless module-part response-only SFT; fresh AdamW',
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
        clean_reference_targets_only=True, planner_target_is_derived_structure_only=True,
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
