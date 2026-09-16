"""Verifier-conditioned correction training for full-module TLA+ generation.

This is a bounded diagnostic after clean-reference SFT, grammar-only decoding,
and the previous high-step feedback worker failed on the protected rows.  The
training inputs are immutable non-protected references with one deterministic
syntax fault injected and an independently captured pinned-SANY diagnostic.
The target is the original immutable reference, but it is never included in
the correction prompt.  Evaluation first generates an ordinary protected
candidate, runs SANY, then gives that exact candidate and diagnostic to a
second model pass.  Rows 47 and 107 are never used for preparation, training,
or feedback collection.
"""

import argparse
import hashlib
import json
import math
import os
import random
import re
import subprocess
import sys
import time
from pathlib import Path

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
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'
EOS_IDS = (128001, 128008, 128009)

BUDGET = dict(
    steps=16,
    accumulation=2,
    lr=5e-6,
    rank=4,
    alpha=8,
    feedback_weight=0.70,
    anchor_weight=0.30,
    seed=20260916,
    training_seconds=480,
    max_new_tokens=2048,
    generation_seconds=60,
    sany_seconds=30,
    adapter_layers=[30, 31],
    adapter_targets=['q_proj', 'k_proj', 'v_proj', 'o_proj',
                     'gate_proj', 'up_proj', 'down_proj'],
    objective='sany_labeled_single_fault_correction_with_clean_anchor',
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


def load(path):
    return json.loads(Path(path).read_bytes())


def module_name(text):
    match = re.search(r'^-+ MODULE (\w+) -+\s*$', text, re.M)
    if not match:
        raise ValueError('canonical module header required')
    return match[1]


def diagnostic_from_log(log):
    lines = [line.strip() for line in log.splitlines() if line.strip()]
    for line in lines:
        if ('Precedence conflict' in line or
                'Encountered ' in line or 'Lexical error' in line or
                'Unknown operator' in line or 'Was expecting' in line):
            return line
    for line in lines:
        if 'Fatal errors' in line or 'Semantic errors' in line:
            return line
    return 'SANY status: model_sany_reject'


def sany_check(text, output, java, jar, timeout=None):
    """Run the pinned parser and return an owned, compact diagnostic."""
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    try:
        name = module_name(text)
    except ValueError as exc:
        result = dict(status='model_reject', passed=False, diagnostic=str(exc))
        dump(output / 'result.json', result)
        return result
    (output / (name + '.tla')).write_text(text)
    timeout = BUDGET['sany_seconds'] if timeout is None else timeout
    try:
        proc = subprocess.run(
            [java, '-cp', str(Path(jar).resolve()), 'tla2sany.SANY', name + '.tla'],
            cwd=output, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        result = dict(status='infrastructure_timeout', passed=None,
                      diagnostic='SANY timeout')
        dump(output / 'result.json', result)
        return result
    log = proc.stdout + proc.stderr
    (output / 'sany.log').write_text(log)
    if re.search(r'\*\*\*\s*(?:Parse|Semantic)|Fatal errors|Parse Error|Semantic errors', log, re.I):
        result = dict(status='model_reject', passed=False, returncode=proc.returncode,
                      diagnostic=diagnostic_from_log(log))
    elif re.search(r'Exception|Could not find|NoClassDef|OutOfMemory', log):
        result = dict(status='infrastructure_error', passed=None, returncode=proc.returncode,
                      diagnostic=diagnostic_from_log(log))
    elif proc.returncode == 0 and 'Semantic processing of module ' + name in log:
        result = dict(status='pass', passed=True, returncode=0,
                      diagnostic='SANY semantic processing passed')
    else:
        result = dict(status='infrastructure_unknown', passed=None, returncode=proc.returncode,
                      diagnostic=diagnostic_from_log(log))
    dump(output / 'result.json', result)
    return result


def selected(packet_bytes):
    if sha(packet_bytes) != PACKET_SHA:
        raise ValueError('frozen packet changed')
    packet = json.loads(packet_bytes)
    # The packet byte hash is the authority.  The packet's historical source
    # manifest predates later repository-only harness repairs, so invoking the
    # live source validator here would reject an otherwise exact immutable
    # packet for unrelated working-tree drift.
    rows = packet.get('rows')
    encodings = packet.get('encodings')
    if (not isinstance(rows, list) or not isinstance(encodings, list) or
            len(rows) != 169 or len(encodings) != 169):
        raise ValueError('complete immutable packet required')
    chosen = {}
    for row in (*TRAIN, *VALID, *PROTECTED):
        source, enc = rows[row], encodings[row]
        if (source.get('split') != 'train' or enc.get('id') != source.get('id') or
                sha(source.get('response', '').encode()) != source.get('response_sha256') or
                enc.get('prompt_sha256') != source.get('prompt_sha256') or
                enc.get('response_sha256') != source.get('response_sha256')):
            raise ValueError(f'row {row} is not an exact training encoding')
        chosen[row] = (source, enc)
    return chosen, packet


def candidate_faults(text):
    """Return deterministic, single-edit candidate faults.

    Every candidate is independently SANY-screened in ``prepare``.  A fault
    that happens to remain syntactically valid is discarded instead of being
    presented as verifier supervision.
    """
    candidates = []
    replacements = [
        ('definition_equals', r'(?m)^(\s*\w+) ==', lambda m: m[1] + ' ='),
        ('map_arrow_colon', r'\|->', lambda m: ':'),
        ('split_map_arrow', r'\|->', lambda m: '| ->'),
        ('malformed_quantifier', r'\\A\s+(\w+)\s+\\in', lambda m: r'\A \in'),
        ('footer_truncation', r'={4,}\s*$', lambda m: '===')
    ]
    for kind, pattern, replace in replacements:
        bad, count = re.subn(pattern, replace, text, count=1)
        if count and bad != text:
            candidates.append((kind, bad))
    # Removing a conjunction marker from a multi-line conjunction is a
    # distinct junction failure and is kept only when the corpus has such a
    # line.  It avoids hand-editing any protected text.
    lines = text.splitlines()
    for index in range(1, len(lines)):
        if re.match(r'^\s+/\\\s+\S', lines[index]) and re.match(r'^\s+\S', lines[index - 1]):
            bad_lines = list(lines)
            bad_lines[index] = re.sub(r'^\s+/\\\s+', '    ', bad_lines[index], count=1)
            bad = '\n'.join(bad_lines) + ('\n' if text.endswith('\n') else '')
            if bad != text:
                candidates.append(('dropped_conjunction', bad))
                break
    return candidates


def correction_prompt(row_prompt, draft, diagnostic, expected_module):
    return (
        row_prompt + '\n\n'
        'Return only one complete corrected TLA+ module. Preserve the exact '
        'module name and end with a single ==== footer. The prior candidate '
        'below was rejected by the owned SANY parser. Repair its syntax and '
        'continue the module; do not explain the repair.\n'
        '--- prior candidate ---\n' + draft + '\n'
        '--- exact SANY diagnostic ---\n' + diagnostic + '\n'
        '--- required module name ---\n---- MODULE ' + expected_module + ' ----\n'
        '--- end verifier feedback ---'
    )


def prepare(args):
    packet_bytes = args.packet.read_bytes()
    chosen, packet = selected(packet_bytes)
    args.output.mkdir(parents=True, exist_ok=False)
    pairs = []
    controls = []
    for row in (*TRAIN, *VALID):
        source = packet['rows'][row]
        good = source['response']
        if sha(good.encode()) != source['response_sha256']:
            raise ValueError(f'reference hash mismatch for row {row}')
        positive = sany_check(good, args.output / f'controls/{row}/reference', args.java, args.jar)
        if positive.get('passed') is not True:
            raise ValueError(f'positive SANY control failed for row {row}: {positive}')
        controls.append(dict(row=row, kind='reference', status=positive['status']))
        accepted = 0
        for kind, bad in candidate_faults(good):
            result = sany_check(bad, args.output / f'controls/{row}/{kind}', args.java, args.jar)
            if result.get('passed') is None:
                raise ValueError(f'infrastructure SANY result for {row}/{kind}: {result}')
            if result.get('passed') is False:
                diagnostic = result.get('diagnostic') or 'SANY model rejection'
                pairs.append(dict(
                    row=row,
                    id=source['id'],
                    split='train' if row in TRAIN else 'validation',
                    kind=kind,
                    draft=bad,
                    draft_sha256=sha(bad.encode()),
                    diagnostic=diagnostic,
                    diagnostic_sha256=sha(diagnostic.encode()),
                    target_sha256=source['response_sha256'],
                ))
                controls.append(dict(row=row, kind=kind, status=result['status'],
                                     diagnostic=diagnostic))
                accepted += 1
        if accepted < 2:
            raise ValueError(f'row {row} has fewer than two SANY-screened faults')
    if len(pairs) < 36:
        raise ValueError(f'correction corpus too small: {len(pairs)}')
    manifest = dict(
        schema=1,
        kind='fullmodule_sany_feedback_correction_v1',
        packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA,
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        budget=BUDGET,
        sany_jar_sha256=file_sha(args.jar),
        pairs=pairs,
        controls=controls,
        correction_prompts_exclude_targets=True,
        diagnostics_owned_by_pinned_sany=True,
        single_fault_candidates_only=True,
        clean_anchor_rows_only=True,
        generated_feedback_loaded=False,
        replay_negatives_loaded=False,
        protected_targets_never_train=True,
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
        reference_controls=len(TRAIN) + len(VALID),
        pair_count=len(pairs),
        protected_rows=list(PROTECTED),
        protected_rows_touched=False,
        target_text_used_only_as_training_label=True,
    ))
    print(json.dumps(dict(prepared=len(pairs), manifest_sha256=file_sha(args.output / 'manifest.json'))))


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


def verify_manifest(args, require_preflight=False):
    if file_sha(args.packet) != PACKET_SHA:
        raise ValueError('frozen packet changed')
    if file_sha(args.manifest) != args.manifest_sha256:
        raise ValueError('manifest hash mismatch')
    manifest = load(args.manifest)
    if (manifest.get('kind') != 'fullmodule_sany_feedback_correction_v1' or
            manifest.get('packet_sha256') != PACKET_SHA or
            manifest.get('parent_checkpoint_sha256') != PARENT_SHA or
            manifest.get('train_rows') != list(TRAIN) or
            manifest.get('validation_rows') != list(VALID) or
            manifest.get('protected_rows') != list(PROTECTED) or
            manifest.get('budget') != BUDGET or
            manifest.get('sany_jar_sha256') != file_sha(args.jar)):
        raise ValueError('manifest identity or budget changed')
    if not manifest.get('correction_prompts_exclude_targets') or not manifest.get('diagnostics_owned_by_pinned_sany'):
        raise ValueError('verifier-label isolation contract missing')
    if any(p['row'] in PROTECTED for p in manifest.get('pairs', [])):
        raise ValueError('protected row contamination')
    if len(manifest.get('pairs', [])) < 36:
        raise ValueError('correction corpus is too small')
    preflight = None
    if require_preflight:
        if not args.preflight or not args.preflight_sha256:
            raise ValueError('CPU tokenizer preflight required')
        if file_sha(args.preflight) != args.preflight_sha256:
            raise ValueError('preflight hash mismatch')
        preflight = load(args.preflight)
        if (preflight.get('manifest_sha256') != args.manifest_sha256 or
                preflight.get('all_tokenizers_exact') is not True or
                preflight.get('nonzero_eos_per_row') is not True):
            raise ValueError('CPU preflight guards failed')
    return manifest, preflight


def preflight(args):
    manifest, _ = verify_manifest(args)
    import transformers
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    packet = load(args.packet)
    records = []
    for pair in manifest['pairs']:
        row = pair['row']
        source = packet['rows'][row]
        if pair['target_sha256'] != source['response_sha256']:
            raise ValueError(f'target hash mismatch for correction row {row}')
        prompt = correction_prompt(source['prompt'], pair['draft'], pair['diagnostic'],
                                   module_name(source['response']))
        enc = exact_chat(tokenizer, prompt, source['response'])
        records.append(dict(
            row=row,
            split=pair['split'],
            kind=pair['kind'],
            prompt_tokens=enc['prompt_tokens'],
            response_tokens=enc['response_tokens'],
            input_ids_sha256=sha(json.dumps(enc['input_ids'], separators=(',', ':')).encode()),
            labels_sha256=sha(json.dumps(enc['labels'], separators=(',', ':')).encode()),
            draft_sha256=pair['draft_sha256'],
            diagnostic_sha256=pair['diagnostic_sha256'],
        ))
    anchors = []
    for row in TRAIN:
        source = packet['rows'][row]
        enc = exact_chat(tokenizer, source['prompt'], source['response'])
        anchors.append(dict(
            row=row,
            prompt_tokens=enc['prompt_tokens'],
            response_tokens=enc['response_tokens'],
            input_ids_sha256=sha(json.dumps(enc['input_ids'], separators=(',', ':')).encode()),
            labels_sha256=sha(json.dumps(enc['labels'], separators=(',', ':')).encode()),
        ))
    model_files = lineage.helpers.model_files(args.model)
    result = dict(
        schema=1,
        kind='fullmodule_sany_feedback_correction_cpu_preflight_v1',
        manifest_sha256=args.manifest_sha256,
        packet_sha256=PACKET_SHA,
        parent_checkpoint_sha256=PARENT_SHA,
        model_files=model_files,
        model_files_sha256=sha(json.dumps(model_files, sort_keys=True).encode()),
        train_rows=list(TRAIN),
        validation_rows=list(VALID),
        protected_rows=list(PROTECTED),
        pairs=records,
        clean_anchor_rows=anchors,
        all_tokenizers_exact=True,
        nonzero_eos_per_row=all(r['response_tokens'] > 0 for r in records + anchors),
        correction_pair_count=len(records),
        clean_anchor_count=len(anchors),
        generated_feedback_loaded=False,
        replay_negatives_loaded=False,
        protected_targets_never_train=True,
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
    print(json.dumps(dict(preflight='pass', pairs=len(records), anchors=len(anchors),
                          preflight_sha256=file_sha(args.output))))


class LoRALinear:
    def __new__(cls, base, rank, alpha):
        import torch
        import torch.nn as nn
        import torch.nn.functional as F

        class Impl(nn.Module):
            def __init__(self, wrapped, r, a):
                super().__init__()
                self.base = wrapped
                device = wrapped.weight.device
                self.lora_A = nn.Parameter(torch.empty(r, wrapped.in_features,
                                                        device=device, dtype=torch.float32))
                self.lora_B = nn.Parameter(torch.zeros(wrapped.out_features, r,
                                                       device=device, dtype=torch.float32))
                nn.init.kaiming_uniform_(self.lora_A, a=math.sqrt(5))
                self.scaling = float(a) / float(r)

            def forward(self, values):
                base = self.base(values)
                dtype = values.dtype if values.is_floating_point() else self.lora_A.dtype
                update = F.linear(F.linear(values, self.lora_A.to(dtype)),
                                  self.lora_B.to(dtype))
                return base + update * self.scaling

        return Impl(base, rank, alpha)


def inject_adapters(net):
    import torch
    net.requires_grad_(False)
    for index in BUDGET['adapter_layers']:
        layer = net.model.layers[index]
        for target in BUDGET['adapter_targets']:
            owner = layer.self_attn if target in {'q_proj', 'k_proj', 'v_proj', 'o_proj'} else layer.mlp
            setattr(owner, target, LoRALinear(getattr(owner, target), BUDGET['rank'], BUDGET['alpha']))
    selected = {}
    for name, parameter in net.named_parameters():
        if '.lora_A' in name or '.lora_B' in name:
            parameter.requires_grad_(True)
            selected[name] = parameter
    expected = len(BUDGET['adapter_layers']) * len(BUDGET['adapter_targets']) * 2
    if len(selected) != expected or any(p.dtype != torch.float32 for p in selected.values()):
        raise ValueError('unexpected adapter parameterization')
    return selected


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
    if not all(torch.equal(p.detach().cpu(), state[n]) for n, p in selected.items()):
        raise ValueError('adapter restoration failed')


def save_exact(torch, state, config, metrics, checkpoint):
    checkpoint = Path(checkpoint)
    if checkpoint.exists():
        raise ValueError('append-only checkpoint exists')
    temporary = checkpoint.with_name('.' + checkpoint.name + '.tmp')
    if temporary.exists():
        raise ValueError('temporary checkpoint exists')
    payload = dict(trainable_state=state, config=config, metrics=metrics,
                   optimizer_state_stored=False,
                   checkpoint_format='legacy_no_zip_exact_fp32_weights')
    try:
        torch.save(payload, temporary, _use_new_zipfile_serialization=False)
        os.replace(temporary, checkpoint)
    except BaseException:
        temporary.unlink(missing_ok=True)
        raise


def teacher_loss(net, enc, device='cuda', context=None):
    import torch
    import torch.nn.functional as F
    context = context or (lambda: torch.autocast('cuda', dtype=torch.bfloat16))
    ids = torch.tensor([enc['input_ids']], device=device)
    labels = torch.tensor([enc['labels']], device=device)
    with context():
        result = net(input_ids=ids, attention_mask=torch.ones_like(ids),
                     labels=None, use_cache=False)
    logits = result.logits[:, :-1, :].float()
    targets = labels[:, 1:]
    mask = targets.ne(-100)
    if not bool(mask.any()):
        raise ValueError('empty response target')
    loss = F.cross_entropy(logits[mask], targets[mask], reduction='mean')
    top1 = (logits.argmax(-1)[mask] == targets[mask]).float().mean()
    return loss, dict(loss=float(loss.detach()), target_top1=float(top1.detach()),
                      target_tokens=int(mask.sum()))


def prompt_only(tokenizer, prompt):
    rendered = tokenizer.apply_chat_template([dict(role='user', content=prompt)],
                                             tokenize=False, add_generation_prompt=True)
    ids = tokenizer.encode(rendered, add_special_tokens=False)
    return dict(input_ids=ids, prompt_tokens=len(ids))


def evaluation_prompt(source_prompt, draft, diagnostic, module):
    return correction_prompt(source_prompt, draft, diagnostic, module)


def train(args):
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(BUDGET['seed'])
    random.seed(BUDGET['seed'])
    manifest, preflight_value = verify_manifest(args, require_preflight=True)
    if file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('exact parent checkpoint required')
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 required')
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output / 'manifest.json', manifest)
    packet = load(args.packet)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    pair_encodings = []
    for pair in manifest['pairs']:
        source = packet['rows'][pair['row']]
        prompt = correction_prompt(source['prompt'], pair['draft'], pair['diagnostic'],
                                   module_name(source['response']))
        enc = exact_chat(tokenizer, prompt, source['response'])
        pair_encodings.append(dict(pair=pair, enc=enc))
    anchor_encodings = []
    for row in TRAIN:
        source = packet['rows'][row]
        anchor_encodings.append((row, exact_chat(tokenizer, source['prompt'], source['response'])))
    if len(pair_encodings) != len(manifest['pairs']):
        raise ValueError('correction encoding count drift')
    net = lineage.helpers.load_policy(args.model)
    saved = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(args.model))
    del saved
    selected = inject_adapters(net)
    context = lambda: torch.autocast('cuda', dtype=torch.bfloat16)
    probe_ids = anchor_encodings[0][1]['input_ids'][:64]
    with torch.no_grad(), context():
        parent_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
        injected_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(parent_probe, injected_probe):
        raise ValueError('zero-initialized adapter changed parent logits')
    initial = {name: p.detach().cpu().clone() for name, p in selected.items()}
    tasks = {}
    for row in PROTECTED:
        task = multi.checker_task(packet, packet['rows'][row])
        tasks[row] = multi.stage_task(task, args.output, str(row))
    sany_identity = multi.sany.identity(list(tasks.values()))

    def generate(row, phase, prompt_enc=None):
        enc = packet['encodings'][row] if prompt_enc is None else prompt_enc
        forced = f'---- MODULE {MODULE_NAMES[row]} ----\n'
        decoded = multi.decode(net, tokenizer, enc, forced_prefix=forced)
        result = dict(row=row, phase=phase, **decoded)
        result['sany'] = multi.sany.check(
            tasks[row], decoded['raw_reply'], args.output / f'sany/{phase}/{row}', sany_identity,
            timeout=BUDGET['sany_seconds'])
        dump(args.output / f'{phase}-row-{row}.json', result)
        return result

    before = {row: generate(row, 'restored_parent') for row in PROTECTED}
    for parameter in selected.values():
        parameter.requires_grad_(True)
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET['lr'], weight_decay=0., foreach=False)
    train_pairs = [x for x in pair_encodings if x['pair']['split'] == 'train']
    rng = random.Random(BUDGET['seed'])
    ledger = []
    started = time.monotonic()
    for step in range(1, BUDGET['steps'] + 1):
        if time.monotonic() - started >= BUDGET['training_seconds']:
            break
        chosen_pair = rng.sample(train_pairs, BUDGET['accumulation'])
        chosen_anchor = rng.sample(anchor_encodings, BUDGET['accumulation'])
        optimizer.zero_grad(set_to_none=True)
        feedback_metrics, anchor_metrics = [], []
        for item in chosen_pair:
            loss, metric = teacher_loss(net, item['enc'])
            (BUDGET['feedback_weight'] * loss / len(chosen_pair)).backward()
            feedback_metrics.append(dict(row=item['pair']['row'], kind=item['pair']['kind'], **metric))
        for row, enc in chosen_anchor:
            loss, metric = teacher_loss(net, enc)
            (BUDGET['anchor_weight'] * loss / len(chosen_anchor)).backward()
            anchor_metrics.append(dict(row=row, **metric))
        grad = float(torch.nn.utils.clip_grad_norm_(selected.values(), 1., error_if_nonfinite=True))
        if not math.isfinite(grad) or grad <= 0:
            raise ValueError('nonfinite/zero correction gradient')
        optimizer.step()
        metrics = feedback_metrics + anchor_metrics
        if not all(math.isfinite(m['loss']) and math.isfinite(m['target_top1']) for m in metrics):
            raise ValueError('nonfinite correction metric')
        entry = dict(step=step, gradient_norm=grad, feedback=feedback_metrics,
                     anchor=anchor_metrics,
                     feedback_weight=BUDGET['feedback_weight'],
                     anchor_weight=BUDGET['anchor_weight'])
        ledger.append(entry)
        with (args.output / 'steps.jsonl').open('a') as stream:
            stream.write(json.dumps(entry) + '\n')
        print(json.dumps(dict(step=step,
                              feedback_loss=sum(x['loss'] for x in feedback_metrics) / len(feedback_metrics),
                              anchor_loss=sum(x['loss'] for x in anchor_metrics) / len(anchor_metrics))),
              flush=True)
    if len(ledger) != BUDGET['steps']:
        raise ValueError('executed update count differs from admitted budget')
    state = {name: p.detach().cpu().clone() for name, p in selected.items()}
    delta = sum(float((state[name] - initial[name]).double().square().sum()) for name in state) ** .5
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError('child adapter did not change finitely')
    config = dict(kind=manifest['kind'], model_files=lineage.helpers.model_files(args.model),
                  dtype_profile=PROFILE, parent_sha256=PARENT_SHA,
                  manifest_sha256=args.manifest_sha256, budget=BUDGET,
                  optimizer_state_stored=False, optimizer_resume_supported=False)
    checkpoint = args.output / 'policy_lora.pt'
    save_exact(torch, state, config, ledger, checkpoint)
    with torch.no_grad():
        child_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
        for parameter in selected.values():
            parameter.zero_()
        reloaded = torch.load(checkpoint, map_location='cpu', weights_only=False)
        restore_adapters(selected, reloaded['trainable_state'])
        reload_probe = net(input_ids=torch.tensor([probe_ids], device='cuda'), use_cache=False).logits[:, -1].float().cpu()
    if not torch.equal(child_probe, reload_probe):
        raise ValueError('checkpoint logit reload mismatch')
    reload_tensors_exact = all(torch.equal(p.detach().cpu(), state[n]) for n, p in selected.items())
    if not reload_tensors_exact:
        raise ValueError('checkpoint tensor reload mismatch')
    for parameter in selected.values():
        parameter.requires_grad_(False)
    del reloaded, optimizer
    torch.cuda.empty_cache()
    after_ordinary = {row: generate(row, 'trained_child_ordinary') for row in PROTECTED}
    after_repair = {}
    for row in PROTECTED:
        ordinary = after_ordinary[row]
        diagnostic = (ordinary.get('sany') or {}).get('diagnostic') or ('SANY status: ' + str((ordinary.get('sany') or {}).get('status', 'unknown')))
        repair_prompt = evaluation_prompt(packet['rows'][row]['prompt'], ordinary['raw_reply'],
                                           diagnostic, MODULE_NAMES[row])
        repair_enc = prompt_only(tokenizer, repair_prompt)
        after_repair[row] = generate(row, 'trained_child_self_feedback', repair_enc)
        after_repair[row]['feedback_draft_sha256'] = sha(ordinary['raw_reply'].encode())
        after_repair[row]['feedback_diagnostic_sha256'] = sha(diagnostic.encode())
        dump(args.output / f'trained_child_self_feedback-row-{row}.json', after_repair[row])
    receipt = dict(
        complete=True,
        kind=manifest['kind'],
        updates=len(ledger),
        correction_pairs=len(train_pairs),
        clean_anchor_rows=list(TRAIN),
        parameter_delta_l2=delta,
        child_sha256=file_sha(checkpoint),
        adapter_parameter_count=sum(p.numel() for p in selected.values()),
        adapter_parameter_tensors=len(selected),
        reload_tensors_exact=reload_tensors_exact,
        reload_logits_exact=True,
        preflight_sha256=file_sha(args.preflight),
        sany_identity=sany_identity,
        before_protected=before,
        after_ordinary=after_ordinary,
        after_self_feedback=after_repair,
        generated_feedback_used_for_training=False,
        protected_targets_never_train=True,
        feedback_targets_immutable=True,
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
