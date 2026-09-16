"""SANY-screened semantic-span preferences, with real checkpoint restoration.

This bounded diagnostic trains on complete response-local semantic spans rather
than one first-divergence token.  Each negative is a declared-name binder
shadow candidate rejected by pinned SANY, while the clean span is retained as
the multi-token target.  Protected rows remain a fixed holdout.
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
import time

PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
PARENT_SHA = '87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511'
TRAIN = (42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58)
VALID = (59, 60, 61, 62, 63, 64)
PROTECTED = (47, 107)
PROFILE = 'frozen bf16 base with float32 final transformer layer; bf16 autocast'
BUDGET = dict(steps=12, accumulation=2, lr=5e-7, margin=1., anchor_weight=.25,
              seed=20260916, training_seconds=480, max_prefix_tokens=2048,
              max_new_tokens=2048, generation_seconds=60, sany_seconds=30,
              objective='multi_token_verifier_guided_semantic_span')

QUANTIFIER = re.compile(r"\\[AE] ([A-Za-z_][A-Za-z0-9_]*) \\in")
IDENTIFIER = re.compile(r"(?<![A-Za-z0-9_\\])([A-Za-z_][A-Za-z0-9_]*)(?![A-Za-z0-9_])")


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(8 * 1024**2), b''):
            h.update(chunk)
    return h.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def save_exact_weights(torch, payload, checkpoint):
    """Atomically write the exact fp32 child without optimizer-state bulk."""
    checkpoint = Path(checkpoint)
    if checkpoint.exists():
        raise ValueError('append-only checkpoint already exists')
    temporary = checkpoint.with_name('.' + checkpoint.name + '.tmp')
    if temporary.exists():
        raise ValueError('temporary checkpoint already exists')
    try:
        torch.save(payload, temporary, _use_new_zipfile_serialization=False)
        os.replace(temporary, checkpoint)
    except BaseException:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass
        raise


def module_name(text):
    m = re.search(r'^-+ MODULE (\w+) -+\s*$', text, re.M)
    if not m:
        raise ValueError('canonical module header required')
    return m[1]


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
            p = subprocess.run([java, '-cp', str(Path(jar).resolve()), 'tla2sany.SANY',
                                name + '.tla'], cwd=output, capture_output=True,
                               text=True, timeout=BUDGET['sany_seconds'])
            log = p.stdout + p.stderr
            (output / 'sany.log').write_text(log)
            # SANY prints semantic.AbortException for ordinary parser rejects.
            # Explicit parser diagnostics take precedence over that exception.
            if re.search(r'\*\*\*\s*(?:Parse|Semantic)|Fatal errors|Parse Error|Semantic errors', log, re.I):
                result = dict(status='model_reject', passed=False, returncode=p.returncode)
            elif re.search(r'Exception|Could not find|NoClassDef|OutOfMemory', log):
                result = dict(status='infrastructure_error', passed=None, returncode=p.returncode)
            elif p.returncode == 0 and 'Semantic processing of module ' + name in log:
                result = dict(status='pass', passed=True, returncode=0)
            else:
                result = dict(status='infrastructure_unknown', passed=None, returncode=p.returncode)
        except subprocess.TimeoutExpired:
            result = dict(status='infrastructure_timeout', passed=None)
    dump(output / 'result.json', result)
    return result


def semantic_span_candidates(text):
    """Build one bounded same-line semantic shadow candidate.

    The binder and its uses must share a source line.  This is intentionally
    narrower than a TLA+ parser; SANY remains the admission oracle.
    """
    lines = text.splitlines(keepends=True)
    declared = []
    for line in lines:
        match = re.match(r'(?:CONSTANTS?|VARIABLES?)\s+(.+)', line)
        if match:
            declared.extend(re.findall(r'[A-Za-z_][A-Za-z0-9_]*', match.group(1)))
    candidates = []
    for index, line in enumerate(lines):
        match = QUANTIFIER.search(line)
        if not match or len(QUANTIFIER.findall(line)) != 1:
            continue
        bound = match.group(1)
        outer = next((name for name in declared if name != bound), None)
        if outer is None:
            continue
        updated = IDENTIFIER.sub(
            lambda item: outer if item.group(1) == bound else item.group(1), line
        )
        if updated != line and QUANTIFIER.search(updated):
            candidates.append((
                'semantic_binder_span', line, ''.join(lines[:index] + [updated] + lines[index + 1:])
            ))
    return candidates


def first_divergence(good, bad, prompt_length):
    i = next((i for i, (a, b) in enumerate(zip(good, bad)) if a != b), None)
    if i is None or i < prompt_length or i == 0 or i > BUDGET['max_prefix_tokens']:
        raise ValueError('invalid response-only contrastive boundary')
    return dict(prefix=good[:i], positive=good[i], negative=bad[i])


def prepare(args):
    raw = args.packet.read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError('frozen packet changed')
    p = json.loads(raw)
    args.output.mkdir(parents=True, exist_ok=False)
    pairs = []
    for row in TRAIN + VALID:
        source = p['rows'][row]
        good = source['response']
        if sha(good.encode()) != source['response_sha256']:
            raise ValueError('reference hash mismatch')
        control = sany(good, args.output / f'controls/{row}/positive', args.java, args.jar)
        if control['passed'] is not True:
            raise ValueError(f'positive SANY control failed for {row}: {control}')
        candidates = semantic_span_candidates(good)
        if not candidates:
            continue
        kind, span_text, bad = candidates[0]
        control = sany(bad, args.output / f'controls/{row}/{kind}', args.java, args.jar)
        if control['passed'] is not False:
            raise ValueError(f'negative SANY control not rejected: {row}/{kind}')
        pairs.append(dict(row=row, id=source['id'], split='train' if row in TRAIN else 'validation',
                          kind=kind, positive_sha256=sha(good.encode()), span_text=span_text,
                          negative=bad, negative_sha256=sha(bad.encode()),
                          candidate_count=len(candidates), selected_candidate=0))
    manifest = dict(kind='fullmodule_semantic_span_preference_v1', span_objective=True,
                    packet_sha256=PACKET_SHA,
                    parent_checkpoint_sha256=PARENT_SHA, train_rows=list(TRAIN),
                    validation_rows=list(VALID), protected_rows=list(PROTECTED),
                    budget=BUDGET, sany_jar_sha256=file_sha(args.jar), pairs=pairs,
                    semantic_corruption='same-line declared-name quantifier shadow, real SANY screened',
                    no_protected_training=True, generated_feedback_loaded=False,
                    replay_negatives_loaded=False, gate_claim=False,
                    quality_claim=False, proof_claim=False, generalization_claim=False,
                    tlc_claim=False, nonvacuity_claim=False)
    dump(args.output / 'manifest.json', manifest)
    print(json.dumps(dict(prepared=len(pairs), manifest_sha256=file_sha(args.output / 'manifest.json'))))


def restore(selected, saved):
    import torch
    state = saved['trainable_state']
    if set(selected) != set(state):
        raise ValueError('checkpoint parameter names mismatch')
    with torch.no_grad():
        for name, param in selected.items():
            tensor = state[name]
            if tensor.dtype != torch.float32 or tensor.shape != param.shape or not torch.isfinite(tensor).all():
                raise ValueError('checkpoint tensor mismatch: ' + name)
            param.copy_(tensor)
    if not all(torch.equal(p.detach().cpu(), state[n]) for n, p in selected.items()):
        raise ValueError('actual checkpoint restoration failed')


def preference_loss(scores, positive, negative):
    import torch.nn.functional as F
    margin = scores[positive] - scores[negative]
    anchor = -F.log_softmax(scores, dim=-1)[positive]
    return F.softplus(BUDGET['margin'] - margin) + BUDGET['anchor_weight'] * anchor, margin


def train(args):
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(BUDGET['seed'])
    random.seed(BUDGET['seed'])
    if file_sha(args.manifest) != args.manifest_sha256 or file_sha(args.packet) != PACKET_SHA:
        raise ValueError('manifest/packet mismatch')
    manifest = json.loads(args.manifest.read_text())
    expected_budget = BUDGET
    if (manifest['train_rows'] != list(TRAIN) or manifest['validation_rows'] != list(VALID)
            or manifest['budget'] != expected_budget or manifest['sany_jar_sha256'] != file_sha(args.jar)):
        raise ValueError('training partition, budget or SANY identity changed')
    if file_sha(args.checkpoint) != PARENT_SHA:
        raise ValueError('actual policy checkpoint mismatch')
    if not torch.cuda.is_available() or not torch.cuda.is_bf16_supported():
        raise ValueError('CUDA bf16 required')
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output / 'manifest.json', manifest)
    packet = json.loads(args.packet.read_text())
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model, local_files_only=True)
    pairs = []
    for pair in manifest['pairs']:
        row = pair['row']
        if row not in TRAIN + VALID or pair['split'] != ('train' if row in TRAIN else 'validation'):
            raise ValueError('protected-row contamination')
        source, enc = packet['rows'][row], packet['encodings'][row]
        if pair['positive_sha256'] != sha(source['response'].encode()) or pair['negative_sha256'] != sha(pair['negative'].encode()):
            raise ValueError('pair text identity changed')
        def encode(answer):
            messages = [dict(role='user', content=source['prompt']), dict(role='assistant', content=answer)]
            text = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=False)
            return tokenizer.encode(text, add_special_tokens=False)
        good, bad = encode(source['response']), encode(pair['negative'])
        if good != enc['input_ids']:
            raise ValueError('training tokenizer differs from frozen packet')
        if manifest.get('span_objective') is True:
            span_ids = tokenizer.encode(pair['span_text'], add_special_tokens=False)
            start = good.index(span_ids[0], enc['prompt_tokens'])
            # The negative deliberately replaces the first non-whitespace
            # character of this span, so its token sequence must differ.  The
            # response prefix before ``start`` is immutable and remains the
            # alignment anchor; searching for the original span in ``bad``
            # incorrectly rejects the intended corruption.
            bad_start = start
            if bad_start >= len(bad):
                raise ValueError('structured corruption missing anchored span')
            pairs.append(dict(row=row, kind=pair['kind'], split=pair['split'],
                              prefix=good[:start], positive_tokens=span_ids,
                              negative_tokens=bad[bad_start:bad_start + len(span_ids)],
                              structured=True))
        else:
            pairs.append(dict(row=row, kind=pair['kind'], split=pair['split'],
                              **first_divergence(good, bad, enc['prompt_tokens'])))
    for row in PROTECTED:
        source, enc = packet['rows'][row], packet['encodings'][row]
        text = tokenizer.apply_chat_template([dict(role='user', content=source['prompt'])],
                                             tokenize=False, add_generation_prompt=True)
        if tokenizer.encode(text, add_special_tokens=False) != enc['input_ids'][:enc['prompt_tokens']]:
            raise ValueError('protected inference tokenizer/prompt mismatch')
    dump(args.output / 'token_pairs.json', pairs)
    saved = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    files = {p.name: file_sha(p) for p in sorted(args.model.iterdir()) if p.is_file() and
             (p.suffix in ('.json', '.safetensors') or p.name in ('tokenizer.model', 'chat_template.jinja'))}
    if saved['config']['model_files'] != files or saved['config']['dtype_profile'] != PROFILE:
        raise ValueError('checkpoint base model/dtype configuration mismatch')
    net = transformers.AutoModelForCausalLM.from_pretrained(args.model, local_files_only=True,
            torch_dtype=torch.bfloat16, attn_implementation='sdpa').to('cuda').eval().requires_grad_(False)
    net.model.layers[-1].to(torch.float32)
    selected = {n: p for n, p in net.named_parameters() if n.startswith('model.layers.31.')}
    if len(selected) != 9:
        raise ValueError('expected nine final-layer tensors')
    context = lambda: torch.autocast('cuda', dtype=torch.bfloat16)
    def sequence_scores(input_ids, positions, *, offload=True):
        """Score selected causal positions in one teacher-forced sequence pass.

        The first structural-span runner called the full model once per target
        token.  That preserved the objective but made a 317-token validation
        span consume the whole bounded allocation.  Running the same positive
        sequence once and selecting hidden states at the causal prediction
        positions preserves the loss exactly while removing redundant model
        passes and the full-vocabulary output for unneeded positions.
        """
        ids = torch.tensor([input_ids], device='cuda')
        mask = torch.ones_like(ids)
        saved = torch.autograd.graph.save_on_cpu(pin_memory=False) if offload else contextlib.nullcontext()
        with saved, context():
            hidden = net.model(input_ids=ids, attention_mask=mask, use_cache=False).last_hidden_state[0]
            selected_hidden = hidden[torch.tensor(list(positions), device='cuda')]
            return net.lm_head(selected_hidden).float()

    def logits(prefix, *, offload=False):
        return sequence_scores(prefix, [len(prefix) - 1], offload=offload)[0]

    def structured_scores(pair, *, offload=False):
        count = min(len(pair['positive_tokens']), len(pair['negative_tokens']))
        if count <= 0 or not pair['prefix']:
            raise ValueError('nonempty aligned structural span and prefix required')
        prefix_length = len(pair['prefix'])
        positions = range(prefix_length - 1, prefix_length - 1 + count)
        return sequence_scores(pair['prefix'] + pair['positive_tokens'][:count], positions,
                               offload=offload)
    probe = pairs[0]['prefix']
    with torch.no_grad():
        base_logits = logits(probe).cpu()
    base_delta = sum(float((p.detach().cpu() - saved['trainable_state'][n]).double().square().sum())
                     for n, p in selected.items()) ** .5
    restore(selected, saved)
    initial = {n: p.detach().cpu().clone() for n, p in selected.items()}
    del saved
    with torch.no_grad():
        parent_logits = logits(probe).cpu()
    runtime = dict(parent_sha256=PARENT_SHA, restored_tensors_exact=True,
                   parent_vs_base_parameter_delta_l2=base_delta,
                   parent_vs_base_max_logit_difference=float((parent_logits-base_logits).abs().max()),
                   model_files=files, torch=torch.__version__, transformers=transformers.__version__,
                   cuda_device=torch.cuda.get_device_name(), interpreter=__import__('sys').executable,
                   runner_sha256=file_sha(__file__), training_tokenizer_exact=True,
                   protected_prompt_tokens_exact=True,
                   structural_span_scoring='single_teacher_forced_pass_selected_hidden_states')
    if base_delta == 0:
        raise ValueError('parent checkpoint is indistinguishable from base weights')
    dump(args.output / 'runtime.json', runtime)
    def evaluate_pairs():
        metrics = []
        with torch.no_grad():
            for pair in pairs:
                if pair.get('structured'):
                    scores = structured_scores(pair)
                    count = min(len(pair['positive_tokens']), len(pair['negative_tokens']))
                    offsets = torch.arange(count, device='cuda')
                    margins = (scores[offsets, torch.tensor(pair['positive_tokens'][:count], device='cuda')] -
                               scores[offsets, torch.tensor(pair['negative_tokens'][:count], device='cuda')])
                    metrics.append(dict(row=pair['row'], kind=pair['kind'], split=pair['split'],
                                        token_count=count, margin=float(margins.mean())))
                else:
                    scores = logits(pair['prefix'])
                    metrics.append(dict(row=pair['row'], kind=pair['kind'], split=pair['split'],
                                        margin=float(scores[pair['positive']] - scores[pair['negative']])))
        return metrics
    def generate(phase):
        results = []
        for row in PROTECTED:
            enc = packet['encodings'][row]
            ids = torch.tensor([enc['input_ids'][:enc['prompt_tokens']]], device='cuda')
            started = time.monotonic()
            with torch.inference_mode(), context():
                answer = net.generate(input_ids=ids, attention_mask=torch.ones_like(ids), do_sample=False,
                      max_new_tokens=BUDGET['max_new_tokens'], max_time=BUDGET['generation_seconds'],
                      eos_token_id=[128001, 128008, 128009], pad_token_id=128009, use_cache=True)
            tokens = answer[0, ids.shape[1]:].tolist()
            text = tokenizer.decode(tokens, skip_special_tokens=True)
            terminal = bool(tokens and tokens[-1] in (128001, 128008, 128009))
            result = dict(row=row, phase=phase, raw_reply=text, token_ids=tokens,
                          raw_reply_sha256=sha(text.encode()), seconds=time.monotonic()-started,
                          finish_reason='eos' if terminal else 'token_or_time_limit')
            result['sany'] = sany(text, args.output / f'sany/{phase}/{row}', args.java, args.jar)
            results.append(result)
            dump(args.output / f'{phase}-row-{row}.json', result)
        return results
    before_pairs = evaluate_pairs()
    before = generate('restored_parent')
    dump(args.output / 'before.json', dict(preferences=before_pairs, protected=before))
    torch.cuda.empty_cache()
    for p in selected.values():
        p.requires_grad_(True)
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET['lr'], weight_decay=0., foreach=False)
    train_pairs = [p for p in pairs if p['split'] == 'train']
    rng = random.Random(BUDGET['seed'])
    ledger = []
    started = time.monotonic()
    for step in range(BUDGET['steps']):
        if time.monotonic() - started >= BUDGET['training_seconds']:
            break
        chosen = rng.sample(train_pairs, BUDGET['accumulation'])
        optimizer.zero_grad(set_to_none=True)
        metrics = []
        for pair in chosen:
            if pair.get('structured'):
                import torch.nn.functional as F
                scores = structured_scores(pair, offload=True)
                count = min(len(pair['positive_tokens']), len(pair['negative_tokens']))
                offsets = torch.arange(count, device='cuda')
                positive = torch.tensor(pair['positive_tokens'][:count], device='cuda')
                negative = torch.tensor(pair['negative_tokens'][:count], device='cuda')
                margins = scores[offsets, positive] - scores[offsets, negative]
                losses = F.softplus(BUDGET['margin'] - margins) + BUDGET['anchor_weight'] * (
                    -F.log_softmax(scores, dim=-1)[offsets, positive])
                loss, margin = losses.mean(), margins.mean()
            else:
                scores = logits(pair['prefix'])
                loss, margin = preference_loss(scores, pair['positive'], pair['negative'])
            if not torch.isfinite(loss):
                raise ValueError('nonfinite contrastive loss')
            (loss / len(chosen)).backward()
            metrics.append(dict(row=pair['row'], kind=pair['kind'], loss=float(loss.detach()),
                                margin=float(margin.detach())))
        norm = float(torch.nn.utils.clip_grad_norm_(selected.values(), 1., error_if_nonfinite=True))
        if not norm > 0:
            raise ValueError('zero contrastive gradient')
        optimizer.step()
        entry = dict(step=step+1, gradient_norm=norm, examples=metrics)
        ledger.append(entry)
        with (args.output / 'steps.jsonl').open('a') as f:
            f.write(json.dumps(entry) + '\n')
        print(json.dumps(dict(step=step+1, loss=sum(m['loss'] for m in metrics)/len(metrics))), flush=True)
    if not ledger:
        raise ValueError('no optimizer update completed')
    state = {n: p.detach().cpu().clone() for n, p in selected.items()}
    delta = sum(float((state[n]-initial[n]).double().square().sum()) for n in state) ** .5
    if not math.isfinite(delta) or delta <= 0:
        raise ValueError('child weights did not change finitely')
    config = dict(kind=manifest['kind'], model_files=files, dtype_profile=PROFILE,
                  parent_sha256=PARENT_SHA, manifest_sha256=args.manifest_sha256, budget=BUDGET,
                  optimizer_state_stored=False, optimizer_resume_supported=False,
                  checkpoint_serialization='legacy_no_zip_exact_fp32_weights')
    checkpoint = args.output / 'policy_optimizer.pt'
    save_exact_weights(torch, dict(trainable_state=state, config=config, metrics=ledger), checkpoint)
    with torch.no_grad():
        child_logits = logits(probe).cpu()
        for p in selected.values():
            p.zero_()
        reload = torch.load(checkpoint, map_location='cpu', weights_only=False)
        restore(selected, reload)
        if not torch.equal(logits(probe).cpu(), child_logits):
            raise ValueError('saved checkpoint logit reload mismatch')
    del reload, optimizer
    for p in selected.values():
        p.requires_grad_(False)
    torch.cuda.empty_cache()
    after_pairs = evaluate_pairs()
    after = generate('trained_child')
    receipt = dict(complete=True, kind=manifest['kind'], updates=len(ledger), parameter_delta_l2=delta,
                   child_sha256=file_sha(checkpoint), reload_tensors_exact=True, reload_logits_exact=True,
                   structural_span_scoring='single_teacher_forced_pass_selected_hidden_states',
                   optimizer_state_stored=False, optimizer_resume_supported=False,
                   checkpoint_serialization='legacy_no_zip_exact_fp32_weights',
                   runtime=runtime, before_preferences=before_pairs, after_preferences=after_pairs,
                   before_protected=before, after_protected=after, gate_claim=False,
                   generalization_claim=False, tlc_claim=False, nonvacuity_claim=False, tlaps_claim=False)
    dump(args.output / 'receipt.json', receipt)
    print(json.dumps(dict(complete=True, updates=len(ledger), parameter_delta_l2=delta)), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=('prepare', 'train'))
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--jar', type=Path, required=True)
    parser.add_argument('--java', default='java')
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--manifest', type=Path)
    parser.add_argument('--manifest-sha256')
    parser.add_argument('--checkpoint', type=Path)
    parser.add_argument('--model', type=Path)
    args = parser.parse_args()
    if args.mode == 'train' and not all((args.manifest, args.manifest_sha256, args.checkpoint, args.model)):
        parser.error('train requires manifest/hash/checkpoint/model')
    (prepare if args.mode == 'prepare' else train)(args)
