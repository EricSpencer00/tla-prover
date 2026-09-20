"""Bounded matched multi-example full-module SANY discriminator.

Rows 44 and 49 are optimized in their fixed order.  Rows 47 and 107 are
decoded and checked only after the update.  This is a structural diagnostic,
not a generalization, TLC, non-vacuity, or proof gate.
"""
import argparse, json, math, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_sany_checks as sany

TRAIN_ROWS = (44, 49)
EVAL_ROWS = (47, 107)
ROW_IDS = {
    44: 'w4-fullmodule:w4opus::d0-m0-p1-t0',
    49: 'w4-fullmodule:w4opus::d1-m0-p0-t5',
    47: 'w4-fullmodule:w4opus::d2-m7-p4-t2',
    107: 'w4-fullmodule:w4opus::d3-m0-p0-t0',
}
RESPONSE_SHAS = {
    44: '1014e9b256c188e24ba4374d5125099d0af0475df5883896bdb41ca683bc7f94',
    49: '2167983adbb1e282fd81f4aeb4f6572acba44fa1db9abdb2e783c449cbd0c23c',
    47: '36c548d2a475c0d086ddf0340f927b36002699ce86e955d702e061324ad2f07c',
    107: '5f6b169dc010369d4e6f65b7766b7961e44a4df15790988c5763861a06e3e853',
}
PROMPT_SHAS = {
    44: 'edf78ead117f730819e6ee1b6b7058b01c648f3e6983f688f7ec5bbd0c7eceea',
    49: '92f72075fe6a6d07e1aafffaa3e8d4d560a056e8d5517bc33b5dd82aa98df732',
    47: '32eb750d7db375df72e8e93d929ac3e5c7a365d50a915202c62db6e3d675877f',
    107: '388d75fc27a48d38ccb3fd0258a72ddfd1b9dbb0852b0b058057521e8eaafb51',
}
INPUT_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
POLICY_SHA = 'fba2768ed9a8f629f6496dc1ef72763b32fc339c74ba9075d1ffc53acd6c2d1d'
BUDGET = dict(updates=128, lr=1e-5, seed=20261011, max_new_tokens=1024,
              item_seconds=45, sany_seconds=30, train_only=False,
              eval_rows=list(EVAL_ROWS), gate_claim=False,
              generalization_claim=False, proof_claim=False,
              tlc_claim=False, nonvacuity_claim=False)
SOURCES = tuple(sorted(set(lineage.SOURCES) | set(sany.SOURCES) |
                       {'tools/proof_fullmodule_multiexample_probe.py'}))


def load(path): return json.loads(Path(path).read_bytes())
def dump(path, value): lineage.helpers.dump(Path(path), value)
def sources(): return {n: lineage.helpers.file_sha(ROOT / n) for n in SOURCES}


def selected(raw):
    if lineage.helpers.sha(raw) != INPUT_SHA:
        raise ValueError('Exact immutable TRAIN169 packet required')
    value = json.loads(raw)
    rows = lineage.packet.validate_training_packet(value)
    encs = value['encodings']
    chosen = {}
    for i in (*TRAIN_ROWS, *EVAL_ROWS):
        row, enc = rows[i], encs[i]
        if row['id'] != ROW_IDS[i] or row['response_sha256'] != RESPONSE_SHAS[i] or row['prompt_sha256'] != PROMPT_SHAS[i]:
            raise ValueError(f'pinned row {i} changed')
        if row['split'] != 'train':
            raise ValueError(f'packet row {i} unexpectedly changed split')
        chosen[i] = (row, enc)
    return chosen, value


def checker_task(value, row):
    candidates = json.loads(value['audit_rows_bytes'])
    target_id = 'w4opus::' + row['id'].split('w4opus::', 1)[-1]
    target = next((x for x in candidates if x['id'] == target_id), None)
    if not target or target['exclusions']['status'] != 'lexically_clear':
        raise ValueError(f"pinned source missing or blocked: {row['id']}")
    raw = target['raw']; text = raw['spec_text']
    if lineage.helpers.sha(text.encode()) != row['response_sha256']:
        raise ValueError(f"pinned reference source changed: {row['id']}")
    return dict(id=target['id'], index=target['index'], module_name=raw['module'],
                dependencies={}, source_text=text, description_text=raw['nl'],
                config_text=raw['cfg_text'])


def stage_task(task, output, label):
    root = Path(output) / 'reference' / label
    root.mkdir(parents=True, exist_ok=False)
    paths = {}
    for key, name, text in (('source', task['module_name'] + '.tla', task['source_text']),
                            ('description', 'description.txt', task['description_text']),
                            ('config', 'configuration.cfg', task['config_text'])):
        path = root / name; path.write_text(text)
        paths[key] = dict(path=str(path), sha256=lineage.helpers.sha(text.encode()))
    return dict(id=task['id'], index=task['index'], module_name=task['module_name'],
                dependencies={}, **paths)


def output_fields(tokens, reply, elapsed, budget=None):
    tokens = list(tokens); eos = set(lineage.common.EOS_IDS)
    budget = BUDGET['max_new_tokens'] if budget is None else int(budget)
    if not all(type(x) is int and 0 <= x < 128256 for x in tokens):
        raise ValueError('Invalid generated token IDs')
    finish = ('eos' if tokens and tokens[-1] in eos and elapsed <= BUDGET['item_seconds']
              else 'token_limit' if len(tokens) >= budget else 'time_limit')
    return dict(token_ids=tokens, raw_reply=reply,
                raw_reply_sha256=lineage.helpers.sha(reply.encode()), output_tokens=len(tokens),
                finish_reason=finish, deadline_exceeded=elapsed > BUDGET['item_seconds'],
                elapsed_seconds=elapsed)


def suffix_ids(ids, suffix):
    """Return whether *ids* ends in the complete tokenized *suffix*.

    This deliberately operates on token ids rather than decoded text.  A
    decoded-string check can confuse a tokenizer's whitespace normalization
    with the actual generated stream, which is especially dangerous for the
    TLA+ module footer.
    """
    ids, suffix = list(ids), list(suffix)
    return bool(suffix) and len(ids) >= len(suffix) and ids[-len(suffix):] == suffix


class ForceEosAfterFooter:
    """Logits processor for an exact, model-generated module footer.

    The footer is never appended to a candidate.  Once the model has emitted
    all footer token ids, this processor makes the next sampled token the
    configured EOS token.  ``prompt_tokens`` is the original prompt length;
    the generated stream therefore includes any pinned header prefix.
    """

    def __init__(self, footer_ids, eos_token_id, prompt_tokens):
        self.footer_ids = tuple(int(x) for x in footer_ids)
        self.eos_token_id = int(eos_token_id)
        self.prompt_tokens = int(prompt_tokens)
        if not self.footer_ids:
            raise ValueError('footer tokenization must not be empty')
        if self.eos_token_id < 0:
            raise ValueError('EOS token id must be non-negative')

    def __call__(self, input_ids, scores):
        # Keep this compatible with transformers' LogitsProcessor protocol,
        # while avoiding a hard import at module import time for CPU tests.
        for row, ids in enumerate(input_ids.tolist()):
            generated = ids[self.prompt_tokens:]
            if suffix_ids(generated, self.footer_ids):
                scores[row, :] = float('-inf')
                scores[row, self.eos_token_id] = 0.0
        return scores


def validate_pins(lineage_checkpoint, checkpoint, *, file_hash=lineage.helpers.file_sha):
    if file_hash(lineage_checkpoint) != lineage.CHILD_SHA:
        raise ValueError('Exact immutable8866 lineage checkpoint required')
    if file_hash(checkpoint) != POLICY_SHA:
        raise ValueError('Exact fba starting policy required')


def decode(net, tokenizer, enc, device='cuda', clock=time.monotonic, forced_prefix=None,
           do_sample=False, temperature=1.0, top_p=1.0):
    import torch
    prompt_tokens = int(enc['prompt_tokens'])
    prompt_ids = list(enc['input_ids'][:prompt_tokens])
    prefix_ids = []
    if forced_prefix:
        prefix_ids = tokenizer.encode(forced_prefix, add_special_tokens=False)
        if not prefix_ids:
            raise ValueError('forced module prefix tokenized to empty')
    # The prefix is supplied as context, not concatenated onto the decoded
    # reply after generation.  The returned slice starts at the original
    # prompt, so the prefix remains part of the model-produced token stream.
    ids = torch.tensor([prompt_ids + prefix_ids], device=device)
    footer_ids = tokenizer.encode('====', add_special_tokens=False)
    eos_id = tokenizer.eos_token_id
    if eos_id is None:
        raise ValueError('tokenizer has no EOS token required for footer stop')
    generation_budget = BUDGET['max_new_tokens'] + len(prefix_ids)
    if generation_budget <= 0:
        raise ValueError('pinned module prefix consumes the full output budget')
    try:
        from transformers import LogitsProcessorList
        processors = LogitsProcessorList([ForceEosAfterFooter(
            footer_ids, eos_id, prompt_tokens)])
    except ImportError:
        # Production workers have transformers.  Keeping this fallback makes
        # the decoder's accounting testable in lightweight environments.
        processors = [ForceEosAfterFooter(footer_ids, eos_id, prompt_tokens)]
    started = clock()
    with torch.inference_mode(), lineage.helpers.autocast(device):
        result = net.generate(input_ids=ids, attention_mask=torch.ones_like(ids),
            do_sample=do_sample, temperature=temperature if do_sample else 1.0,
            top_p=top_p if do_sample else 1.0, num_beams=1, num_return_sequences=1,
            max_new_tokens=generation_budget, max_time=BUDGET['item_seconds'],
            logits_processor=processors,
            no_repeat_ngram_size=8,
            pad_token_id=tokenizer.pad_token_id or tokenizer.eos_token_id)
    if device == 'cuda': torch.cuda.synchronize()
    elapsed = clock() - started
    # Slice at the original prompt, not the prefixed input.  This retains the
    # exact pinned header in the generated evidence without post-editing.
    tokens = lineage.common.trim_output(result[0, prompt_tokens:].tolist(), set(lineage.common.EOS_IDS))
    reply = lineage.common.decode_reply(tokenizer, tokens)
    return output_fields(tokens, reply, elapsed, budget=generation_budget)


def teacher(net, enc, device='cuda', context=None):
    import torch
    context = context or (lambda: lineage.helpers.autocast(device))
    ids = torch.tensor([enc['input_ids']], device=device)
    labels = torch.tensor([enc['labels']], device=device)
    with context(): result = net(input_ids=ids, attention_mask=torch.ones_like(ids), labels=labels, use_cache=False)
    target = labels[:, 1:]; predicted = result.logits[:, :-1].argmax(-1); mask = target.ne(-100)
    return result, dict(loss=float(result.loss.detach()), target_top1=float((predicted[mask] == target[mask]).float().mean().detach()))


def update(net, selected_t, train_encs, device='cuda', context=None, measure=lambda _: None):
    import torch
    context = context or (lambda: lineage.helpers.autocast(device))
    opt = torch.optim.AdamW(selected_t.values(), lr=BUDGET['lr'], weight_decay=0., foreach=False)
    rows = []
    for step in range(1, BUDGET['updates'] + 1):
        opt.zero_grad(set_to_none=True); metrics = []
        for enc in train_encs:  # fixed order, both examples contribute to each update
            result, metric = teacher(net, enc, device, context)
            (result.loss / len(train_encs)).backward(); metrics.append(metric); del result
        norms = lineage.gradients(selected_t)
        grad = float(torch.nn.utils.clip_grad_norm_(selected_t.values(), 1., error_if_nonfinite=True)); opt.step()
        measure('after_step_' + str(step))
        if not all(math.isfinite(x['loss']) and math.isfinite(x['target_top1']) for x in metrics) or not math.isfinite(grad) or not any(norms.values()):
            raise ValueError('Nonfinite/zero training evidence')
        rows.append(dict(step=step, loss=[x['loss'] for x in metrics], target_top1=[x['target_top1'] for x in metrics], gradient_norm=grad, gradient_norms=norms))
    return opt, rows


def admit(a):
    chosen, value = selected(a.input.read_bytes())
    values = {n: getattr(a, n) for n in (*lineage.PATHS, 'expected_input_sha256')}
    values['checkpoint'] = a.lineage_checkpoint
    base = lineage.admit(type('A', (), values)())
    if a.expected_input_sha256 != INPUT_SHA or base['input_sha256'] != INPUT_SHA: raise ValueError('Exact TRAIN lineage required')
    validate_pins(a.lineage_checkpoint, a.checkpoint)
    tasks = {str(i): checker_task(value, chosen[i][0]) for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    return dict(schema=1, kind='multiexample_structural_fullmodule_probe', budget=BUDGET,
        rows={'train': list(TRAIN_ROWS), 'eval': list(EVAL_ROWS)}, task_ids={str(i): ROW_IDS[i] for i in (*TRAIN_ROWS, *EVAL_ROWS)},
        encodings={str(i): chosen[i][1] for i in (*TRAIN_ROWS, *EVAL_ROWS)}, checker_tasks=tasks,
        packet_splits={str(i): chosen[i][0]['split'] for i in (*TRAIN_ROWS, *EVAL_ROWS)},
        lineage_admission_sha256=lineage.helpers.sha(json.dumps(base, sort_keys=True).encode()), input_sha256=INPUT_SHA,
        lineage_checkpoint_sha256=lineage.CHILD_SHA, policy_checkpoint_sha256=POLICY_SHA, source_sha256=sources(),
        training_authorized=True, protected_outputs_never_train=True, train_only=False, gate_claim=False,
        generalization_claim=False, proof_claim=False, tlc_claim=False, nonvacuity_claim=False)


def worker(a):
    import torch, transformers
    frozen = load(a.admission)
    if admit(a) != frozen: raise ValueError('Admission drift')
    out = a.output; out.mkdir(parents=True, exist_ok=False); dump(out / 'admission.json', frozen)
    tasks = {i: stage_task(frozen['checker_tasks'][str(i)], out, str(i)) for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    current = sany.identity(list(tasks.values()))
    tokenizer = transformers.AutoTokenizer.from_pretrained(str(a.model_path), local_files_only=True); net = lineage.helpers.load_policy(str(a.model_path))
    parent = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    selected_t = lineage.helpers.restore_policy(net, parent, lineage.helpers.model_files(a.model_path)); initial = {n: p.detach().cpu().clone() for n, p in selected_t.items()}; del parent
    selected_t = lineage.helpers.select_final_layer(net, True); encs = frozen['encodings']
    before = {str(i): teacher(net, encs[str(i)]) [1] for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    pre = {str(i): decode(net, tokenizer, encs[str(i)]) for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    opt, steps = update(net, selected_t, [encs[str(i)] for i in TRAIN_ROWS]); after = {str(i): teacher(net, encs[str(i)])[1] for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    post = {str(i): decode(net, tokenizer, encs[str(i)]) for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    config = dict(frozen, model_files=lineage.helpers.model_files(a.model_path), dtype_profile=lineage.helpers.PROFILE)
    saved = lineage.helpers.save_reload(net, selected_t, opt, initial, config, steps, encs[str(TRAIN_ROWS[0])]['input_ids'][:64], out / 'policy_optimizer.pt', 'cuda')
    reference = {str(i): sany.check(tasks[i], frozen['checker_tasks'][str(i)]['source_text'], out / 'sany_reference' / str(i), current, timeout=BUDGET['sany_seconds']) for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    candidate = {str(i): (sany.check(tasks[i], post[str(i)]['raw_reply'], out / 'sany_candidate' / str(i), current, timeout=BUDGET['sany_seconds']) if post[str(i)]['finish_reason'] == 'eos' else None) for i in (*TRAIN_ROWS, *EVAL_ROWS)}
    delta = sum(float((p.detach().cpu() - initial[n]).double().square().sum()) for n, p in selected_t.items()) ** .5
    receipt = dict(complete=True, updates=128, parameter_delta_l2=delta, reload=saved, before_teacher=before, after_teacher=after,
                   pre=pre, post=post, reference=reference, candidate=candidate, train_rows=list(TRAIN_ROWS), eval_rows=list(EVAL_ROWS),
                   train_only=False, gate_claim=False, generalization_claim=False, proof_claim=False, tlc_claim=False, nonvacuity_claim=False,
                   reference_sany_pass={i: reference[str(i)]['sany'] == 1 for i in (*TRAIN_ROWS, *EVAL_ROWS)},
                   candidate_sany_pass={i: bool(candidate[str(i)] and candidate[str(i)]['sany'] == 1) for i in (*TRAIN_ROWS, *EVAL_ROWS)})
    dump(out / 'steps.json', steps); dump(out / 'receipt.json', receipt); return receipt


def main():
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('mode', choices=('admit', 'worker'))
    for n in (*lineage.PATHS, 'output'): p.add_argument('--' + n.replace('_', '-'), type=Path, required=True)
    p.add_argument('--lineage-checkpoint', type=Path, required=True); p.add_argument('--expected-input-sha256', required=True); p.add_argument('--admission', type=Path)
    a = p.parse_args()
    if a.mode == 'admit':
        if a.output.exists(): raise ValueError('Admission output must not exist')
        dump(a.output, admit(a))
    else:
        if a.admission is None: p.error('--admission required')
        print(json.dumps(worker(a)))

if __name__ == '__main__': main()
