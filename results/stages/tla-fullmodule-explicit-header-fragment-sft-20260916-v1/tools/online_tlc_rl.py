#!/usr/bin/env python3
"""Online one-token Qwen action repair with actual SANY/TLC and mutation rewards.

Bounded curriculum experiment, never a full-spec or generalization score.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
import sys
import time

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))
from harness.corpora import normalize_tla, shingle_set, jaccard
from harness.runner import check_sany, check_tlc, module_name
from harness.mutation import mutant_verdict


def dump(path, obj):
    path.write_text(json.dumps(obj, indent=2) + '\n')


def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()


def known_model_type_error(log):
    """Only an evidenced TLC diagnostic, never a blanket classification of errors."""
    return bool(re.search(
        r'^Error: The (?:first|second) argument of [<>]=? should be an integer, but instead it is:',
        log, re.M))


def verify(text, cfg, mod, work):
    work.mkdir(parents=True, exist_ok=False)
    path = work / f'{mod}.tla'
    path.write_text(text)
    (work / f'{mod}.cfg').write_text(cfg)
    sany, out, _ = check_sany(path, work, 10)
    (work / 'sany.log').write_text(out)
    row = dict(sany=sany, tlc=None, vacuity=[], log_path=str(work))
    if sany == 'pass':
        tlc, vacuity, out, _ = check_tlc(mod, cfg, work, 10)
        (work / 'tlc.log').write_text(out)
        row.update(tlc=tlc, vacuity=vacuity,
                   model_type_error=tlc == 'error' and known_model_type_error(out),
                   mutation_verdict=mutant_verdict(tlc, out),
                   explicit_tlc_completion='Model checking completed. No error has been found' in out)
    return row


def action_mutants(text, mod):
    if mod == 'AdaptiveK':
        pairs = [("k' = AdaptiveK(newCat)", "k' = K_DEFAULT"),
                 ("k' = AdaptiveK(newCat)", "k' = K_TESTFAIL")]
    else:
        pairs = [("number' = number + 1", "number' = number + 2"),
                 ("number' = number - 1", "number' = number - 2")]
    mutants = []
    for i, (old, new) in enumerate(pairs):
        pattern = r'\s+'.join(re.escape(piece) for piece in old.split())
        if len(re.findall(pattern, text)) == 1:
            mutants.append((f'action-{i}', re.sub(pattern, lambda _: new, text, count=1)))
    return mutants


def reward_candidate(candidate, reference, cfg, mod, work):
    row = verify(candidate, cfg, mod, work)
    row['normalized_source_identity'] = normalize_tla(candidate) == normalize_tla(reference)
    row['cfg_sha256'] = sha(cfg)
    row['candidate_sha256'] = sha(candidate)
    row['reward'] = None
    row['terminal_pass'] = False
    if row['sany'] == 'fail':
        row['reward'] = 0.0
    elif row['sany'] == 'pass' and (row['tlc'] in ('fail_invariant', 'fail_deadlock', 'fail_liveness')
                                  or row.get('model_type_error', False)):
        row['reward'] = 0.25
    elif row['sany'] == 'pass' and row['tlc'] == 'pass':
        # No reward for a changed program whose intended semantics were not audited.
        if row['normalized_source_identity'] and not row['vacuity'] and row.get('explicit_tlc_completion'):
            mutants = []
            for label, text in action_mutants(candidate, mod):
                # Every invariant definition lies after this boundary; mutations
                # must affect only an action and preserve that entire suffix.
                boundary = 'InvAllowedSet ==' if mod == 'AdaptiveK' else 'TypeOK =='
                assert candidate.split(boundary, 1)[1] == text.split(boundary, 1)[1]
                mutants.append(verify(text, cfg, mod, work / label))
            row['action_mutants'] = mutants
            if len(mutants) == 2 and all(m['sany'] == 'pass' and m['tlc'] == 'fail_invariant' for m in mutants):
                safety = all(m['mutation_verdict']['safety_killed'] for m in mutants)
                row.update(reward=1.0 if safety else 0.6, terminal_pass=safety,
                           semantic_audit='curriculum_contract_restored',
                           safety_mutation_adequate=safety,
                           partial_reward_only=not safety)
    return row


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--steps', type=int, default=6)
    p.add_argument('--group-size', type=int, default=12)
    p.add_argument('--seed', type=int, default=20260906)
    p.add_argument('--seconds', type=int, default=480)
    p.add_argument('--lr', type=float, default=1e-5)
    p.add_argument('--temperature', type=float, default=1.25)
    p.add_argument('--task-indices', default='4,5,2,3,0,1',
                   help='Training curriculum order, indices 0-5; evaluation stays fixed')
    p.add_argument('--device', default='mps', choices=['mps', 'cpu', 'cuda'])
    p.add_argument('--model-path', type=Path)
    p.add_argument('--resume', type=Path, required=True)
    p.add_argument('--output', type=Path)
    p.add_argument('--holdout-corpus', type=Path, default=Path('/Users/eric/GitHub/tla_benchmark/data/tla_files'))
    a = p.parse_args()
    order = [int(x) for x in a.task_indices.split(',')]
    if not order or any(i not in range(6) for i in order):
        p.error('task indices must be in 0..5; retention task cannot be trained')
    assert 1 <= a.steps <= 100 and 2 <= a.group_size <= 64 and a.temperature > 0
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    import torch
    import transformers
    from transformers import AutoModelForCausalLM, AutoTokenizer
    start = time.monotonic()
    out = a.output or REPO / 'results/runs' / time.strftime('online-tlc-rl-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    print('RUN_DIR=' + str(out), flush=True)
    (out / 'trainer.py').write_text(Path(__file__).read_text())
    sources = ['CAPHTECH/kiri/docs/formal/AdaptiveK.tla',
               'fabracht/tla-rs/test_cases/should_pass/specification_directive_multi_var.tla']
    site_sets = [[('IF cat = "bugfix"', '='), ('ELSE IF cat = "integration"', '=')],
                 [("number' = number + 1", '+'), ("number' = number - 1", '-'),
                  ("number' = number + 1", '1'), ("number' = number - 1", '1')]]
    manifest = [json.loads(l) for l in (REPO / 'data/chattla-corpora-v3-wide/manifest_tier3_tlc.jsonl').read_text().splitlines()]
    held_path = REPO / 'corpus/holdout_30.json'
    held = [(n, (a.holdout_corpus / f'{n}.tla').read_text()) for n in json.loads(held_path.read_text())['holdout_specs']]
    tasks, audits = [], []
    for rel, sites in zip(sources, site_sets):
        path = REPO / 'data/chattla-corpora-v3-wide/tier3_tlc' / rel
        text, cfg = path.read_text(), path.with_suffix('.cfg').read_text()
        mod = module_name(text)
        rows = [r for r in manifest if r['content_sha256'] == sha(text) and r['decontam_verdict'] == 'clean']
        assert rows, f'No clean content-hashed manifest entry: {path}'
        shingles = shingle_set(normalize_tla(text))
        overlaps = {str(n): jaccard(shingles, shingle_set(normalize_tla(t))) for n, t in held}
        assert max(overlaps.values()) < .65 and all(sha(text) != sha(t) for _, t in held)
        audits.append(dict(source=str(path), source_sha256=sha(text), cfg_sha256=sha(cfg), holdout_jaccard=overlaps))
        for site, target in sites:
            assert text.count(site) == 1
            offset = text.index(site) + site.rindex(target)
            tasks.append(dict(id=f'{mod}-{len(tasks)}', mod=mod, reference=text, cfg=cfg,
                              prefix=text[:offset], suffix=text[offset + len(target):], target=target))
    # Frozen previous SANY task: evaluated but never selected by training schedule.
    retained = tasks[0]
    reference = retained['reference']
    offset = reference.index('THEN')
    tasks.append(dict(id='AdaptiveK-THEN-retention', mod=retained['mod'],
                      reference=reference, cfg=retained['cfg'], prefix=reference[:offset],
                      suffix=reference[offset+4:], target='THEN', evaluation_only=True))
    cache = Path.home() / '.cache/huggingface/hub/models--Qwen--Qwen2.5-0.5B-Instruct/snapshots'
    model = a.model_path or sorted(x for x in cache.glob('*') if (x / 'model.safetensors').exists())[-1]
    torch.set_num_threads(4)
    torch.manual_seed(a.seed)
    if a.device == 'cuda': torch.cuda.reset_peak_memory_stats()
    tok = AutoTokenizer.from_pretrained(model, local_files_only=True)
    net = AutoModelForCausalLM.from_pretrained(model, local_files_only=True, torch_dtype=torch.float32).to(a.device).eval()
    for v in net.parameters(): v.requires_grad_(False)
    for v in net.model.layers[-1].parameters(): v.requires_grad_(True)
    trainable = {n: v for n, v in net.named_parameters() if v.requires_grad}
    saved = torch.load(a.resume, map_location='cpu', weights_only=False)
    assert set(saved['trainable_state']) == set(trainable)
    with torch.no_grad():
        for n, v in trainable.items(): v.copy_(saved['trainable_state'][n].to(a.device))
    initial = {n: v.detach().cpu().clone() for n, v in trainable.items()}
    opt = torch.optim.AdamW(trainable.values(), lr=a.lr, weight_decay=0)
    config = dict(args={k: str(v) if isinstance(v, Path) else v for k, v in vars(a).items()},
                  scope='six one-token action/expression repair tasks from two frozen training modules plus one previous SANY retention evaluation; not heldout generalization',
                  audits=audits, holdout_sha256=sha(held_path.read_text()),
                  resume_sha256=hashlib.sha256(a.resume.read_bytes()).hexdigest(),
                  sampling='full vocabulary categorical; no candidate injection, retries, or filtering',
                  reward='parse failure=0; verified TLC rejection=.25; token-identical source restoration plus TLC/type mutation catches=.6 partial; additionally safety mutation catches=1; all other outcomes excluded',
                  semantic_audit='token identity to original source, not human semantic approval',
                  optimizer='fresh AdamW; resumed SANY policy parameters; group-normalized REINFORCE')
    config.update(torch_version=torch.__version__, transformers_version=transformers.__version__)
    dump(out / 'config.json', config)
    for task in tasks:
        # Qwen numbers start a separate token after whitespace; retain that
        # whitespace for numerical holes instead of sampling the space itself.
        rendered = task['prefix'] if task['target'].isdigit() else task['prefix'].rstrip()
        task['inputs'] = tok(rendered, return_tensors='pt').to(a.device)
        task['target_ids'] = [i for i in range(len(tok)) if tok.decode([i], skip_special_tokens=False).strip() == task['target']]

    def evaluate(label):
        reports = []
        for t in tasks:
            with torch.no_grad():
                logits = net(**t['inputs']).logits[0, -1].float()
                probs = logits.softmax(-1)
                token = int(logits.argmax())
            text = tok.decode([token], skip_special_tokens=False)
            row = reward_candidate(t['prefix'] + text + t['suffix'], t['reference'], t['cfg'], t['mod'], out / label / t['id'])
            row.update(task=t['id'], text=text, target_probability=float(probs[t['target_ids']].sum()))
            reports.append(row)
        dump(out / f'{label}.json', reports)
        return reports

    before = evaluate('before')
    metrics = []
    for step in range(a.steps):
        if time.monotonic() - start > a.seconds: break
        # Arithmetic tasks first: parseable numerical mistakes expose TLC reward.
        t = tasks[order[step % len(order)]]
        with torch.no_grad():
            logits = net(**t['inputs']).logits[0, -1].float() / a.temperature
            probs = logits.softmax(-1)
            sampled = torch.multinomial(probs, a.group_size, replacement=True)
        rewards, indices, rows = [], [], []
        for i, token in enumerate(sampled.tolist()):
            if time.monotonic() - start > a.seconds: break
            text = tok.decode([token], skip_special_tokens=False)
            row = reward_candidate(t['prefix'] + text + t['suffix'], t['reference'], t['cfg'], t['mod'], out / f'step-{step:03}' / f'sample-{i:02}')
            row.update(step=step, task=t['id'], token=token, text=text, behavior_logp=float(probs[token].log()))
            if row['reward'] is not None:
                rewards.append(row['reward']); indices.append(i)
            rows.append(row)
            with (out / 'rollouts.jsonl').open('a') as stream: stream.write(json.dumps(row) + '\n')
        r = torch.tensor(rewards, device=a.device)
        std = float(r.std(unbiased=False)) if len(rewards) else 0
        m = dict(step=step, task=t['id'], n=len(rows), sany_pass=sum(x['sany']=='pass' for x in rows),
                 tlc_reject=sum(x['tlc'] in ('fail_invariant','fail_deadlock','fail_liveness')
                                or x.get('model_type_error', False) for x in rows),
                 terminal_pass=sum(x['terminal_pass'] for x in rows), excluded=len(rows)-len(rewards),
                 reward_std=std, updated=False)
        m.update(entropy_nats=float(-(probs * probs.clamp_min(1e-30).log()).sum()),
                 unique_tokens=len(set(sampled.tolist())),
                 duplicate_fraction=1-len(set(sampled.tolist()))/len(sampled))
        if len(rewards) > 1 and std > 1e-7:
            opt.zero_grad(set_to_none=True)
            current = net(**t['inputs']).logits[0, -1].float() / a.temperature
            loss = -(((r-r.mean()) / r.std(unbiased=False)).detach() * current.log_softmax(-1)[sampled[indices]]).mean()
            loss.backward()
            norm = torch.nn.utils.clip_grad_norm_(trainable.values(), 1.)
            opt.step()
            m.update(updated=True, loss=float(loss.detach()), gradient_norm=float(norm))
        metrics.append(m)
        dump(out / 'metrics.json', metrics)
        print(json.dumps(m), flush=True)
    after = evaluate('after')
    state = {n: v.detach().cpu().clone() for n, v in trainable.items()}
    checkpoint = out / 'policy_optimizer.pt'
    torch.save(dict(trainable_state=state, optimizer=opt.state_dict(), config=config, metrics=metrics, torch_rng_state=torch.get_rng_state()), checkpoint)
    loaded = torch.load(checkpoint, map_location='cpu', weights_only=False)
    with torch.no_grad():
        first = net(**tasks[0]['inputs']).logits[0, -1].detach().cpu()
        for v in trainable.values(): v.zero_()
        for n,v in trainable.items(): v.copy_(loaded['trainable_state'][n].to(a.device))
        opt.load_state_dict(loaded['optimizer'])
        second = net(**tasks[0]['inputs']).logits[0, -1].detach().cpu()
    assert torch.equal(first, second)
    summary = dict(scope=config['scope'], optimizer_steps=sum(m['updated'] for m in metrics), metrics=metrics,
                   parameter_delta_norm=sum(float(((state[n]-initial[n])**2).sum()) for n in state)**.5,
                   checkpoint=str(checkpoint), reload_logits_exact=True, elapsed_s=time.monotonic()-start,
                   before=before, after=after, generalization_measured=False, full_spec_generation_measured=False)
    if a.device == 'cuda':
        summary['cuda_peak_allocated_bytes'] = torch.cuda.max_memory_allocated()
        summary['cuda_peak_reserved_bytes'] = torch.cuda.max_memory_reserved()
    dump(out / 'summary.json', summary)
    print(json.dumps({k:v for k,v in summary.items() if k not in ('before','after','metrics')}), flush=True)


if __name__ == '__main__': main()
