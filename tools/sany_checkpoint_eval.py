#!/usr/bin/env python3
"""Frozen-policy stochastic SANY evaluation; known one-token curriculum only."""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import sys
import time

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))
from harness.runner import check_sany, module_name


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tasks_from_parent(config):
    sites = [[('IF cat = "bugfix"', '='), ('ELSE IF cat = "integration"', '=')],
             [("number' = number + 1", '+'), ("number' = number - 1", '-'),
              ("number' = number + 1", '1'), ("number' = number - 1", '1')]]
    tasks = []
    for audit, holes in zip(config['audits'], sites):
        rel = audit['source'].split('/data/', 1)[1]
        path = REPO / 'data' / rel
        assert sha(path) == audit['source_sha256']
        reference = path.read_text()
        for site, target in holes:
            assert reference.count(site) == 1
            offset = reference.index(site) + site.rindex(target)
            tasks.append(dict(id=f'{module_name(reference)}-{len(tasks)}',
                              mod=module_name(reference), reference=reference,
                              prefix=reference[:offset], suffix=reference[offset+len(target):], target=target))
    reference = tasks[0]['reference']
    offset = reference.index('THEN')
    tasks.append(dict(id='AdaptiveK-THEN-retention', mod=tasks[0]['mod'], reference=reference,
                      prefix=reference[:offset], suffix=reference[offset+4:], target='THEN'))
    assert len(tasks) == 7
    return tasks


def summarize(rows, target, elapsed, finished=False):
    counts = Counter(r['sany'] for r in rows)
    per_task = {}
    for row in rows:
        counts_task = per_task.setdefault(row['task'], Counter())
        counts_task[row['sany']] += 1
    return dict(requested_attempts=target, attempts=len(rows), sany_counts=dict(counts),
                pass_fraction_all_attempts=counts['pass']/len(rows) if rows else None,
                unique_candidates=len({r['candidate_sha256'] for r in rows}),
                per_task=per_task, elapsed_seconds=elapsed, finished=finished,
                stop_reason=('target_reached' if len(rows) == target else 'time_budget') if finished else None,
                scope='known seven one-token repair prompts on two training modules; SANY only, not semantic/TLC/prover success or generalization')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--resume', type=Path, required=True)
    p.add_argument('--model-path', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--attempts', type=int, default=1000)
    p.add_argument('--seconds', type=int, default=3300)
    p.add_argument('--seed', type=int, default=20260907)
    p.add_argument('--temperature', type=float, default=1.0)
    p.add_argument('--device', default='cuda')
    a = p.parse_args()
    if a.attempts < 1 or a.seconds < 30 or a.temperature <= 0:
        p.error('positive attempts/temperature and at least 30 seconds required')
    started = time.monotonic()
    a.output.mkdir(parents=True, exist_ok=False)
    def dump(name, value):
        (a.output / name).write_text(json.dumps(value, indent=2) + '\n')
    (a.output / 'evaluator.py').write_text(Path(__file__).read_text())
    parent = json.loads(a.resume.with_name('config.json').read_text())
    tasks = tasks_from_parent(parent)
    checkpoint_sha = sha(a.resume)
    config = dict(args={k:str(v) if isinstance(v, Path) else v for k,v in vars(a).items()},
                  checkpoint_sha256=checkpoint_sha, parent_config=parent,
                  tasks=[{k:v for k,v in t.items()} for t in tasks],
                  sampling='frozen policy, full vocabulary, round-robin tasks, one sample per attempt, no retries/filtering',
                  updates=0, verification='SANY only; no TLC or semantic success claim')
    dump('config.json', config)
    # Real positive and negative controls before any model sampling.
    for label, source, expected in [('positive', tasks[0]['reference'], 'pass'),
                                    ('negative', tasks[0]['prefix']+' ) ) '+tasks[0]['suffix'], 'fail')]:
        work = a.output / ('control-'+label)
        work.mkdir()
        path = work / (tasks[0]['mod']+'.tla')
        path.write_text(source)
        status, log, _ = check_sany(path, work, 10)
        (work / 'sany.log').write_text(log)
        if status != expected:
            raise RuntimeError(f'SANY {label} control: expected {expected}, got {status}')
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(a.seed)
    tok = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    net = transformers.AutoModelForCausalLM.from_pretrained(a.model_path, local_files_only=True,
                                                           torch_dtype=torch.float32).to(a.device).eval()
    net.requires_grad_(False)
    saved = torch.load(a.resume, map_location='cpu', weights_only=False)
    parameters = dict(net.named_parameters())
    expected = {n for n in parameters if n.startswith(f'model.layers.{len(net.model.layers)-1}.')}
    assert set(saved['trainable_state']) == expected
    with torch.no_grad():
        for name, value in saved['trainable_state'].items():
            parameters[name].copy_(value.to(a.device))
    config.update(torch_version=torch.__version__, transformers_version=transformers.__version__)
    dump('config.json', config)
    distributions = []
    with torch.inference_mode():
        for task in tasks:
            prefix = task['prefix'] if task['target'].isdigit() else task['prefix'].rstrip()
            inputs = tok(prefix, return_tensors='pt').to(a.device)
            distributions.append((net(**inputs).logits[0,-1].float()/a.temperature).softmax(-1))
    rows = []
    with (a.output / 'rows.jsonl').open('x') as ledger:
        for i in range(a.attempts):
            if time.monotonic()-started >= a.seconds-15:
                break
            task = tasks[i % len(tasks)]
            token = int(torch.multinomial(distributions[i % len(tasks)], 1))
            decoded = tok.decode([token], skip_special_tokens=False)
            candidate = task['prefix']+decoded+task['suffix']
            work = a.output / f'sample-{i:04}'
            work.mkdir()
            path = work / (task['mod']+'.tla')
            path.write_text(candidate)
            status, log, duration = check_sany(path, work, 10)
            (work / 'sany.log').write_text(log)
            row = dict(attempt=i, task=task['id'], token=token, decoded=decoded, sany=status,
                       candidate_sha256=sha(path), verifier_seconds=duration, log_path=str(work))
            rows.append(row)
            ledger.write(json.dumps(row)+'\n')
            ledger.flush()
            if len(rows) % 50 == 0:
                summary = summarize(rows, a.attempts, time.monotonic()-started)
                dump('summary.json', summary)
                print(json.dumps(summary), flush=True)
    assert sha(a.resume) == checkpoint_sha
    summary = summarize(rows, a.attempts, time.monotonic()-started, finished=True)
    summary['checkpoint_unchanged'] = True
    dump('summary.json', summary)
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
