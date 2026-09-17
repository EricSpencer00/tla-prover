#!/usr/bin/env python3
"""Bounded real-model multi-token proof-fragment repair, certified by TLAPS.

Development skeleton repair only; no claim of training or unseen proving.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))


def digest(data):
    return hashlib.sha256(data).hexdigest()


def prompt_for(task, feedback=None):
    dependency_context = ''.join(
        '\n===BEGIN DEPENDENCY ' + dep['module'] + '===\n' + dep['text'] +
        '\n===END DEPENDENCY ' + dep['module'] + '===\n'
        for dep in task.get('dependency_context', []))
    prompt = ('Complete the missing TLA+ proof fragment marked <PROOF_HOLE>. '
              'The theorem statement and all other proof steps are fixed. '
              'Return only the missing proof fragment, preferably in a tla code fence. '
              'Use valid TLAPS syntax. Do not introduce axioms, omit proofs, change '
              'definitions, or repeat the module.\n\n'
              + (dependency_context + '\n' if dependency_context else '')
              + task['prefix'] + '<PROOF_HOLE>' + task['suffix'])
    if feedback:
        prompt += '\n\nThe previous fragment was rejected. TLAPS/checker feedback:\n' + feedback[-3000:]
    return prompt


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def selected_tasks(manifest, split):
    tasks = manifest['tasks']
    if split != 'all':
        tasks = [task for task in tasks if task.get('split') == split]
    if not tasks or len({task['id'] for task in tasks}) != len(tasks):
        raise ValueError('empty task selection or duplicate task IDs')
    return tasks


def with_dependency_context(task):
    task = dict(task)
    task['dependency_context'] = []
    for name in task.get('dependencies', []):
        path = Path(name)
        data = path.read_bytes()
        expected = task.get('dependency_sha256', {}).get(name)
        if expected is not None and digest(data) != expected:
            raise ValueError('dependency hash changed since manifest freeze')
        task['dependency_context'].append(dict(module=path.stem, text=data.decode(), sha256=digest(data)))
    return task


def worker(a):
    from harness.proof_fragment_check import certify_fragment
    from harness.proof_gen import extract_proof_block
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    tasks = selected_tasks(json.loads(a.manifest.read_text()), a.split)
    if a.include_dependencies:
        tasks = [with_dependency_context(task) for task in tasks]
    config = dict(args={k:str(v) if isinstance(v, Path) else v for k,v in vars(a).items()},
                  manifest_sha256=digest(a.manifest.read_bytes()),
                  scope='development human-skeleton multi-token proof repair; no training, no official benchmark claim',
                  attempts_per_task=a.rounds, generation_max_tokens=a.max_tokens,
                  checkpoint='cached Qwen2.5-0.5B-Instruct base' if a.resume is None else str(a.resume),
                  checkpoint_sha256=digest(a.resume.read_bytes()) if a.resume else None,
                  selection='fixed manifest before model load; no correctness filtering of model outputs')
    dump(a.output/'config.json', config)
    # Oracle restoration and rejection controls establish the task/checker before
    # measuring the model. An invalid fixture stops the run, never drops a task.
    for task in tasks:
        deps = tuple(Path(p) for p in task.get('dependencies', []))
        for label, fragment, expected in [('reference', task['reference_fragment'], True),
                                           ('omitted', 'OMITTED', False)]:
            row = certify_fragment(task['prefix'], fragment, task['suffix'],
                                   theorem_name=task['theorem_name'],
                                   work_root=a.output/'controls'/task['id']/label,
                                   dependencies=deps, timeout=a.verifier_timeout)
            dump(a.output/f"control-{task['id']}-{label}.json", row)
            if row['certified'] != expected:
                raise RuntimeError(f"control mismatch: {task['id']} {label}: {row['status']}")
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(a.seed)
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    net = transformers.AutoModelForCausalLM.from_pretrained(a.model_path, local_files_only=True,
                        torch_dtype=torch.float32).to(a.device).eval()
    net.requires_grad_(False)
    if a.resume:
        saved = torch.load(a.resume, map_location='cpu', weights_only=False)
        parameters = dict(net.named_parameters())
        expected = {name for name in parameters if name.startswith(f'model.layers.{len(net.model.layers)-1}.')}
        if set(saved['trainable_state']) != expected:
            raise ValueError('checkpoint must contain exactly the final transformer layer')
        with torch.no_grad():
            for name, value in saved['trainable_state'].items():
                parameters[name].copy_(value.to(a.device))
    config.update(torch_version=torch.__version__, transformers_version=transformers.__version__)
    dump(a.output/'config.json', config)
    rows = []
    with (a.output/'rows.jsonl').open('x') as ledger:
        for task_index, task in enumerate(tasks):
            feedback = None
            for attempt in range(a.rounds):
                seed = a.seed + 100*task_index + attempt
                torch.manual_seed(seed)
                prompt = prompt_for(task, feedback)
                rendered = tokenizer.apply_chat_template([dict(role='user', content=prompt)],
                             tokenize=False, add_generation_prompt=True)
                inputs = tokenizer(rendered, return_tensors='pt').to(a.device)
                started = time.monotonic()
                with torch.inference_mode():
                    output = net.generate(**inputs, max_new_tokens=a.max_tokens,
                              do_sample=attempt > 0, **({'temperature': .8, 'top_k': 0} if attempt > 0 else {}),
                              pad_token_id=tokenizer.eos_token_id, max_time=60)
                ids = output[0, inputs.input_ids.shape[1]:].tolist()
                reply = tokenizer.decode(ids, skip_special_tokens=True)
                fragment = extract_proof_block(reply)
                row = dict(task=task['id'], attempt=attempt, seed=seed, prompt=prompt,
                           rendered_prompt=rendered, raw_reply=reply, token_ids=ids,
                           input_tokens=inputs.input_ids.shape[1], output_tokens=len(ids),
                           hit_token_limit=len(ids)==a.max_tokens,
                           generation_seconds=time.monotonic()-started, fragment=fragment,
                           certified=False, status='no_proof_fragment', proved=0, total=0)
                if fragment is not None:
                    result = certify_fragment(task['prefix'], fragment, task['suffix'],
                               theorem_name=task['theorem_name'],
                               work_root=a.output/'attempts'/task['id']/str(attempt),
                               dependencies=tuple(Path(p) for p in task.get('dependencies', [])),
                               timeout=a.verifier_timeout)
                    row.update(result)
                feedback = row.get('output') or row.get('reason') or row['status']
                rows.append(row)
                ledger.write(json.dumps(row)+'\n')
                ledger.flush()
                print(json.dumps({k:row[k] for k in ['task','attempt','certified','status','proved','total']}), flush=True)
                if row['certified']:
                    break
    summary = dict(tasks=len(tasks), attempted_tasks=len({r['task'] for r in rows}),
                   certified_tasks=len({r['task'] for r in rows if r['certified']}),
                   first_attempt_certified=sum(r['certified'] and r['attempt']==0 for r in rows),
                   model_attempts=len(rows), parameter_updates=0, scope=config['scope'], split=a.split,
                   per_split={split: dict(tasks=sum(t.get('split', 'unspecified') == split for t in tasks),
                       certified_tasks=len({r['task'] for r in rows if r['certified'] and
                         next(t for t in tasks if t['id'] == r['task']).get('split', 'unspecified') == split}))
                       for split in {t.get('split', 'unspecified') for t in tasks}})
    dump(a.output/'summary.json', summary)
    print(json.dumps(summary), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--model-path', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--device', default='mps')
    p.add_argument('--resume', type=Path)
    p.add_argument('--split', choices=['all', 'train', 'development'], default='all')
    p.add_argument('--include-dependencies', action='store_true',
                   help='Provide frozen imported source definitions as explicit model context')
    p.add_argument('--rounds', type=int, default=2)
    p.add_argument('--max-tokens', type=int, default=128)
    p.add_argument('--verifier-timeout', type=int, default=30)
    p.add_argument('--seconds', type=int, default=900)
    p.add_argument('--seed', type=int, default=20260911)
    p.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    a = p.parse_args()
    if not 1 <= a.rounds <= 8 or not 1 <= a.max_tokens <= 1024 or a.seconds < 1:
        p.error('invalid bounded experiment budget')
    a.output = a.output.resolve()
    a.manifest = a.manifest.resolve()
    if a.worker:
        worker(a)
        return
    from harness.runner import run_cmd
    a.output.mkdir(parents=True, exist_ok=False)
    (a.output/'evaluator.py').write_text(Path(__file__).read_text())
    (a.output/'manifest.json').write_bytes(a.manifest.read_bytes())
    command = [sys.executable, '-u', str(Path(__file__).resolve()), *sys.argv[1:], '--worker']
    code, output, seconds, timed_out = run_cmd(command, REPO, a.seconds)
    (a.output/'console.log').write_text(output)
    dump(a.output/'execution.json', dict(exit_code=code, elapsed_seconds=seconds, timed_out=timed_out))
    print(output[-5000:])
    raise SystemExit(0 if code == 0 and not timed_out else 1)


if __name__ == '__main__':
    main()
