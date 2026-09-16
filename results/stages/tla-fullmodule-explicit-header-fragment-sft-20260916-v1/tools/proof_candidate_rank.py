#!/usr/bin/env python3
"""Bounded neural-guided symbolic proof search, not free proof generation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def freeze_tasks(manifest_bytes, contexts, metadata, candidate_limit):
    from tools.proof_context_eval import validate_contexts
    from tools.proof_repair_pilot import selected_tasks, with_dependency_context, prompt_for
    from tools.proof_retrieved_context import render
    from tools.proof_fact_search import proposals
    tasks = selected_tasks(json.loads(manifest_bytes), 'development')
    if len(tasks) != 4:
        raise ValueError('This experiment requires the full four-task development population')
    validate_contexts(manifest_bytes, metadata, contexts, tasks)
    frozen = []
    for source in tasks:
        # Explicit allowlist: reference answers never reach prompts or proposals.
        task = {k: source[k] for k in ('id', 'prefix', 'suffix', 'theorem_name', 'target_goal')}
        task['dependencies'] = source.get('dependencies', [])
        task['dependency_sha256'] = source.get('dependency_sha256', {})
        if any(path not in task['dependency_sha256'] for path in task['dependencies']):
            raise ValueError('Every dependency requires a frozen hash')
        enriched = with_dependency_context(task)
        context = contexts[task['id']]
        paths = list(context['library_sha256'])
        texts = [Path(p).read_text() for p in task['dependencies']]
        candidates, _ = proposals(task['prefix'], task['theorem_name'], task['target_goal'],
                                  texts, [Path(p).read_text() for p in paths])
        task['candidates'] = candidates[:candidate_limit]
        if len(task['candidates']) < 4:
            raise ValueError('At least four candidates required per task')
        task['prompt'] = prompt_for(enriched) + render(context)
        task['prompt_sha256'] = sha(task['prompt'].encode())
        task['context'] = context
        frozen.append(task)
    return frozen


def encode_candidate(tokenizer, prompt_text, candidate, max_tokens):
    messages = [dict(role='user', content=prompt_text)]
    prompt = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
    full = tokenizer.apply_chat_template(messages+[dict(role='assistant', content=candidate)],
                                         tokenize=False, add_generation_prompt=False)
    # Chat rendering already supplies BOS/EOT. Adding tokenizer defaults here
    # duplicated Llama's BOS during training but not free-generation inference.
    prefix = tokenizer(prompt, add_special_tokens=False, truncation=False)['input_ids']
    ids = tokenizer(full, add_special_tokens=False, truncation=False)['input_ids']
    if not prefix or not full.startswith(prompt) or ids[:len(prefix)] != prefix:
        raise ValueError('Chat template changed inference prompt boundary')
    response = ids[len(prefix):]
    if tokenizer.eos_token_id not in response or response.index(tokenizer.eos_token_id) < 1:
        raise ValueError('Candidate must include content and terminal EOS')
    ids = ids[:len(prefix)+response.index(tokenizer.eos_token_id)+1]
    if len(ids) > max_tokens:
        raise ValueError('Sequence exceeds budget; no truncation permitted')
    return dict(input_ids=ids, labels=[-100]*len(prefix)+ids[len(prefix):],
                prompt_tokens=len(prefix), response_tokens=len(ids)-len(prefix), rendered_prompt=prompt)


def response_logps(logits, labels):
    """Causal alignment: logit i predicts label i+1; only response/EOS count."""
    import torch
    labels = torch.as_tensor(labels, device=logits.device)
    if logits.ndim != 2 or labels.ndim != 1 or logits.shape[0] != len(labels):
        raise ValueError('Expected sequence-by-vocabulary logits and matching labels')
    mask = labels[1:] != -100
    if not mask.any():
        raise ValueError('No scored response tokens')
    selected = logits[:-1][mask].float().log_softmax(-1)
    values = selected.gather(1, labels[1:][mask, None]).squeeze(1)
    if not torch.isfinite(values).all():
        raise ValueError('Nonfinite candidate score')
    return dict(sum_logp=float(values.sum()), mean_logp=float(values.mean()),
                response_tokens=int(mask.sum()), token_logps=values.tolist())


def rank_scores(rows):
    return sorted(rows, key=lambda row: (-row['mean_logp'], row['candidate_index']))


def worker(a):
    from harness.proof_fragment_check import certify_fragment
    from tools.proof_sequence_train import restore_trainable
    config = json.loads((a.output/'config.json').read_text())
    frozen_bytes = (a.output/'frozen.json').read_bytes()
    if sha(frozen_bytes) != config['frozen_sha256']:
        raise ValueError('Frozen inputs changed')
    tasks = json.loads(frozen_bytes)
    for task in tasks:
        for path, expected in {**task['dependency_sha256'], **task['context']['library_sha256']}.items():
            if sha(Path(path).read_bytes()) != expected:
                raise ValueError('Dependency/library changed')
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    import torch
    import transformers
    torch.set_num_threads(4)
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    encodings = [[encode_candidate(tokenizer, t['prompt'], c, a.max_tokens) for c in t['candidates']] for t in tasks]
    dump(a.output/'encodings.json', encodings)
    net = transformers.AutoModelForCausalLM.from_pretrained(a.model_path, local_files_only=True,
             torch_dtype=torch.float32).to(a.device).eval()
    net.requires_grad_(False)
    model_files = {p.name:sha(p.read_bytes()) for p in a.model_path.iterdir()
                   if p.is_file() and p.suffix in {'.json', '.safetensors'}}
    if a.resume:
        checkpoint_bytes = a.resume.read_bytes()
        if sha(checkpoint_bytes) != config['checkpoint_sha256']:
            raise ValueError('Checkpoint changed after freeze')
        saved = torch.load(a.resume, map_location='cpu', weights_only=False)
        if saved['config']['model_files'] != model_files:
            raise ValueError('Checkpoint base model identity mismatch')
        names = {id(p) for p in net.model.layers[-1].parameters()}
        restore_trainable({n:p for n,p in net.named_parameters() if id(p) in names}, saved)
    dump(a.output/'runtime.json', dict(model_files=model_files, torch=torch.__version__,
         transformers=transformers.__version__, device=a.device, dtype='float32', parameter_updates=0))
    scoring_started = time.monotonic()
    scored = {}
    with (a.output/'scores.jsonl').open('x') as stream:
        for task, encoded in zip(tasks, encodings):
            rows = []
            for index, encoding in enumerate(encoded):
                if time.monotonic()-scoring_started >= a.score_seconds:
                    break
                with torch.inference_mode():
                    ids = torch.tensor([encoding['input_ids']], device=a.device)
                    logits = net(input_ids=ids, use_cache=False).logits[0]
                    score = response_logps(logits, encoding['labels'])
                row = dict(task=task['id'], candidate_index=index, fragment=task['candidates'][index], **score)
                rows.append(row)
                stream.write(json.dumps(row)+'\n'); stream.flush()
            # Do not rank a budget-selected subset as though all candidates competed.
            if len(rows) == len(encoded):
                scored[task['id']] = rank_scores(rows)
    scoring_elapsed = time.monotonic()-scoring_started
    del net
    if a.device == 'mps':
        torch.mps.empty_cache()
    dump(a.output/'rankings.json', scored)
    check_started = time.monotonic()
    checked = []
    with (a.output/'checks.jsonl').open('x') as stream:
        for task in tasks:
            for rank, row in enumerate(scored.get(task['id'], [])[:4], 1):
                if time.monotonic()-check_started > a.check_seconds-a.timeout:
                    break
                result = certify_fragment(task['prefix'], row['fragment'], task['suffix'],
                    theorem_name=task['theorem_name'], dependencies=tuple(map(Path, task['dependencies'])),
                    work_root=a.output/'checks'/task['id']/str(rank), timeout=a.timeout)
                result.update(task=task['id'], rank=rank, fragment=row['fragment'])
                checked.append(result)
                stream.write(json.dumps(result)+'\n'); stream.flush()
                if result['certified']:
                    break
    dump(a.output/'summary.json', dict(requested_tasks=4, fully_scored_tasks=len(scored),
         top1_verified=len({r['task'] for r in checked if r['certified'] and r['rank']==1}),
         top4_verified=len({r['task'] for r in checked if r['certified']}), checker_attempts=len(checked),
         scoring_seconds=scoring_elapsed, verification_seconds=time.monotonic()-check_started,
         method='neural-guided symbolic search; mean response logp including EOS; not free proof generation',
         parameter_updates=0, reference_fragment_used=False))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('manifest', 'contexts', 'model-path', 'output'):
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--resume', type=Path)
    p.add_argument('--device', choices=['cpu', 'mps'], default='mps')
    p.add_argument('--candidates', type=int, default=32)
    p.add_argument('--max-tokens', type=int, default=8192)
    p.add_argument('--score-seconds', type=int, default=900)
    p.add_argument('--check-seconds', type=int, default=180)
    p.add_argument('--timeout', type=int, default=10)
    p.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    a = p.parse_args()
    if not (4 <= a.candidates <= 32 and 30 <= a.score_seconds <= 1800 and
            10 <= a.check_seconds <= 300 and 1 <= a.timeout <= 10 and 128 <= a.max_tokens <= 8192):
        p.error('Invalid bounded candidate/time/token budget')
    a.output = a.output.resolve()
    if a.worker:
        worker(a)
        return
    contexts = json.loads(a.contexts.read_text())
    frozen = freeze_tasks(a.manifest.read_bytes(), contexts,
              json.loads(a.contexts.with_name('config.json').read_text()), a.candidates)
    a.output.mkdir(parents=True, exist_ok=False)
    dump(a.output/'frozen.json', frozen)
    dump(a.output/'config.json', dict(args={k:str(v) if isinstance(v, Path) else v for k,v in vars(a).items()},
         manifest_sha256=sha(a.manifest.read_bytes()), frozen_sha256=sha((a.output/'frozen.json').read_bytes()),
         checkpoint_sha256=sha(a.resume.read_bytes()) if a.resume else None,
         ranking='descending mean conditional response token logp including EOS; stable candidate-index ties',
         measurement='top1/top4 strict certified repairs over all four development tasks',
         hypothesis='Frozen learned weights rank symbolic premises better than lexical proposal order',
         stop='separate scoring/check budgets; incomplete candidate populations remain unranked',
         implementation_sha256={str(path.relative_to(ROOT)):sha(path.read_bytes()) for path in
             [Path(__file__).resolve(), ROOT/'harness/proof_fragment_check.py',
              ROOT/'harness/runner.py', ROOT/'tools/proof_sequence_train.py',
              ROOT/'tools/proof_repair_pilot.py', ROOT/'tools/proof_fact_search.py', ROOT/'tools/proof_source_scope.py',
              ROOT/'tools/proof_retrieved_context.py', ROOT/'tools/proof_premise_search.py']},
         reference_fragment_used=False, parameter_updates=0))
    (a.output/'tool.py').write_bytes(Path(__file__).read_bytes())
    from harness.runner import run_cmd
    command = [sys.executable, '-u', str(Path(__file__).resolve()), *sys.argv[1:], '--worker']
    code, output, elapsed, timed_out = run_cmd(command, ROOT, a.score_seconds+a.check_seconds+180)
    (a.output/'console.log').write_text(output)
    dump(a.output/'execution.json', dict(exit_code=code, elapsed_seconds=elapsed, timed_out=timed_out))
    print(output[-5000:])
    raise SystemExit(0 if code == 0 and not timed_out else 1)


if __name__ == '__main__':
    main()
