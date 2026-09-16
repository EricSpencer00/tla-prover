#!/usr/bin/env python3
"""Separate bounded GPU proof generation from local strict TLAPS verification."""
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


def validate_prompts(data):
    if data.get('split') != 'development' or data.get('reference_fragments_exported') is not False:
        raise ValueError('invalid prompt export contract')
    rows = data.get('tasks')
    if not isinstance(rows, list) or not rows:
        raise ValueError('empty or invalid prompt population')
    expected = {}
    for row in rows:
        key, prompt = row.get('id'), row.get('prompt')
        if not isinstance(key, str) or not key or key in expected:
            raise ValueError('invalid or duplicate prompt task')
        if not isinstance(prompt, str) or row.get('prompt_sha256') != sha(prompt.encode()):
            raise ValueError('prompt text hash mismatch')
        if set(row) != {'id', 'prompt', 'prompt_sha256'}:
            raise ValueError('unexpected fields in prompt export')
        expected[key] = row
    return expected


def validate_generations(prompt_bytes, data, config, generations):
    expected = validate_prompts(data)
    if config.get('prompts_sha256') != sha(prompt_bytes):
        raise ValueError('generation config prompt file hash mismatch')
    if config.get('requested_task_ids') != list(expected):
        raise ValueError('generation config task population mismatch')
    if config.get('max_new_tokens') != 512:
        raise ValueError('generation budget mismatch')
    seen = set()
    for row in generations:
        key = row.get('id')
        if key not in expected or key in seen:
            raise ValueError('unknown or duplicate generated task')
        seen.add(key)
        prompt = expected[key]
        if row.get('prompt_sha256') != prompt['prompt_sha256'] or row.get('prompt') != prompt['prompt']:
            raise ValueError('prompt provenance mismatch')
        for field in ('raw_reply', 'rendered_prompt'):
            value = row.get(field)
            if not isinstance(value, str) or row.get(field+'_sha256') != sha(value.encode()):
                raise ValueError(field+' hash mismatch')
        if prompt['prompt'] not in row['rendered_prompt']:
            raise ValueError('rendered prompt lacks original user content')
        for field, count in [('token_ids', 'output_tokens'), ('input_token_ids', 'input_tokens')]:
            ids = row.get(field)
            if (not isinstance(ids, list) or not ids
                    or any(type(token) is not int or token < 0 for token in ids)
                    or type(row.get(count)) is not int or row[count] != len(ids)):
                raise ValueError('inconsistent '+count)
        if row['output_tokens'] > 512 or row.get('hit_token_limit') is not (row['output_tokens'] == 512):
            raise ValueError('output budget accounting mismatch')
    # A deadline may legitimately leave a suffix unattempted, but not skip/reorder tasks.
    if [r['id'] for r in generations] != list(expected)[:len(generations)]:
        raise ValueError('generation order or missing interior task mismatch')


def prepare(a):
    from tools.proof_repair_pilot import selected_tasks, with_dependency_context, prompt_for
    from tools.proof_retrieved_context import render
    from tools.proof_context_eval import validate_contexts
    manifest_bytes = a.manifest.read_bytes()
    tasks = selected_tasks(json.loads(manifest_bytes), 'development')
    contexts = json.loads(a.contexts.read_text())
    metadata = json.loads(a.contexts.with_name('config.json').read_text())
    validate_contexts(manifest_bytes, metadata, contexts, tasks)
    rows = []
    for task in tasks:
        prompt = prompt_for(with_dependency_context(task)) + render(contexts[task['id']])
        rows.append(dict(id=task['id'], prompt=prompt, prompt_sha256=sha(prompt.encode())))
    dump(a.output/'prompts.json', dict(manifest_sha256=sha(manifest_bytes),
         context_sha256=sha(a.contexts.read_bytes()), split='development', tasks=rows,
         reference_fragments_exported=False))


def generate(a):
    prompt_bytes = a.prompts.read_bytes()
    data = json.loads(prompt_bytes)
    expected = validate_prompts(data)
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    import torch
    import transformers
    started = time.monotonic()
    torch.set_num_threads(4)
    torch.manual_seed(20260912)
    torch.cuda.reset_peak_memory_stats()
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    net = transformers.AutoModelForCausalLM.from_pretrained(a.model_path, local_files_only=True,
             torch_dtype=torch.bfloat16).to('cuda').eval()
    net.requires_grad_(False)
    dump(a.output/'config.json', dict(prompts_sha256=sha(prompt_bytes), requested_task_ids=list(expected),
         model_path=str(a.model_path), dtype='bfloat16', seed=20260912, max_new_tokens=512,
         decoding='greedy; one generation per task; no training/retries/filtering',
         model_config_sha256=sha((a.model_path/'config.json').read_bytes()),
         torch_version=torch.__version__, transformers_version=transformers.__version__,
         gpu=torch.cuda.get_device_name(), seconds=a.seconds))
    rows = []
    with (a.output/'generations.jsonl').open('x') as stream:
        for task in data['tasks']:
            if time.monotonic()-started > a.seconds-120:
                break
            rendered = tokenizer.apply_chat_template([dict(role='user', content=task['prompt'])],
                        tokenize=False, add_generation_prompt=True)
            inputs = tokenizer(rendered, return_tensors='pt').to('cuda')
            with torch.inference_mode():
                generated = net.generate(**inputs, do_sample=False, max_new_tokens=512,
                         max_time=100, pad_token_id=tokenizer.eos_token_id)
            ids = generated[0, inputs.input_ids.shape[1]:].tolist()
            reply = tokenizer.decode(ids, skip_special_tokens=True)
            row = dict(id=task['id'], prompt=task['prompt'], prompt_sha256=task['prompt_sha256'],
                       rendered_prompt=rendered, rendered_prompt_sha256=sha(rendered.encode()),
                       raw_reply=reply, raw_reply_sha256=sha(reply.encode()),
                       input_token_ids=inputs.input_ids[0].tolist(),
                       token_ids=ids, input_tokens=inputs.input_ids.shape[1], output_tokens=len(ids),
                       hit_token_limit=len(ids)==512)
            rows.append(row)
            stream.write(json.dumps(row)+'\n'); stream.flush()
            print(json.dumps(dict(id=task['id'], output_tokens=len(ids))), flush=True)
    dump(a.output/'summary.json', dict(requested=len(data['tasks']), generated=len(rows),
         elapsed_seconds=time.monotonic()-started, complete=len(rows)==len(data['tasks']),
         cuda_peak_allocated_bytes=torch.cuda.max_memory_allocated(), parameter_updates=0))


def verify(a):
    from harness.proof_gen import extract_proof_block
    from harness.proof_fragment_check import certify_fragment
    from tools.proof_repair_pilot import selected_tasks
    prompt_bytes = a.prompts.read_bytes()
    data = json.loads(prompt_bytes)
    if data['manifest_sha256'] != sha(a.manifest.read_bytes()):
        raise ValueError('manifest hash mismatch')
    tasks = {t['id']:t for t in selected_tasks(json.loads(a.manifest.read_text()), 'development')}
    expected = validate_prompts(data)
    if set(tasks) != set(expected):
        raise ValueError('task population mismatch')
    generations = [json.loads(x) for x in a.generations.read_text().splitlines()]
    config_bytes = a.generations.with_name('config.json').read_bytes()
    validate_generations(prompt_bytes, data, json.loads(config_bytes), generations)
    results = []
    with (a.output/'rows.jsonl').open('x') as stream:
        for row in generations:
            task = tasks[row['id']]
            if row['prompt_sha256'] != expected[row['id']]['prompt_sha256']:
                raise ValueError('prompt provenance mismatch')
            fragment = extract_proof_block(row['raw_reply'])
            result = dict(id=row['id'], certified=False, status='no_proof_fragment', fragment=fragment)
            if fragment is not None:
                result.update(certify_fragment(task['prefix'], fragment, task['suffix'],
                    theorem_name=task['theorem_name'], dependencies=tuple(map(Path,task.get('dependencies',[]))),
                    work_root=a.output/'checks'/task['id'], timeout=30))
            results.append(result)
            stream.write(json.dumps(result)+'\n'); stream.flush()
            print(json.dumps({k:result[k] for k in ['id','certified','status']}), flush=True)
    dump(a.output/'summary.json', dict(requested_tasks=len(tasks), generated_tasks=len(generations),
         verified_repairs=sum(r['certified'] for r in results),
         missing_tasks=sorted(set(tasks)-{r['id'] for r in generations}),
         manifest_sha256=data['manifest_sha256'], generation_sha256=sha(a.generations.read_bytes()),
         prompts_sha256=sha(prompt_bytes), generation_config_sha256=sha(config_bytes),
         scope='known source-separated development proof repair with given skeleton and statement retrieval; no training'))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=['prepare','generate','verify'])
    p.add_argument('--manifest', type=Path)
    p.add_argument('--contexts', type=Path)
    p.add_argument('--prompts', type=Path)
    p.add_argument('--model-path', type=Path)
    p.add_argument('--generations', type=Path)
    p.add_argument('--seconds', type=int, default=600)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    required = dict(prepare=['manifest','contexts'], generate=['prompts','model_path'], verify=['manifest','prompts','generations'])
    if any(getattr(a,k) is None for k in required[a.mode]) or not 150 <= a.seconds <= 3300:
        p.error('missing mode arguments or invalid time budget')
    a.output = a.output.resolve()
    a.output.mkdir(parents=True, exist_ok=False)
    (a.output/'tool.py').write_bytes(Path(__file__).read_bytes())
    globals()[a.mode](a)


if __name__ == '__main__':
    main()
