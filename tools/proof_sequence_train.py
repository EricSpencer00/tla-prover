#!/usr/bin/env python3
"""Bounded response-only SFT of verified, multi-token TLAPS proof fragments.

This is supervised learning, not RL or a certification claim. Development
responses never enter the model; the caller must first approve strict controls.
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
from tools.proof_repair_pilot import prompt_for, with_dependency_context


def digest(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def training_tasks(manifest):
    """Fail closed on absent/overlapping family splits; do not filter failures."""
    tasks = manifest['tasks']
    if not tasks or len({t['id'] for t in tasks}) != len(tasks):
        raise ValueError('Tasks must have unique IDs and be nonempty')
    for t in tasks:
        if t.get('split') not in {'train', 'development'}:
            raise ValueError('Every task needs explicit train/development split')
        if not t.get('source_family') or not t.get('source_sha256'):
            raise ValueError('Every task needs source family and hash')
    train = [t for t in tasks if t['split'] == 'train']
    dev = [t for t in tasks if t['split'] == 'development']
    if not train or not dev:
        raise ValueError('Both train and development are required')
    for key in ('source_family', 'source_sha256', 'assembled_sha256'):
        left = {t[key] for t in train if t.get(key)}
        right = {t[key] for t in dev if t.get(key)}
        if left & right:
            raise ValueError(f'Train/development overlap: {key}')
    # Exact scaffold duplication is forbidden independently of claimed hashes.
    if {(t['prefix'], t['suffix']) for t in train} & {(t['prefix'], t['suffix']) for t in dev}:
        raise ValueError('Train/development scaffold overlap')
    return train


def encode_response(tokenizer, task, max_tokens):
    """Use exactly inference's prompt tokens, supervising only assistant + EOT.

    Reject a tokenizer whose full conversation retokenizes the generation
    prefix, rather than silently moving a token boundary or masking a prompt.
    """
    messages = [dict(role='user', content=prompt_for(task))]
    prompt = tokenizer.apply_chat_template(messages, tokenize=False, add_generation_prompt=True)
    full = tokenizer.apply_chat_template(
        messages + [dict(role='assistant', content=task['reference_fragment'])],
        tokenize=False, add_generation_prompt=False)
    prefix_ids = tokenizer(prompt, add_special_tokens=False, truncation=False)['input_ids']
    ids = tokenizer(full, add_special_tokens=False, truncation=False)['input_ids']
    if not full.startswith(prompt) or ids[:len(prefix_ids)] != prefix_ids:
        raise ValueError('Chat template does not preserve inference prompt token boundary')
    response = ids[len(prefix_ids):]
    if tokenizer.eos_token_id not in response or response.index(tokenizer.eos_token_id) < 2:
        raise ValueError('Response must be multi-token and include end-of-turn EOS')
    # Do not teach template whitespace after end-of-turn; generation stops at EOS.
    ids = ids[:len(prefix_ids) + response.index(tokenizer.eos_token_id) + 1]
    if len(ids) > max_tokens:
        raise ValueError('Sequence exceeds budget; truncation is forbidden')
    labels = [-100] * len(prefix_ids) + ids[len(prefix_ids):]
    return dict(input_ids=ids, labels=labels, prompt_tokens=len(prefix_ids),
                response_tokens=len(ids)-len(prefix_ids), rendered_prompt=prompt)


def restore_trainable(trainable, saved):
    import torch
    state = saved['trainable_state']
    if set(state) != set(trainable):
        raise ValueError('Checkpoint trainable parameter coverage mismatch')
    for name, parameter in trainable.items():
        if state[name].shape != parameter.shape or state[name].dtype != parameter.dtype:
            raise ValueError(f'Checkpoint shape/dtype mismatch: {name}')
    with torch.no_grad():
        for name, parameter in trainable.items():
            parameter.copy_(state[name].to(parameter.device))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--model-path', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--device', choices=['cpu', 'mps', 'cuda'], default='mps')
    parser.add_argument('--steps', type=int, default=32)
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--max-tokens', type=int, default=4096)
    parser.add_argument('--seed', type=int, default=20260905)
    parser.add_argument('--lr', type=float, default=1e-5)
    parser.add_argument('--include-dependencies', action='store_true')
    args = parser.parse_args()
    if not 1 <= args.steps <= 1000 or not 1 <= args.seconds <= 3300 or args.lr <= 0:
        parser.error('Invalid bounded steps/seconds/lr')
    start = time.monotonic()
    manifest_bytes = args.manifest.read_bytes()
    tasks = training_tasks(json.loads(manifest_bytes))
    if args.include_dependencies:
        tasks = [with_dependency_context(task) for task in tasks]
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output/'manifest.json').write_bytes(manifest_bytes)
    (args.output/'trainer.py').write_bytes(Path(__file__).read_bytes())
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(args.seed)
    if args.device == 'cuda':
        torch.cuda.reset_peak_memory_stats()
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model_path, local_files_only=True)
    encoded = [encode_response(tokenizer, t, args.max_tokens) for t in tasks]
    net = transformers.AutoModelForCausalLM.from_pretrained(
        args.model_path, local_files_only=True, torch_dtype=torch.float32).to(args.device).eval()
    net.requires_grad_(False)
    net.model.layers[-1].requires_grad_(True)
    trainable = {n: p for n, p in net.named_parameters() if p.requires_grad}
    initial = {n: p.detach().cpu().clone() for n, p in trainable.items()}
    optimizer = torch.optim.AdamW(trainable.values(), lr=args.lr, weight_decay=0)
    config = dict(args={k:str(v) if isinstance(v, Path) else v for k,v in vars(args).items()},
                  manifest_sha256=digest(manifest_bytes), trainer_sha256=digest(Path(__file__).read_bytes()),
                  prompt_function_sha256=digest(Path(sys.modules[prompt_for.__module__].__file__).read_bytes()),
                  algorithm='response-only causal cross entropy SFT; fresh AdamW; base initialization',
                  scope='multi-token proof-fragment learning; strict external TLAPS evaluation required',
                  train_ids=[t['id'] for t in tasks], trainable_names=list(trainable),
                  trainable_parameters=sum(p.numel() for p in trainable.values()),
                  torch_version=torch.__version__, transformers_version=transformers.__version__,
                  hardware=torch.cuda.get_device_name() if args.device == 'cuda' else args.device,
                  model_files={p.name:digest(p.read_bytes()) for p in args.model_path.iterdir()
                               if p.is_file() and (p.suffix == '.json' or p.suffix == '.safetensors')})
    dump(args.output/'config.json', config)
    dump(args.output/'training_encodings.json', [dict(task=t['id'], **e) for t,e in zip(tasks, encoded)])
    metrics = []
    with (args.output/'steps.jsonl').open('x') as ledger:
        for step in range(args.steps):
            if time.monotonic()-start >= args.seconds:
                break
            index = step % len(encoded)
            e = encoded[index]
            ids = torch.tensor([e['input_ids']], device=args.device)
            labels = torch.tensor([e['labels']], device=args.device)
            optimizer.zero_grad(set_to_none=True)
            # Transformers shifts labels internally: logits[i-1] predicts labels[i].
            result = net(input_ids=ids, labels=labels, use_cache=False)
            loss = result.loss
            if not torch.isfinite(loss):
                raise RuntimeError('Nonfinite loss')
            loss.backward()
            norm = torch.nn.utils.clip_grad_norm_(trainable.values(), 1., error_if_nonfinite=True)
            optimizer.step()
            row = dict(step=step+1, task=tasks[index]['id'], loss=float(loss.detach()),
                       gradient_norm=float(norm), elapsed_s=time.monotonic()-start,
                       response_tokens=e['response_tokens'])
            metrics.append(row)
            ledger.write(json.dumps(row)+'\n')
            ledger.flush()
            print(json.dumps(row), flush=True)
    state = {n:p.detach().cpu().clone() for n,p in trainable.items()}
    checkpoint = args.output/'policy_optimizer.pt'
    torch.save(dict(trainable_state=state, optimizer=optimizer.state_dict(), config=config,
                    metrics=metrics, torch_rng_state=torch.get_rng_state(),
                    cuda_rng_state=torch.cuda.get_rng_state_all() if args.device == 'cuda' else None,
                    mps_rng_state=torch.mps.get_rng_state() if args.device == 'mps' else None), checkpoint)
    probe = torch.tensor([encoded[0]['input_ids']], device=args.device)
    with torch.no_grad():
        before = net(input_ids=probe, use_cache=False).logits[:, -1].cpu().clone()
        for p in trainable.values():
            p.zero_()
        restore_trainable(trainable, torch.load(checkpoint, map_location='cpu', weights_only=False))
        after = net(input_ids=probe, use_cache=False).logits[:, -1].cpu()
    if not torch.equal(before, after):
        raise RuntimeError('Checkpoint failed exact reload')
    delta = sum(float((state[n]-initial[n]).double().square().sum()) for n in state)**.5
    summary = dict(updates=len(metrics), requested_updates=args.steps, parameter_delta_l2=delta,
                   elapsed_s=time.monotonic()-start, checkpoint=str(checkpoint),
                   checkpoint_sha256=digest(checkpoint.read_bytes()), reload_logits_exact=True,
                   stop_reason='step_budget' if len(metrics)==args.steps else 'time_budget',
                   train_tasks=len(tasks), development_responses_forwarded=0,
                   cuda_peak_allocated=torch.cuda.max_memory_allocated() if args.device == 'cuda' else None)
    dump(args.output/'summary.json', summary)
    print(json.dumps(summary), flush=True)


if __name__ == '__main__':
    main()
