#!/usr/bin/env python3
"""Finite-candidate grouped REINFORCE with strict TLAPS rewards; not PPO/GRPO."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def reward_for(result):
    """Unknown/infrastructure outcomes never become zero-valued RL labels."""
    if result.get('timed_out') or result.get('status') in {
            'timeout', 'infrastructure_error', 'unrecognized_output', 'no_obligations', 'contract_reject'}:
        return None
    output = result.get('output', '')
    infrastructure = (r'(?im)^.*(?:command not found|No such file or directory|Permission denied|'
                      r'Cannot find module|could not find module|out of memory|timed out|timeout|'
                      r'backend .*not found|backend .*unavailable|exception|segmentation fault|interrupted).*$')
    if re.search(infrastructure, output):
        return None
    if (result.get('certified') is True and result.get('status') == 'pass'
            and result.get('returncode') == 0 and result.get('proved', 0) > 0
            and result.get('proved') == result.get('total')):
        return 1.0
    if result.get('status') not in {'verifier_reject', 'error'}:
        return None
    # Observed strict TLAPS proof-failure diagnostic. The generic final line
    # "There were backend errors" also appears on ordinary unproved obligations.
    if (re.search(r'(?m)^\[ERROR\]: [1-9]\d*/\d+ obligations? failed\.$', output)
            and '[ERROR]: Could not prove or check:' in output):
        return 0.0
    if re.search(r'(?m)^Error: Operator "[^"\n]+" not found\s*$', output):
        return 0.0
    return None


def advantages_for(rewards):
    if not rewards or any(r not in (0.0, 1.0) for r in rewards):
        return None
    mean = sum(rewards)/len(rewards)
    advantages = [r-mean for r in rewards]
    return advantages if any(advantages) else None


def centered_surrogate(selected_scores, advantages, temperature):
    """Exact sampled categorical gradient after the centered log-Z cancels."""
    import torch
    if temperature <= 0:
        raise ValueError('Positive policy temperature required')
    weights = torch.as_tensor(advantages, device=selected_scores.device, dtype=selected_scores.dtype)
    if (selected_scores.ndim != 1 or weights.shape != selected_scores.shape
            or not len(weights) or abs(float(weights.sum())) > 1e-6):
        raise ValueError('One same-task centered advantage group required')
    return -(weights.detach()*selected_scores/temperature).mean()


def grouped_weights(sampled, advantages, temperature):
    """Coefficients of -score for duplicate-aggregated runtime backward passes."""
    if (not sampled or len(sampled) != len(advantages) or temperature <= 0
            or abs(sum(advantages)) > 1e-6):
        raise ValueError('Invalid centered sampled group')
    return {index: sum(adv for sample, adv in zip(sampled, advantages) if sample == index)
            / (len(sampled)*temperature) for index in sorted(set(sampled))}


def task_schedule(count, groups, seed, shuffle=False):
    """A frozen full-population schedule, shuffled independently of policy RNG."""
    if count < 1 or groups < 1:
        raise ValueError('Nonempty population and schedule required')
    rng, scheduled = random.Random(seed), []
    while len(scheduled) < groups:
        epoch = list(range(count))
        if shuffle:
            rng.shuffle(epoch)
        scheduled.extend(epoch)
    return scheduled[:groups]


def differentiable_mean_logp(logits, labels):
    import torch
    labels = torch.as_tensor(labels, device=logits.device)
    mask = labels[1:] != -100
    if not mask.any():
        raise ValueError('No response labels')
    return logits[:-1][mask].float().log_softmax(-1).gather(1, labels[1:][mask, None]).mean()


def _step_augmented(task, candidate_limit):
    """Add prefix-derived proof-step candidates without consulting answers."""
    from tools.proof_official_extension import source_aware_candidates
    from tools.proof_premise_search import candidates as definition_candidates
    from tools.proof_source_scope import top_level_code
    from tools.proof_step_candidates import step_candidates
    sources = [task['prefix']] + [Path(p).read_text() for p in task['context']['library_sha256']]
    _, smt = source_aware_candidates(['BY SMT'], sources)
    visible = ['SMT'] if smt else []
    if any(re.search(r'(?m)^\s*PTL\s*==', top_level_code(s)) for s in sources):
        visible.append('PTL')
    defs = next((c[len('BY SMT DEF '):].split(', ')
                 for c in definition_candidates(task['prefix'])
                 if c.startswith('BY SMT DEF ')), [])
    steps, metadata = step_candidates(task['prefix'], task['theorem_name'],
                                      visible_backends=visible,
                                      visible_definitions=defs, limit=6)
    task['candidates'] = list(dict.fromkeys(task['candidates'][:2] + steps +
                                            task['candidates'][2:]))[:candidate_limit]
    task['candidate_language'] = dict(**metadata, proposed_steps=steps,
        mixture='two original choices, up to six prefix-derived step choices, original fallback')
    return task


def freeze_train(manifest_bytes, candidate_limit, *, step_candidates=False):
    from tools.proof_sequence_train import training_tasks
    from tools.proof_repair_pilot import with_dependency_context, prompt_for
    from tools.proof_retrieved_context import retrieve, render
    from tools.proof_fact_search import proposals
    from tools.proof_family_manifest import named_goals
    tasks = training_tasks(json.loads(manifest_bytes))
    if len(tasks) > 256:
        raise ValueError('Bounded learner supports at most256 frozen TRAIN tasks')
    frozen = []
    for source in tasks:
        task = {k:source[k] for k in ('id', 'prefix', 'suffix', 'theorem_name')}
        goals = named_goals(task['prefix']) if not source.get('target_goal') else []
        task['target_goal'] = source.get('target_goal') or (goals[-1] if goals else None)
        if not task['target_goal']:
            raise ValueError('Target statement missing')
        task['dependencies'] = source.get('dependencies', [])
        task['dependency_sha256'] = source.get('dependency_sha256', {})
        context = retrieve(task)
        candidates, _ = proposals(task['prefix'], task['theorem_name'], task['target_goal'],
            [Path(p).read_text() for p in task['dependencies']],
            [Path(p).read_text() for p in context['library_sha256']])
        task.update(context=context, candidates=candidates[:candidate_limit],
                    prompt=prompt_for(with_dependency_context(task))+render(context))
        if step_candidates:
            task = _step_augmented(task, candidate_limit)
        if not task['candidates']:
            raise ValueError('Empty candidate population')
        frozen.append(task)
    return frozen


def worker(a):
    from tools.proof_candidate_rank import encode_candidate
    from tools.proof_sequence_train import restore_trainable
    from harness.proof_fragment_check import certify_fragment
    started = time.monotonic()
    config = json.loads((a.output/'config.json').read_text())
    raw = (a.output/'frozen.json').read_bytes()
    if sha(raw) != config['frozen_sha256']:
        raise ValueError('Frozen data changed')
    for name, expected in config['implementation_sha256'].items():
        if sha((ROOT/name).read_bytes()) != expected:
            raise ValueError('Implementation changed after freeze: '+name)
    tasks = json.loads(raw)
    for task in tasks:
        for name, expected in {**task['dependency_sha256'], **task['context']['library_sha256']}.items():
            if sha(Path(name).read_bytes()) != expected:
                raise ValueError('Source dependency changed')
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(a.seed)
    rng = torch.Generator(device='cpu').manual_seed(a.seed)
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    encoded = [[encode_candidate(tokenizer, t['prompt'], c, a.max_tokens) for c in t['candidates']] for t in tasks]
    dump(a.output/'encodings.json', encoded)
    net = transformers.AutoModelForCausalLM.from_pretrained(a.model_path, local_files_only=True,
              torch_dtype=torch.float32).to(a.device).eval()
    net.requires_grad_(False)
    net.model.layers[-1].requires_grad_(True)
    trainable = {n:p for n,p in net.named_parameters() if p.requires_grad}
    model_files = {p.name:sha(p.read_bytes()) for p in a.model_path.iterdir()
                   if p.is_file() and p.suffix in {'.json', '.safetensors'}}
    if a.resume:
        if sha(a.resume.read_bytes()) != config['parent_sha256']:
            raise ValueError('Parent changed')
        saved = torch.load(a.resume, map_location='cpu', weights_only=False)
        if saved['config']['model_files'] != model_files:
            raise ValueError('Parent base model mismatch')
        restore_trainable(trainable, saved)
    initial = {n:p.detach().cpu().clone() for n,p in trainable.items()}
    optimizer = torch.optim.AdamW(trainable.values(), lr=a.lr, weight_decay=0)
    config.update(model_files=model_files, trainable_names=list(trainable),
                  trainable_parameters=sum(p.numel() for p in trainable.values()),
                  torch_version=torch.__version__, transformers_version=transformers.__version__)
    dump(a.output/'runtime-config.json', config)
    def score(e):
        ids = torch.tensor([e['input_ids']], device=a.device)
        return differentiable_mean_logp(net(input_ids=ids, use_cache=False).logits[0], e['labels'])
    updates, attempts, metrics = 0, 0, []
    with (a.output/'groups.jsonl').open('x') as ledger:
        for group, task_index in enumerate(task_schedule(len(tasks), a.steps, a.seed, a.shuffle_tasks)):
            if time.monotonic()-started > a.seconds-60:
                break
            task, enc = tasks[task_index], encoded[task_index]
            values = []
            with torch.inference_mode():
                for e in enc:
                    if time.monotonic()-started > a.seconds-60:
                        break
                    values.append(float(score(e)))
            if len(values) != len(enc):
                break
            logits = torch.tensor(values, dtype=torch.float64)/a.temperature
            if not torch.isfinite(logits).all():
                raise ValueError('Nonfinite policy scores')
            probabilities = logits.softmax(0)
            sampled = torch.multinomial(probabilities, a.group_size, replacement=True, generator=rng).tolist()
            rewards, checks, memo = [], [], {}
            for sample_index, index in enumerate(sampled):
                if index in memo:
                    reward, previous = memo[index]
                    checks.append(dict(sample_index=sample_index, candidate_index=index, memoized_from=previous))
                elif time.monotonic()-started > a.seconds-60-a.timeout:
                    reward = None
                    checks.append(dict(sample_index=sample_index, candidate_index=index, status='budget_excluded'))
                else:
                    result = certify_fragment(task['prefix'], task['candidates'][index], task['suffix'],
                        theorem_name=task['theorem_name'], dependencies=tuple(map(Path, task['dependencies'])),
                        work_root=a.output/'checks'/str(group)/str(sample_index), timeout=a.timeout)
                    attempts += 1
                    reward = reward_for(result)
                    memo[index] = (reward, sample_index)
                    checks.append(dict(sample_index=sample_index, candidate_index=index, reward=reward, **result))
                rewards.append(reward)
            advantages = advantages_for(rewards)
            row = dict(group=group, task=task['id'], sampled_ids=sampled, probabilities=probabilities.tolist(),
                       candidate_mean_logps=values, temperature=a.temperature, rewards=rewards, checks=checks,
                       entropy=float(torch.special.entr(probabilities).sum()),
                       distinct_sampled=len(set(sampled)), updated=False,
                       reward_variance=None if None in rewards else sum((r-sum(rewards)/len(rewards))**2 for r in rewards)/len(rewards))
            optimizer.zero_grad(set_to_none=True)
            if advantages is not None and time.monotonic()-started < a.seconds-60:
                # Sum repeated samples' weights; each recomputed graph is released
                # immediately. Centering is within this one task/group only.
                for index, weight in grouped_weights(sampled, advantages, a.temperature).items():
                    if weight:
                        loss = -score(enc[index])*weight
                        loss.backward()
                norm = torch.nn.utils.clip_grad_norm_(trainable.values(), 1., error_if_nonfinite=True)
                optimizer.step()
                updates += 1
                row.update(updated=True, gradient_norm=float(norm), advantages=advantages)
            else:
                row['skip_reason'] = 'unknown_reward' if None in rewards else ('zero_variance' if advantages is None else 'time_budget')
            row.update(actual_updates=updates, elapsed_seconds=time.monotonic()-started)
            metrics.append(row)
            ledger.write(json.dumps(row)+'\n'); ledger.flush()
            print(json.dumps({k:row[k] for k in ('group', 'task', 'rewards', 'updated', 'actual_updates')}), flush=True)
    state = {n:p.detach().cpu().clone() for n,p in trainable.items()}
    checkpoint = a.output/'policy_optimizer.pt'
    torch.save(dict(trainable_state=state, optimizer=optimizer.state_dict(), config=config, metrics=metrics,
                    torch_rng_state=torch.get_rng_state(), sampling_rng_state=rng.get_state(),
                    mps_rng_state=torch.mps.get_rng_state() if a.device == 'mps' else None), checkpoint)
    with torch.no_grad():
        probe = torch.tensor([encoded[0][0]['input_ids']], device=a.device)
        before = net(input_ids=probe, use_cache=False).logits[:, -1].cpu().clone()
        for parameter in trainable.values():
            parameter.zero_()
        restore_trainable(trainable, torch.load(checkpoint, map_location='cpu', weights_only=False))
        restored_exact = all(torch.equal(parameter.detach().cpu(), state[name]) for name, parameter in trainable.items())
        after = net(input_ids=probe, use_cache=False).logits[:, -1].cpu()
    if not restored_exact or not torch.equal(before, after):
        raise RuntimeError('Saved checkpoint did not reproduce exact trainable tensors and probe logits')
    delta = sum(float((state[n]-initial[n]).double().square().sum()) for n in state)**.5
    dump(a.output/'summary.json', dict(groups=len(metrics), requested_groups=a.steps, updates=updates,
         train_tasks=len(tasks), attempted_train_tasks=len({r['task'] for r in metrics}),
         checker_attempts=attempts, sampled_attempts=sum(len(r['sampled_ids']) for r in metrics),
         parameter_delta_l2=delta, checkpoint_sha256=sha(checkpoint.read_bytes()),
         reload_tensors_exact=restored_exact, reload_logits_exact=True,
         development_responses_forwarded=0, elapsed_seconds=time.monotonic()-started,
         stop_reason='group_budget' if len(metrics)==a.steps else 'time_budget',
         scope='finite-candidate policy learning on TRAIN; no development proof-capability claim'))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('manifest', 'model-path', 'output'):
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--resume', type=Path)
    p.add_argument('--device', choices=['cpu','cuda','mps'], default='mps')
    p.add_argument('--steps', type=int, default=16)
    p.add_argument('--candidates', type=int, default=8)
    p.add_argument('--group-size', type=int, default=4)
    p.add_argument('--temperature', type=float, default=1.)
    p.add_argument('--lr', type=float, default=1e-5)
    p.add_argument('--seconds', type=int, default=900)
    p.add_argument('--timeout', type=int, default=10)
    p.add_argument('--max-tokens', type=int, default=8192)
    p.add_argument('--seed', type=int, default=20260917)
    p.add_argument('--shuffle-tasks', action='store_true')
    p.add_argument('--step-candidates', action='store_true',
                   help='Add prefix-derived completed proof-step proposals')
    p.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    a = p.parse_args()
    if not (1 <= a.steps <= 64 and 2 <= a.candidates <= 8 and 2 <= a.group_size <= 8 and
            .05 <= a.temperature <= 5 and 0 < a.lr <= 1e-4 and 120 <= a.seconds <= 900 and
            1 <= a.timeout <= 10 and 128 <= a.max_tokens <= 8192):
        p.error('Invalid bounded RL budget')
    a.output = a.output.resolve()
    if a.worker:
        worker(a)
        return
    frozen = freeze_train(a.manifest.read_bytes(), a.candidates,
                          step_candidates=a.step_candidates)
    a.output.mkdir(parents=True, exist_ok=False)
    dump(a.output/'frozen.json', frozen)
    dump(a.output/'config.json', dict(args={k:str(v) if isinstance(v, Path) else v for k,v in vars(a).items()},
         implementation_sha256={name:sha((ROOT/name).read_bytes()) for name in (
             'tools/proof_candidate_rl.py', 'tools/proof_candidate_rank.py',
             'tools/proof_sequence_train.py', 'tools/proof_repair_pilot.py',
             'tools/proof_fact_search.py', 'tools/proof_premise_search.py', 'tools/proof_source_scope.py',
             'tools/proof_retrieved_context.py', 'tools/proof_family_manifest.py',
             'harness/proof_fragment_check.py', 'harness/runner.py')},
         frozen_sha256=sha((a.output/'frozen.json').read_bytes()), manifest_sha256=sha(a.manifest.read_bytes()),
         parent_sha256=sha(a.resume.read_bytes()) if a.resume else None,
         algorithm='finite-candidate grouped REINFORCE; centered same-task rewards; mean-logp categorical policy; not PPO/GRPO',
         optimizer='fresh AdamW final transformer layer only float32',
         sampling='actual current policy with replacement; no forced candidates',
         reward='strict TLAPS certified=1; narrow known rejection=0; unknown excludes whole group',
         memoization='same candidate within one sampled group only; reverify every new group',
         reference_fragment_used=False, train_ids=[t['id'] for t in frozen],
         task_schedule=[frozen[i]['id'] for i in task_schedule(len(frozen), a.steps, a.seed, a.shuffle_tasks)],
         hypothesis='TLAPS reward improves neural ranking of fixed symbolic proof candidates',
         measurement='actual updates, variance, parameter delta; separate matched development ranking required',
         candidate_language=('prefix-derived proof steps plus original proposals'
                             if a.step_candidates else 'original symbolic proposals')))
    (a.output/'tool.py').write_bytes(Path(__file__).read_bytes())
    from harness.runner import run_cmd
    command = [sys.executable, '-u', str(Path(__file__).resolve()), *sys.argv[1:], '--worker']
    code, output, elapsed, timed_out = run_cmd(command, ROOT, a.seconds+120)
    (a.output/'console.log').write_text(output)
    dump(a.output/'execution.json', dict(exit_code=code, elapsed_seconds=elapsed, timed_out=timed_out))
    print(output[-5000:])
    raise SystemExit(0 if code == 0 and not timed_out else 1)


if __name__ == '__main__':
    main()
