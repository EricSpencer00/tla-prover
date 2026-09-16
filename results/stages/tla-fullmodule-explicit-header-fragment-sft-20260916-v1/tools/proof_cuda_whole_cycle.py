#!/usr/bin/env python3
"""Matched whole-target developmental cycle; never a gate or RL claim."""
import argparse
import json
import math
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_cuda_cycle import run_processes, dump
from tools.proof_cuda_train import file_sha, model_files, validate_packet, encode_row, PROFILE
from tools.proof_cuda_hierarchical_cycle import validate_model_path, MODEL_PATH
from tools.proof_cuda_eval import read_rows, validate_tokenization, digest, sha

PARENT_SHA = '6d6c42def8283d50229862874c9b1ab7c2355a499159c0ae37b43c1bd18d7ca2'
CACHE_POLICY = 'release_unused_after_each_optimizer_step'
RESUME_CONFIG_SHA = 'c57764707d2ab32caeb19bd17c555b1b552ddee2bc157bd376e23fd537fe1401'
RESUME_FAILURE_SHA = '3665e3ed9866f61c4be9bcb89db2c55206259b960d5b942eaa20e48a62276787'
RESUME_ARTIFACT_SHA = {
    "base/config.json": "06eb4edb5b2b92c13c4316e9ff867cb6a90f6462e4107eb413fb79d0c97ef969",
    "base/summary.json": "69938f696568f2fb9a7db46745b0ce9171e52518c04acb5dc3b50517d18acc35",
    "base/generations.jsonl": "13b4c476094973adb3ba43a2d7fa4f5a26979bdcafac47c8745e7a65f1447dc6",
    "parent/config.json": "0e9c1568a15f18ced7051a37a7c6b6e49a063f25b036f79f800d7e5748a9ecce",
    "parent/summary.json": "6c363631d510d351fa82a051837fb5e808aac71ffc7fe945b69110be64c8517b",
    "parent/generations.jsonl": "3938a59a4068c38a1c75661ba89142d82f33c38a03d824638382f2820bd0d248",
    "training/config.json": "e788b32b05620b6681c4045044a74d4fd3fe790545075da3989e0e1e5ee74d92",
    "training/summary.json": "ae7b716588753b0a2ae3148c403cec328584ea25d08638a9ad1e30786ff6223b",
    "training/steps.jsonl": "896980618560b0f4813de6a00eaa5d8007c2fe69fe29df4e35d0ff2ec63ef5c4",
    "training/encodings.json": "309c07259861f9fc0cbf35ee4dda97c54c51a024df4739401682ff4794d42fea",
    "training/train.json": "78c3dd57247edde10c50dc12e6e8a3ca2f720f0a98f6d0eca901c359c13cfeff",
    "progress.json": "27a1df97388869c82982f71ef1b8f58e308a93d6d625da4b6993e98070c4794b"
}
FAILED_CHECKPOINT_SHA = 'ff984ddf6724fe87d96e9fa277839860077af4bd4f5a261a4eac6eb4f763ea1a'
RESUME_ALLOWED_CHANGES = {'tools/proof_cuda_train.py','tools/proof_cuda_whole_cycle.py',
                          'tools/proof_cuda_whole_cycle.pbs'}
TRAIN_SOURCES = ('tools/proof_cuda_train.py', 'tools/proof_sequence_train.py',
                 'tools/proof_candidate_rank.py', 'tools/proof_repair_pilot.py',
                 'tools/proof_whole_packet.py')


def check_encodings(tokenizer, packet, tasks):
    from tools.proof_cuda_whole_eval import encode_prompt
    feasibility = {r['id']:r for r in packet['token_feasibility']['rows']}
    train = {r['id']:r for r in packet['rows']}
    for task in tasks:
        actual = encode_prompt(tokenizer,task); expected = feasibility[task['id']]
        if (actual['status'] != 'ready' or actual['input_tokens'] != expected['prompt_tokens']
                or digest(actual['input_token_ids']) != expected['input_token_ids_sha256']):
            raise ValueError('Target runtime inference differs from local frozen token evidence')
        if task['id'] in train:
            encoded = encode_row(tokenizer,train[task['id']])
            if (encoded['input_ids'][:encoded['prompt_tokens']] != actual['input_token_ids']
                    or encoded['response_tokens'] != expected['response_tokens']
                    or len(encoded['input_ids']) != expected['total_tokens']):
                raise ValueError('Target runtime training/inference prefix or response changed')


def freeze(train, prompts, model, parent, train_sha, prompts_sha):
    from tools.proof_cuda_whole_eval import IMPLEMENTATION, BUDGET
    from tools.proof_whole_packet import validate_export
    if file_sha(train) != train_sha or file_sha(prompts) != prompts_sha:
        raise ValueError('Exact locally frozen TRAIN and probe packet hashes required')
    packet = json.loads(train.read_bytes()); rows = validate_packet(packet)
    if packet.get('packet_kind') != 'frozen6_whole_target_proofs' or len(rows) != 6:
        raise ValueError('Exact controlled six whole-target training examples required')
    tasks = validate_export(json.loads(prompts.read_bytes()))
    if {r['id']: r['prompt'] for r in rows} != {r['id']: r['prompt'] for r in tasks if r['split'] == 'train'}:
        raise ValueError('TRAIN and retention prompt mismatch')
    if file_sha(parent) != PARENT_SHA:
        raise ValueError('Exact immutable hierarchical parent checkpoint required')
    validate_model_path(model)
    if BUDGET['max_new_tokens'] != 3072 or BUDGET['seconds'] != 900 or BUDGET['profile'] != PROFILE:
        raise ValueError('Whole-proof probe contract changed')
    import transformers
    tokenizer = transformers.AutoTokenizer.from_pretrained(model,local_files_only=True)
    check_encodings(tokenizer,packet,tasks)
    sources = sorted(set(IMPLEMENTATION) | set(TRAIN_SOURCES) | {
        'tools/proof_cuda_whole_cycle.py', 'tools/proof_cuda_whole_cycle.pbs',
        'tools/proof_cuda_cycle.py', 'tools/proof_cuda_hierarchical_cycle.py',
        'tools/proof_cuda_repair_eval.py'})
    generation = json.loads((model/'generation_config.json').read_bytes())
    eos = generation['eos_token_id']
    eos = sorted(set(eos if isinstance(eos,list) else [eos]))
    if not eos or any(type(i) is not int or i < 0 for i in eos):
        raise ValueError('Pinned model must define valid EOS token IDs')
    return dict(train_input_sha256=train_sha, prompts_sha256=prompts_sha, eos_token_ids=eos,
                parent_checkpoint_sha256=PARENT_SHA, model_files=model_files(model),
                implementation_sha256={n:file_sha(ROOT/n) for n in sources},
                train_ids=[r['id'] for r in rows], train_evidence=packet['evidence'], profile=PROFILE)


def check_probe(path, raw, frozen, checkpoint_sha, tokenizer):
    from tools.proof_cuda_whole_eval import validate_run, IMPLEMENTATION
    config = json.loads((path/'config.json').read_bytes())
    rows = read_rows(path/'generations.jsonl')
    summary = json.loads((path/'summary.json').read_bytes())
    tasks = validate_run(raw, config, rows, summary)
    if summary.get('returncode') != 0 or summary.get('termination') != 'complete' or len(rows) != 10 or any(r['status'] != 'generated' for r in rows):
        raise ValueError('Complete measured ten-task probe required before advancement')
    expected = dict(model_files=frozen['model_files'], prompts_sha256=frozen['prompts_sha256'],
                    eos_token_ids=frozen['eos_token_ids'],
                    checkpoint_sha256=checkpoint_sha, arm='base' if checkpoint_sha is None else 'checkpoint',
                    implementation_sha256={n:frozen['implementation_sha256'][n] for n in IMPLEMENTATION})
    for key, value in expected.items():
        if config.get(key) != value:
            raise ValueError('Probe identity mismatch: '+key)
    for task, row in zip(tasks, rows):
        validate_tokenization(tokenizer, task, row)
    return dict(generated=10, train_generated=6, development_generated=4,
                checkpoint_sha256=checkpoint_sha, model_files=frozen['model_files'],
                prompts_sha256=frozen['prompts_sha256'], torch_version=config['torch_version'],
                transformers_version=config['transformers_version'],
                files_sha256={n:file_sha(path/n) for n in ('config.json','summary.json','generations.jsonl')})


def check_training(path, frozen):
    config = json.loads((path/'config.json').read_bytes())
    summary = json.loads((path/'summary.json').read_bytes())
    expected = dict(model_files=frozen['model_files'], input_sha256=frozen['train_input_sha256'],
                    train_ids=frozen['train_ids'], evidence=frozen['train_evidence'], dtype_profile=PROFILE,
                    requested_updates=100, seconds=600, seed=20260926, lr=1e-5, max_tokens=8192,
                    cuda_cache_policy=CACHE_POLICY,
                    implementation_sha256={n:frozen['implementation_sha256'][n] for n in TRAIN_SOURCES})
    for key, value in expected.items():
        if config.get(key) != value:
            raise ValueError('Training identity mismatch: '+key)
    if (summary.get('reload_tensors_exact') is not True or summary.get('reload_logits_exact') is not True
            or summary.get('evaluation_responses_forwarded') != 0 or summary.get('train_tasks') != 6
            or summary.get('attempted_train_tasks') != 6 or summary.get('updates') != 100
            or summary.get('requested_updates') != 100):
        raise ValueError('Complete six-task, hundred-update coverage and exact reload required')
    for name in ('parameter_delta_l2','cuda_peak_allocated','cuda_peak_reserved'):
        value = summary.get(name)
        if not isinstance(value, (int,float)) or not math.isfinite(value) or value <= 0:
            raise ValueError('Missing finite positive training health: '+name)
    if max(summary['cuda_peak_allocated'], summary['cuda_peak_reserved']) > 36*1024**3:
        raise ValueError('Memory headroom exceeded')
    steps = read_rows(path/'steps.jsonl')
    if (len(steps) != 100 or [r['step'] for r in steps] != list(range(1,101))
            or {r['task'] for r in steps} != set(frozen['train_ids'])
            or any(not math.isfinite(r[k]) for r in steps for k in ('loss','gradient_norm'))):
        raise ValueError('Actual optimizer ledger incomplete or unhealthy')
    if file_sha(path/'policy_optimizer.pt') != summary['checkpoint_sha256']:
        raise ValueError('Checkpoint bytes changed')
    return summary


def runtime_versions():
    import torch
    import transformers
    return dict(torch_version=torch.__version__,transformers_version=transformers.__version__)


def validate_resume(source, output, runtime_root, frozen, raw, tokenizer):
    """Reuse only the exact completed parents of the known headroom failure.

    This never resumes optimizer state, executes old code, copies old results,
    or admits its over-budget trained checkpoint as a valid child.
    """
    source=source.resolve(strict=True); runtime_root=runtime_root.resolve(strict=True)
    output=output.resolve()
    for original in (source,runtime_root):
        if output==original or output in original.parents or original in output.parents:
            raise ValueError('Recovery output must be isolated from original evidence/runtime')
    if ((source/'whole').exists() or (source/'summary.json').exists()
            or file_sha(source/'config.json')!=RESUME_CONFIG_SHA
            or file_sha(source/'failure.json')!=RESUME_FAILURE_SHA):
        raise ValueError('Only the pinned pre-child memory-headroom failure is recoverable')
    config=json.loads((source/'config.json').read_bytes())
    failure=json.loads((source/'failure.json').read_bytes()); old=config['frozen']
    if (failure.get('error')!="ValueError('Memory headroom exceeded')"
            or failure.get('completed_phases')!=['matched_parent_probes']):
        raise ValueError('Unexpected original failure phase')
    names=old['implementation_sha256']
    if len(names)!=12 or set(names)!=set(frozen['implementation_sha256']):
        raise ValueError('Exact original twelve-file runtime inventory required')
    for name, expected in names.items():
        if file_sha(runtime_root/name)!=expected:
            raise ValueError('Original staged runtime changed: '+name)
        if name not in RESUME_ALLOWED_CHANGES and frozen['implementation_sha256'][name]!=expected:
            raise ValueError('Recovery changed probe, packet or encoder: '+name)
    for key in ('train_input_sha256','prompts_sha256','eos_token_ids','parent_checkpoint_sha256',
                'model_files','train_ids','train_evidence','profile'):
        if old[key]!=frozen[key]:
            raise ValueError('Recovery input/model contract differs: '+key)
    if (file_sha(runtime_root/'train.json')!=old['train_input_sha256']
            or file_sha(runtime_root/'prompts.json')!=old['prompts_sha256']
            or sha(raw)!=old['prompts_sha256']):
        raise ValueError('Original staged inputs or requested prompts changed')
    for name,expected in RESUME_ARTIFACT_SHA.items():
        if file_sha(source/name)!=expected:
            raise ValueError('Original recovery artifact changed: '+name)
    base=check_probe(source/'base',raw,old,None,tokenizer)
    parent=check_probe(source/'parent',raw,old,PARENT_SHA,tokenizer)
    versions=runtime_versions()
    for arm in (base,parent):
        if any(arm.get(k)!=v for k,v in versions.items()):
            raise ValueError('Recovery runtime libraries differ from original parents')
    train=source/'training'; summary=json.loads((train/'summary.json').read_bytes())
    if (file_sha(train/'policy_optimizer.pt')!=FAILED_CHECKPOINT_SHA
            or summary.get('checkpoint_sha256')!=FAILED_CHECKPOINT_SHA
            or summary.get('updates')!=100 or summary.get('attempted_train_tasks')!=6
            or summary.get('reload_tensors_exact') is not True
            or summary.get('reload_logits_exact') is not True
            or summary.get('cuda_peak_reserved')!=39862665216):
        raise ValueError('Original failed-training evidence changed')
    files=['config.json','failure.json','progress.json',
           'training/config.json','training/summary.json','training/steps.jsonl',
           'training/encodings.json','training/train.json','training/policy_optimizer.pt']
    files += [arm+'/'+name for arm in ('base','parent')
              for name in ('config.json','summary.json','generations.jsonl')]
    return dict(source=str(source),runtime_root=str(runtime_root),
        source_files_sha256={name:file_sha(source/name) for name in files},
        original_runtime_sha256=names,base=base,parent=parent,runtime_versions=versions,
        allowed_runtime_changes=sorted(n for n in names if names[n]!=frozen['implementation_sha256'][n]),
        failed_checkpoint_sha256=FAILED_CHECKPOINT_SHA,failed_checkpoint_loaded=False,
        optimizer_resume=False,training_parent='fresh immutable base',
        cache_policy=CACHE_POLICY,parents_regenerated=False)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('train-input','prompts','parent-checkpoint','output'):
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--train-sha256', required=True); p.add_argument('--prompts-sha256', required=True)
    p.add_argument('--model-path', type=Path, default=MODEL_PATH)
    p.add_argument('--resume-cycle', type=Path)
    p.add_argument('--resume-runtime-root', type=Path)
    a = p.parse_args(); a.output = a.output.resolve()
    if bool(a.resume_cycle)!=bool(a.resume_runtime_root):
        p.error('--resume-cycle and --resume-runtime-root are required together')
    if a.output == a.parent_checkpoint.resolve() or a.output in a.parent_checkpoint.resolve().parents:
        raise ValueError('New output must not contain immutable parent')
    a.output.mkdir(parents=True, exist_ok=False)
    started = time.monotonic(); progress = []
    def record(phase, result):
        progress.append(dict(phase=phase,elapsed_seconds=time.monotonic()-started,result=result))
        dump(a.output/'progress.json',progress); print(json.dumps(progress[-1]),flush=True)
    try:
        def current():
            return freeze(a.train_input,a.prompts,a.model_path,a.parent_checkpoint,a.train_sha256,a.prompts_sha256)
        frozen = current()
        import transformers
        tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path,local_files_only=True)
        raw = a.prompts.read_bytes()
        recovery=(validate_resume(a.resume_cycle,a.output,a.resume_runtime_root,frozen,raw,tokenizer)
                  if a.resume_cycle else None)
        def guard():
            if current() != frozen: raise ValueError('Frozen inputs/runtime/model changed between phases')
            if recovery and validate_resume(a.resume_cycle,a.output,a.resume_runtime_root,frozen,raw,tokenizer)!=recovery:
                raise ValueError('Original recovery evidence changed between phases')
        dump(a.output/'config.json',dict(frozen=frozen,
            hypothesis='Whole-target proof supervision improves complete proof construction versus BASE and repair-trained parent',
            training='Fresh-base final-layer response SFT, fresh optimizer; not RL or parent resume',
            confounds='Six new-family whole targets versus seventeen old repair spans; changed training population, prompt and response length; not a causal isolation of hierarchy',
            measurement='Matched greedy3072 six TRAIN whole-target extensions and four reused DEV repairs, separate contracts and denominators; not G2',
            budgets=dict(parent_parallel_seconds=900,training_seconds=600,child_seconds=900,total_supervisor_seconds=2700),
            stop='Incomplete parents, time-limited replies, changed provenance, incomplete training, failed reload or excess memory stop advancement',
            recovery=recovery,
            recovery_confounds='Only training CUDA cache release policy changed; completed parent outputs reused exactly; fresh base and optimizer, failed checkpoint never loaded',
            proof_success_claim=False,strict_verification='Local serial strict30s checks after collection'))
        def command(name, checkpoint=None):
            cmd = [sys.executable,str(ROOT/'tools/proof_cuda_whole_eval.py'),'generate',
                   '--prompts',str(a.prompts),'--model-path',str(a.model_path),'--output',str(a.output/name)]
            if checkpoint: cmd += ['--checkpoint',str(checkpoint)]
            return cmd
        guard()
        if recovery:
            base,parent=recovery['base'],recovery['parent']
        else:
            run_processes([command('base'),command('parent',a.parent_checkpoint)],
                          [a.output/'base.log',a.output/'parent.log'],920)
            guard()
            base = check_probe(a.output/'base',raw,frozen,None,tokenizer)
            parent = check_probe(a.output/'parent',raw,frozen,PARENT_SHA,tokenizer)
        compare = ('model_files','prompts_sha256','torch_version','transformers_version')
        if any(base[k] != parent[k] for k in compare): raise ValueError('Unmatched parent probes')
        record('matched_parent_probes',dict(base=base,parent=parent))
        train = a.output/'training'; guard()
        run_processes([[sys.executable,str(ROOT/'tools/proof_cuda_train.py'),'train',
            '--input',str(a.train_input),'--expected-input-sha256',frozen['train_input_sha256'],
            '--model-path',str(a.model_path),'--output',str(train),'--seed','20260926',
            '--steps','100','--seconds','600']],[a.output/'training.log'],620)
        guard(); trained = check_training(train,frozen); record('fresh_whole_sft',trained)
        run_processes([command('whole',train/'policy_optimizer.pt')],[a.output/'whole.log'],920)
        guard(); child = check_probe(a.output/'whole',raw,frozen,trained['checkpoint_sha256'],tokenizer)
        if any(base[k] != child[k] for k in compare): raise ValueError('Unmatched child probe')
        record('whole_probe',child)
        dump(a.output/'summary.json',dict(status='developmental_generation_cycle_complete',
            elapsed_seconds=time.monotonic()-started,verification_pending=True,proof_success_claim=False,
            train_retention_tasks=6,reused_development_tasks=4,official_evaluation_tasks=0))
    except BaseException as exc:
        dump(a.output/'failure.json',dict(error=repr(exc),elapsed_seconds=time.monotonic()-started,
            completed_phases=[r['phase'] for r in progress],proof_success_claim=False))
        raise


if __name__ == '__main__': main()
