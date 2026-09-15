"""Clean W4 full-module curriculum training from the exact mixed-replay child.

This branch deliberately removes generated feedback and replay negatives.  It
uses only immutable reference targets from non-protected W4 rows, with a
short-to-long curriculum and a fixed protected evaluation on rows 47 and 107.
The protected rows are never training inputs or targets.
"""
import argparse
import hashlib
import json
import math
import os
import random
import shutil
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi


PACKET_SHA = 'a125a0d5bf66dedfb664c692c69dcd612181a8b7ac316c264075ca434061ce6c'
START_SHA = '1d4fce896e0d55b10cf3f6943df58fabd6aeebb3649c98822dc0385b36fd32c4'
TRAIN_ROWS = (42, 43, 44, 45, 46, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58)
VALID_ROWS = (59, 60, 61, 62, 63, 64)
EVAL_ROWS = (47, 107)
ALL_REFERENCE_ROWS = TRAIN_ROWS + VALID_ROWS + EVAL_ROWS
MODULE_NAMES = {47: 'W4Od2m7p4t2', 107: 'W4Od3m0p0t0'}
BUDGET = dict(
    updates=32, lr=1e-6, max_tokens=8192, max_new_tokens=2048,
    item_seconds=60, sany_seconds=30, seed=20260915,
    train_rows=list(TRAIN_ROWS), validation_rows=list(VALID_ROWS),
    eval_rows=list(EVAL_ROWS), response_only=True, clean_reference_targets=True,
    training_authorized=True, gate_claim=False, quality_claim=False,
    proof_claim=False, generalization_claim=False, tlc_claim=False,
    nonvacuity_claim=False,
)

# The shared decoder/trainer module has a deliberately conservative default
# budget for older probes.  Pin this experiment's budget explicitly so its
# protected evaluation cannot silently fall back to a 1024-token cap.
multi.BUDGET.update(
    updates=BUDGET['updates'], lr=BUDGET['lr'], seed=BUDGET['seed'],
    max_new_tokens=BUDGET['max_new_tokens'], item_seconds=BUDGET['item_seconds'],
    sany_seconds=BUDGET['sany_seconds'], train_only=False,
    eval_rows=list(EVAL_ROWS), gate_claim=False, quality_claim=False,
    generalization_claim=False, proof_claim=False, tlc_claim=False,
    nonvacuity_claim=False,
)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    return sha(Path(path).read_bytes())


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def packet_rows(path):
    raw = Path(path).read_bytes()
    if sha(raw) != PACKET_SHA:
        raise ValueError('Exact immutable W4 packet required')
    packet = json.loads(raw)
    if len(packet.get('rows', ())) != 169 or len(packet.get('encodings', ())) != 169:
        raise ValueError('Complete 169-row packet required')
    chosen = {}
    for i in ALL_REFERENCE_ROWS:
        row = packet['rows'][i]
        enc = packet['encodings'][i]
        if row.get('split') != 'train' or enc.get('id') != row.get('id'):
            raise ValueError(f'row {i} is not an exact training encoding')
        if (sha(row['prompt'].encode()) != row['prompt_sha256'] or
                sha(row['response'].encode()) != row['response_sha256'] or
                enc.get('prompt_sha256') != row['prompt_sha256'] or
                enc.get('response_sha256') != row['response_sha256']):
            raise ValueError(f'row {i} text identity mismatch')
        if not isinstance(enc.get('input_ids'), list) or not isinstance(enc.get('labels'), list):
            raise ValueError(f'row {i} is missing exact token arrays')
        chosen[i] = (row, enc)
    if set(TRAIN_ROWS) & set(EVAL_ROWS) or set(VALID_ROWS) & set(EVAL_ROWS):
        raise ValueError('Protected-row contamination')
    return packet, chosen


def curriculum_schedule():
    short = (42, 44, 45, 46, 48, 49, 50, 51)
    long = (43, 52, 53, 54, 55, 56, 57, 58)
    schedule = short + long + long + short
    if len(schedule) != BUDGET['updates'] or set(schedule) != set(TRAIN_ROWS):
        raise ValueError('Curriculum schedule does not cover exact training rows')
    return schedule


def admit(args):
    packet, chosen = packet_rows(args.input)
    if file_sha(args.checkpoint) != START_SHA:
        raise ValueError('Exact mixed-replay starting checkpoint required')
    schedule = curriculum_schedule()
    if (not set(TRAIN_ROWS).isdisjoint(EVAL_ROWS) or
            not set(VALID_ROWS).isdisjoint(EVAL_ROWS)):
        raise ValueError('Protected rows are not disjoint')
    result = dict(
        schema=1, kind='fullmodule_clean_structural_length_curriculum_admission',
        complete=True, input_sha256=PACKET_SHA, starting_checkpoint_sha256=START_SHA,
        train_rows=list(TRAIN_ROWS), validation_rows=list(VALID_ROWS), eval_rows=list(EVAL_ROWS),
        schedule=schedule, schedule_sha256=sha(json.dumps(schedule, separators=(',', ':')).encode()),
        budget=BUDGET, rows_loaded=len(chosen), protected_rows_never_train=True,
        generated_feedback_loaded=False, replay_negatives_loaded=False,
        clean_reference_targets_only=True, training_authorized=True,
        quality_claim=False, gate_claim=False, proof_claim=False,
        generalization_claim=False, tlc_claim=False, nonvacuity_claim=False,
    )
    if args.output.exists():
        raise ValueError('Admission output already exists')
    dump(args.output, result)
    print(json.dumps(result, sort_keys=True))
    return result


def eval_protected(net, tokenizer, chosen, tasks, current, output, phase):
    results = {}
    for i in EVAL_ROWS:
        row, enc = chosen[i]
        post = multi.decode(
            net, tokenizer, enc,
            forced_prefix=f'---- MODULE {MODULE_NAMES[i]} ----\n')
        result = dict(row=i, phase=phase, **post)
        result['candidate'] = (
            multi.sany.check(
                tasks[i], post['raw_reply'], output / 'sany_candidate' / phase / str(i), current,
                timeout=BUDGET['sany_seconds'])
            if post['finish_reason'] == 'eos' else None
        )
        results[str(i)] = result
        dump(output / f'{phase}-row-{i}.json', result)
    return results


def save_reload(net, selected, initial, config, ledger, probe_ids, checkpoint, device):
    import torch
    scratch = Path('/tmp') / f'tla-structural-curriculum-{os.getpid()}.pt'
    state = {n: p.detach().cpu().clone() for n, p in selected.items()}
    saved = dict(
        trainable_state=state, config=config, metrics=ledger,
        optimizer_state_stored=False, checkpoint_format='slim_trainable_state_no_optimizer',
        torch_rng_state=torch.get_rng_state(), python_rng_state=random.getstate(),
        cuda_rng_state=torch.cuda.get_rng_state_all() if device == 'cuda' else None,
    )
    try:
        torch.save(saved, scratch)
        probe = torch.tensor([probe_ids], device=device)
        with torch.no_grad(), lineage.helpers.autocast(device):
            before = net(input_ids=probe, use_cache=False).logits[:, -1].cpu().clone()
            for parameter in selected.values():
                parameter.zero_()
            restored = torch.load(scratch, map_location='cpu', weights_only=False)
            lineage.helpers.restore_trainable(selected, restored)
            exact_tensors = all(torch.equal(p.detach().cpu(), state[n])
                                for n, p in selected.items())
            after = net(input_ids=probe, use_cache=False).logits[:, -1].cpu()
        if not exact_tensors or not torch.equal(before, after):
            raise RuntimeError('Exact same-runtime checkpoint reload failed')
        scratch_sha = file_sha(scratch)
        shutil.copyfile(scratch, checkpoint)
        if file_sha(checkpoint) != scratch_sha:
            raise RuntimeError('Scratch-to-destination checkpoint hash mismatch')
        delta = math.sqrt(sum(float((state[n] - initial[n]).double().square().sum()) for n in state))
        return dict(
            checkpoint_sha256=scratch_sha, reload_tensors_exact=True, reload_logits_exact=True,
            checkpoint_copy_hash_exact=True, checkpoint_format='slim_trainable_state_no_optimizer',
            optimizer_state_stored=False, parameter_delta_l2=delta,
        )
    finally:
        scratch.unlink(missing_ok=True)


def worker(args):
    import torch
    import transformers

    admission = json.loads(args.admission.read_bytes())
    expected = admit(type('A', (), dict(input=args.input, checkpoint=args.checkpoint,
                                         output=Path('/tmp') / f'curriculum-admit-{os.getpid()}.json'))())
    Path('/tmp') .joinpath(f'curriculum-admit-{os.getpid()}.json').unlink(missing_ok=True)
    if admission != expected:
        raise ValueError('Admission drift')
    packet, chosen = packet_rows(args.input)
    args.output.mkdir(parents=True, exist_ok=False)
    dump(args.output / 'admission.json', admission)
    tasks = {i: multi.stage_task(multi.checker_task(packet, chosen[i][0]), args.output, str(i))
             for i in ALL_REFERENCE_ROWS}
    current = multi.sany.identity(list(tasks.values()))
    tokenizer = transformers.AutoTokenizer.from_pretrained(str(args.model_path), local_files_only=True)
    net = lineage.helpers.load_policy(str(args.model_path))
    saved = torch.load(args.checkpoint, map_location='cpu', weights_only=False)
    selected = lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(args.model_path))
    initial = {n: p.detach().cpu().clone() for n, p in selected.items()}
    selected = lineage.helpers.select_final_layer(net, True)
    encodings = {i: chosen[i][1] for i in ALL_REFERENCE_ROWS}
    before = eval_protected(net, tokenizer, chosen, tasks, current, args.output, 'restored_start')
    optimizer = torch.optim.AdamW(selected.values(), lr=BUDGET['lr'], weight_decay=0.0, foreach=False)
    ledger = []
    started = time.monotonic()
    for step, row_index in enumerate(curriculum_schedule(), 1):
        if time.monotonic() - started >= 600 - 90:
            raise RuntimeError('Curriculum reached checkpoint reserve before 32 updates')
        optimizer.zero_grad(set_to_none=True)
        result, metric = multi.teacher(net, encodings[row_index])
        if not math.isfinite(metric['loss']) or not math.isfinite(metric['target_top1']):
            raise RuntimeError(f'Nonfinite teacher metric at step {step}')
        result.loss.backward()
        norms = lineage.gradients(selected)
        norm = float(torch.nn.utils.clip_grad_norm_(selected.values(), 1.0,
                                                     error_if_nonfinite=True))
        if not math.isfinite(norm) or not any(norms.values()):
            raise RuntimeError(f'Incomplete or zero gradient at step {step}')
        optimizer.step()
        if any(not bool(torch.isfinite(p).all()) for p in selected.values()):
            raise RuntimeError(f'Nonfinite parameter at step {step}')
        entry = dict(step=step, row=row_index, loss=metric['loss'],
                     target_top1=metric['target_top1'], gradient_norm=norm,
                     gradient_norms=norms, response_tokens=encodings[row_index]['response_tokens'])
        ledger.append(entry)
        with (args.output / 'steps.jsonl').open('a') as stream:
            stream.write(json.dumps(entry) + '\n')
        print(json.dumps(entry), flush=True)
    if len(ledger) != BUDGET['updates']:
        raise RuntimeError('Executed update count differs from admitted curriculum')
    config = dict(
        schema=1, kind='fullmodule_clean_structural_length_curriculum',
        algorithm='clean response-only reference SFT; short-to-long W4 curriculum; final-layer AdamW',
        packet_sha256=PACKET_SHA, parent_sha256=START_SHA,
        train_rows=list(TRAIN_ROWS), validation_rows=list(VALID_ROWS), eval_rows=list(EVAL_ROWS),
        schedule=curriculum_schedule(), budget=BUDGET,
        model_files=lineage.helpers.model_files(args.model_path),
        dtype_profile=lineage.helpers.PROFILE, optimizer_state_stored=False,
        protected_targets_never_train=True, generated_feedback_loaded=False,
        replay_negatives_loaded=False, gate_claim=False, quality_claim=False,
        proof_claim=False, generalization_claim=False, tlc_claim=False, nonvacuity_claim=False,
    )
    reload_info = save_reload(
        net, selected, initial, config, ledger,
        encodings[TRAIN_ROWS[0]]['input_ids'][:64], args.output / 'policy_optimizer.pt', 'cuda')
    after = eval_protected(net, tokenizer, chosen, tasks, current, args.output, 'trained_child')
    references = {
        str(i): multi.sany.check(
            tasks[i], chosen[i][0]['response'], args.output / 'sany_reference' / str(i), current,
            timeout=BUDGET['sany_seconds'])
        for i in ALL_REFERENCE_ROWS
    }
    candidate_sany = {str(i): bool(after[str(i)]['candidate'] and
                                   after[str(i)]['candidate'].get('sany') == 1)
                      for i in EVAL_ROWS}
    reference_sany = {str(i): references[str(i)].get('sany') == 1 for i in ALL_REFERENCE_ROWS}
    receipt = dict(
        schema=1, kind='fullmodule_clean_structural_length_curriculum', complete=True,
        input_sha256=PACKET_SHA, starting_checkpoint_sha256=START_SHA,
        checkpoint_sha256=file_sha(args.output / 'policy_optimizer.pt'),
        updates=len(ledger), train_rows=list(TRAIN_ROWS), validation_rows=list(VALID_ROWS),
        eval_rows=list(EVAL_ROWS), curriculum_schedule=curriculum_schedule(),
        before=before, after=after, references=references,
        protected_candidate_sany_pass=candidate_sany,
        protected_reference_sany_pass={str(i): reference_sany[str(i)] for i in EVAL_ROWS},
        all_reference_sany_pass=reference_sany, reload=reload_info,
        training_authorized=True, protected_targets_never_train=True,
        generated_feedback_loaded=False, replay_negatives_loaded=False,
        quality_claim=False, gate_claim=False, proof_claim=False,
        generalization_claim=False, tlc_claim=False, nonvacuity_claim=False,
    )
    dump(args.output / 'receipt.json', receipt)
    print(json.dumps(receipt, sort_keys=True))


def main():
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=('admit', 'worker'))
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--checkpoint', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--admission', type=Path)
    p.add_argument('--model-path', type=Path)
    args = p.parse_args()
    if args.mode == 'admit':
        admit(args)
    else:
        if args.admission is None or args.model_path is None:
            p.error('worker requires --admission and --model-path')
        worker(args)


if __name__ == '__main__':
    main()
