"""Current-child SANY-feedback repair experiment.

This adapter keeps the audited six-row feedback objective, but binds it to the
2026-09-14 parent-broader child instead of the stale four-row policy used by
the historical feedback branch.  Rows 45, 46, 50--53 are development rows;
rows 47 and 107 remain protected and are never decoded or trained during
feedback collection.
"""
import argparse
import json
import os
import shutil
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi
from tools import proof_fullmodule_sany_feedback_corpus_probe as corpus
from tools import proof_fullmodule_sany_feedback_repair_probe as repair


CURRENT_CHILD_SHA = '3d7e08733268eccad08ab7dace3484c0e3b7158b5e84ab27658ccdd004af7304'
CURRENT_CHILD_PREFLIGHT_KIND = 'parent_broader_sft_cpu_preflight_v1'
CURRENT_CHILD_TENSOR_KIND = 'parent_broader_sft_independent_tensor_verification_v1'
PACKET_SHA = corpus.INPUT_SHA
DEV_ROWS = tuple(corpus.DEV_ROWS)
EVAL_ROWS = tuple(corpus.EVAL_ROWS)
PAIRED_RECEIPT_SHA = '2f3c13c99e17579265a5fba374a99729ef24953677bec9f3a4b4422b755628a6'
PAIRED_ROW47_LOG_SHA = 'a1ca54daeefb4136abd42319f38f130770f3fc6e73abf4b04bcec9b3e3fceafb'

# The adapter uses the already-audited corpus contract and worker, but replaces
# every stale policy/lineage admission with the current-child binding below.
repair.INPUT_SHA = corpus.INPUT_SHA
repair.DEV_ROWS = DEV_ROWS
repair.EVAL_ROWS = EVAL_ROWS
repair.ROW_IDS = corpus.ROW_IDS
repair.PROMPT_SHAS = corpus.PROMPT_SHAS
repair.RESPONSE_SHAS = corpus.RESPONSE_SHAS
repair.MODULE_NAMES = {
    45: 'W4Od18m9p1t2', 46: 'W4Od13m1p5t1', 50: 'W4Od10m2p0t3',
    51: 'W4Od4m2p0t1', 52: 'W4Od19m7p2t1', 53: 'W4Od12m7p3t1',
    47: 'W4Od2m7p4t2', 107: 'W4Od3m0p0t0',
}
repair.BUDGET = dict(
    # Thirty-two mixed updates keep the objective inside the approved
    # fifteen-minute Polaris envelope while limiting feedback memorization.
    updates=32, lr=5e-6, max_new_tokens=1024, item_seconds=45,
    sany_seconds=30, dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
    response_only=True, final_layer_only=True, training_authorized=True,
    gate_claim=False, generalization_claim=False, proof_claim=False,
    tlc_claim=False, nonvacuity_claim=False,
)
repair.REPAIR_ALGORITHM = (
    'mixed response-only current-child SANY-feedback repair plus clean-W4 '
    'replay v1; six feedback rows and eight disjoint replay rows; fresh '
    'final-layer AdamW; immutable targets'
)

REPLAY_ROWS = (42, 43, 44, 48, 49, 54, 55, 56)
FEEDBACK_WEIGHT = 0.35
REPLAY_WEIGHT = 0.65
REPLAY_ENCS = ()

# The historical optimizer reads multi.BUDGET, not repair.BUDGET.  Bind both
# explicitly so the declared budget is the executed budget, and keep the
# generation/SANY limits identical across the two helper modules.
multi.BUDGET.update(
    updates=repair.BUDGET['updates'], lr=repair.BUDGET['lr'],
    max_new_tokens=repair.BUDGET['max_new_tokens'],
    item_seconds=repair.BUDGET['item_seconds'],
    sany_seconds=repair.BUDGET['sany_seconds'],
    train_only=False, eval_rows=list(EVAL_ROWS), gate_claim=False,
    generalization_claim=False, proof_claim=False, tlc_claim=False,
    nonvacuity_claim=False,
)


def load(path):
    return json.loads(Path(path).read_bytes())


def dump(path, value):
    lineage.helpers.dump(Path(path), value)


def _hash(path):
    return lineage.helpers.file_sha(Path(path))


def _child_evidence(checkpoint, preflight, tensor_verification):
    if _hash(checkpoint) != CURRENT_CHILD_SHA:
        raise ValueError('Exact current parent-broader child checkpoint required')
    pre = load(preflight)
    tensor = load(tensor_verification)
    if pre.get('kind') != CURRENT_CHILD_PREFLIGHT_KIND or pre.get('complete') is not True:
        raise ValueError('Current child CPU preflight is incomplete or wrong kind')
    if tensor.get('kind') != CURRENT_CHILD_TENSOR_KIND or tensor.get('child_sha256') != CURRENT_CHILD_SHA:
        raise ValueError('Current child independent tensor evidence is not bound')
    if tensor.get('child_tensors_finite_fp32') is not True or tensor.get('same_nine_tensor_names') is not True:
        raise ValueError('Current child tensor evidence is not fully validated')
    return dict(
        child_checkpoint_sha256=CURRENT_CHILD_SHA,
        child_preflight_sha256=_hash(preflight),
        child_tensor_verification_sha256=_hash(tensor_verification),
        child_preflight_kind=pre.get('kind'),
        child_tensor_verification_kind=tensor.get('kind'),
        child_parent_sha256=tensor.get('parent_sha256'),
        child_updates=tensor.get('updates'),
        child_trainable_parameters=tensor.get('trainable_parameters'),
    )


def selected(raw):
    """Validate the pinned packet without the stale remote source manifest.

    The packet's full SHA is immutable and already staged/hashed.  The remote
    historical validator also pins the source tree from 2026-09-06, so using it
    here would reject the same packet for environmental drift.  Revalidate the
    complete model-ready fields needed by this experiment and every selected
    row's prompt/target identity instead.
    """
    if lineage.helpers.sha(raw) != PACKET_SHA:
        raise ValueError('Exact immutable TRAIN169 packet required')
    packet = json.loads(raw)
    rows = packet.get('rows')
    encodings = packet.get('encodings')
    if not isinstance(rows, list) or not isinstance(encodings, list) or len(rows) != 169 or len(encodings) != 169:
        raise ValueError('Complete 169-row packet required')
    chosen = {}
    for i in (*DEV_ROWS, *EVAL_ROWS):
        row, enc = rows[i], encodings[i]
        if (row.get('id'), row.get('prompt_sha256'), row.get('response_sha256')) != (
                corpus.ROW_IDS[i], corpus.PROMPT_SHAS[i], corpus.RESPONSE_SHAS[i]):
            raise ValueError(f'pinned corpus row {i} changed')
        if row.get('split') != 'train' or enc.get('id') != row.get('id'):
            raise ValueError(f'packet row {i} is not an exact training encoding')
        if enc.get('prompt_sha256') != row.get('prompt_sha256') or enc.get('response_sha256') != row.get('response_sha256'):
            raise ValueError(f'packet encoding hashes changed for row {i}')
        if not isinstance(enc.get('input_ids'), list) or not isinstance(enc.get('labels'), list):
            raise ValueError(f'packet encoding missing token arrays for row {i}')
        chosen[i] = (row, enc)
    return chosen, packet


def scaffold(a):
    selected(Path(a.input).read_bytes())
    evidence = _child_evidence(a.checkpoint, a.child_preflight, a.child_tensor_verification)
    return dict(
        schema=1,
        kind='sany_feedback_current_child_scaffold_v1',
        packet_sha256=PACKET_SHA,
        dev_rows=list(DEV_ROWS),
        eval_rows=list(EVAL_ROWS),
        row_ids={str(i): corpus.ROW_IDS[i] for i in (*DEV_ROWS, *EVAL_ROWS)},
        prompt_shas={str(i): corpus.PROMPT_SHAS[i] for i in (*DEV_ROWS, *EVAL_ROWS)},
        response_shas={str(i): corpus.RESPONSE_SHAS[i] for i in (*DEV_ROWS, *EVAL_ROWS)},
        **evidence,
        eval_rows_never_train=True,
        eval_rows_never_decoded=True,
        target_text_not_in_feedback=True,
        training_authorized=False,
        gate_claim=False,
        generalization_claim=False,
        proof_claim=False,
        tlc_claim=False,
        nonvacuity_claim=False,
        blocker='requires six current-child SANY feedback records',
    )


def _diagnostic(result):
    text = (result.get('process') or {}).get('output')
    return text if isinstance(text, str) and text else 'SANY status: ' + str(result.get('status', 'unknown'))


def _replay_encodings(raw):
    """Bind a disjoint clean W4 replay set from the immutable packet."""
    if lineage.helpers.sha(raw) != PACKET_SHA:
        raise ValueError('Exact immutable TRAIN169 packet required for replay')
    packet = json.loads(raw)
    rows, encodings = packet.get('rows'), packet.get('encodings')
    if not isinstance(rows, list) or not isinstance(encodings, list) or len(rows) != 169 or len(encodings) != 169:
        raise ValueError('Complete packet required for replay')
    values = []
    for i in REPLAY_ROWS:
        if i in DEV_ROWS or i in EVAL_ROWS:
            raise ValueError('Replay row overlaps feedback or protected evaluation')
        row, enc = rows[i], encodings[i]
        if row.get('split') != 'train' or enc.get('id') != row.get('id'):
            raise ValueError(f'Replay row {i} is not an exact training row')
        if (enc.get('prompt_sha256') != row.get('prompt_sha256') or
                enc.get('response_sha256') != row.get('response_sha256')):
            raise ValueError(f'Replay row {i} encoding hash mismatch')
        ids, labels = enc.get('input_ids'), enc.get('labels')
        prompt_tokens = enc.get('prompt_tokens')
        if (not isinstance(ids, list) or not isinstance(labels, list) or
                type(prompt_tokens) is not int or prompt_tokens <= 0 or
                labels != [-100] * prompt_tokens + ids[prompt_tokens:]):
            raise ValueError(f'Replay row {i} is not response-only encoded')
        values.append(enc)
    return tuple(values)


def _mixed_update(net, selected_t, train_encs, device='cuda', context=None,
                  measure=lambda _: None):
    """Run a weighted feedback/replay update with one exact step ledger."""
    import math
    import torch

    if len(train_encs) != len(DEV_ROWS) or len(REPLAY_ENCS) != len(REPLAY_ROWS):
        raise ValueError('Mixed update set does not match the admitted partition')
    context = context or (lambda: lineage.helpers.autocast(device))
    optimizer = torch.optim.AdamW(selected_t.values(), lr=multi.BUDGET['lr'],
                                  weight_decay=0., foreach=False)
    steps = []
    for step in range(1, multi.BUDGET['updates'] + 1):
        optimizer.zero_grad(set_to_none=True)
        feedback_metrics, replay_metrics = [], []
        for enc in train_encs:
            result, metric = multi.teacher(net, enc, device, context)
            (FEEDBACK_WEIGHT * result.loss / len(train_encs)).backward()
            feedback_metrics.append(metric)
            del result
        for enc in REPLAY_ENCS:
            result, metric = multi.teacher(net, enc, device, context)
            (REPLAY_WEIGHT * result.loss / len(REPLAY_ENCS)).backward()
            replay_metrics.append(metric)
            del result
        norms = lineage.gradients(selected_t)
        grad = float(torch.nn.utils.clip_grad_norm_(selected_t.values(), 1.,
                                                     error_if_nonfinite=True))
        optimizer.step()
        measure('after_step_' + str(step))
        all_metrics = feedback_metrics + replay_metrics
        if (not all(math.isfinite(x['loss']) and math.isfinite(x['target_top1'])
                    for x in all_metrics) or not math.isfinite(grad) or
                not any(norms.values())):
            raise ValueError('Nonfinite/zero mixed training evidence')
        feedback_loss = sum(x['loss'] for x in feedback_metrics) / len(feedback_metrics)
        replay_loss = sum(x['loss'] for x in replay_metrics) / len(replay_metrics)
        steps.append(dict(
            step=step,
            loss=[x['loss'] for x in all_metrics],
            target_top1=[x['target_top1'] for x in all_metrics],
            feedback_loss=feedback_loss,
            replay_loss=replay_loss,
            objective_loss=FEEDBACK_WEIGHT * feedback_loss + REPLAY_WEIGHT * replay_loss,
            feedback_weight=FEEDBACK_WEIGHT, replay_weight=REPLAY_WEIGHT,
            feedback_rows=list(DEV_ROWS), replay_rows=list(REPLAY_ROWS),
            gradient_norm=grad, gradient_norms=norms,
        ))
    return optimizer, steps


def collect(a):
    import torch
    import transformers

    frozen = load(a.admission)
    if frozen != scaffold(a):
        raise ValueError('Current-child scaffold admission drift')
    if a.output.exists():
        raise ValueError('Append-only output already exists')
    out = Path(a.output)
    out.mkdir(parents=True, exist_ok=False)
    chosen, packet = selected(Path(a.input).read_bytes())
    tasks = {
        i: multi.stage_task(multi.checker_task(packet, chosen[i][0]), out, str(i))
        for i in DEV_ROWS
    }
    current = multi.sany.identity(list(tasks.values()))
    tokenizer = transformers.AutoTokenizer.from_pretrained(str(a.model_path), local_files_only=True)
    net = lineage.helpers.load_policy(str(a.model_path))
    saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(a.model_path))
    del saved

    records = []
    results = {}
    started = time.monotonic()
    for i in DEV_ROWS:
        draft = multi.decode(net, tokenizer, chosen[i][1])
        result = multi.sany.check(
            tasks[i], draft['raw_reply'], out / 'sany' / str(i), current,
            timeout=30,
        )
        record = dict(
            row=i,
            draft=draft['raw_reply'],
            diagnostic=_diagnostic(result),
            draft_sha256=lineage.helpers.sha(draft['raw_reply'].encode()),
        )
        corpus.validate_feedback(record)
        records.append(record)
        results[str(i)] = dict(
            decode=draft,
            sany=result,
            diagnostic_sha256=lineage.helpers.sha(record['diagnostic'].encode()),
        )

    feedback = out / 'feedback.jsonl'
    with feedback.open('x') as stream:
        for record in records:
            stream.write(json.dumps(record, sort_keys=True) + '\n')
    dump(out / 'sany_results.json', results)
    evidence = _child_evidence(a.checkpoint, a.child_preflight, a.child_tensor_verification)
    receipt = dict(
        schema=1, complete=True, kind='sany_feedback_collection',
        dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
        eval_rows_never_decoded=True, eval_rows_never_train=True,
        input_sha256=PACKET_SHA,
        policy_checkpoint_sha256=CURRENT_CHILD_SHA,
        current_child=evidence,
        model_files=lineage.helpers.model_files(a.model_path),
        sany_identity=current,
        feedback_sha256=_hash(feedback),
        results_sha256=_hash(out / 'sany_results.json'),
        records=len(records), elapsed_seconds=time.monotonic() - started,
        training_authorized=False, gate_claim=False,
        generalization_claim=False, proof_claim=False, tlc_claim=False,
        nonvacuity_claim=False,
    )
    dump(out / 'receipt.json', receipt)
    return receipt


def eval_feedback(path, checkpoint):
    path = Path(path)
    if path.is_dir():
        paired = load(path / 'paired-generation-receipt.json')
        value = load(path / 'paired-row47.json')
        diagnostic = (path / 'paired-row47-sany.log').read_text()
        source_receipt_sha256 = PAIRED_RECEIPT_SHA
        if _hash(path / 'paired-generation-receipt.json') != PAIRED_RECEIPT_SHA:
            raise ValueError('Paired-generation receipt hash changed')
        if _hash(path / 'paired-row47-sany.log') != PAIRED_ROW47_LOG_SHA:
            raise ValueError('Paired row47 SANY log hash changed')
        value['packet_sha256'] = paired.get('packet_sha256')
        value['checkpoint_sha256'] = paired.get('checkpoint_sha256')
        value['draft_sha256'] = value.get('raw_reply_sha256')
        value['diagnostic'] = diagnostic
        value['diagnostic_sha256'] = lineage.helpers.sha(diagnostic.encode())
    else:
        value = load(path)
        diagnostic = value.get('diagnostic')
        source_receipt_sha256 = value.get('source_receipt_sha256')
    if value.get('row') != 47 or value.get('packet_sha256') != PACKET_SHA:
        raise ValueError('Current-child row47 feedback packet binding missing')
    if value.get('checkpoint_sha256') != CURRENT_CHILD_SHA or _hash(checkpoint) != CURRENT_CHILD_SHA:
        raise ValueError('Current-child row47 feedback checkpoint binding missing')
    draft = value.get('raw_reply', value.get('draft'))
    if not isinstance(draft, str) or not draft or not isinstance(diagnostic, str) or not diagnostic:
        raise ValueError('Row47 draft and exact SANY diagnostic required')
    if value.get('draft_sha256') != lineage.helpers.sha(draft.encode()):
        raise ValueError('Row47 draft hash changed')
    if value.get('diagnostic_sha256') != lineage.helpers.sha(diagnostic.encode()):
        raise ValueError('Row47 diagnostic hash changed')
    return dict(
        draft=draft,
        diagnostic=diagnostic,
        draft_sha256=value['draft_sha256'],
        diagnostic_sha256=value['diagnostic_sha256'],
        receipt_sha256=source_receipt_sha256,
    )


def eval_context_sha(path):
    path = Path(path)
    return PAIRED_RECEIPT_SHA if path.is_dir() else _hash(path)


def admit_training(a):
    frozen = load(a.scaffold)
    if frozen != scaffold(a):
        raise ValueError('Current-child scaffold admission drift')
    collection_receipt, _ = corpus.load_feedback(a.feedback)
    if collection_receipt.get('input_sha256') != PACKET_SHA:
        raise ValueError('Feedback packet binding changed')
    if collection_receipt.get('policy_checkpoint_sha256') != CURRENT_CHILD_SHA:
        raise ValueError('Feedback is not from the current child')
    if collection_receipt.get('eval_rows_never_train') is not True or collection_receipt.get('eval_rows_never_decoded') is not True:
        raise ValueError('Feedback collection does not attest eval isolation')
    prior = eval_feedback(a.eval_receipt, a.checkpoint)
    return dict(
        schema=1,
        kind='sany_feedback_current_child_worker_v1',
        algorithm=repair.REPAIR_ALGORITHM,
        budget=repair.BUDGET,
        dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
        replay_rows=list(REPLAY_ROWS),
        feedback_weight=FEEDBACK_WEIGHT, replay_weight=REPLAY_WEIGHT,
        executed_update_budget=multi.BUDGET['updates'],
        input_sha256=PACKET_SHA,
        scaffold_sha256=_hash(a.scaffold),
        feedback_receipt_sha256=_hash(Path(a.feedback) / 'receipt.json'),
        feedback_sha256=collection_receipt['feedback_sha256'],
        policy_checkpoint_sha256=CURRENT_CHILD_SHA,
        eval_feedback_sha256=eval_context_sha(a.eval_receipt),
        eval_row47_feedback=prior,
        eval_rows_never_train=True,
        feedback_targets_immutable=True,
        training_authorized=True,
        gate_claim=False, generalization_claim=False, proof_claim=False,
        tlc_claim=False, nonvacuity_claim=False,
    )


def worker(a):
    global REPLAY_ENCS
    # The historical worker contains the audited response-only update and
    # protected evaluation.  Only its stale admission hooks are replaced.
    repair.admit_training = admit_training
    repair.selected = selected
    repair.validate_eval_receipt = lambda path: eval_feedback(path, a.checkpoint)
    repair.load_feedback = corpus.load_feedback
    repair.validate_feedback = corpus.validate_feedback
    REPLAY_ENCS = _replay_encodings(Path(a.input).read_bytes())
    multi.update = _mixed_update

    # Polaris home is a parallel filesystem.  The historical helper wrote the
    # large torch archive there directly and one run ended with an NFS iostream
    # position error after compute had completed.  Preserve its exact reload
    # check, but execute it on node-local scratch and copy the verified bytes to
    # the append-only result path only after the scratch hash is final.
    def safe_save_reload(net, selected_t, optimizer, initial, config, metrics,
                         probe_ids, checkpoint, device):
        import torch

        scratch = Path('/tmp') / f'tla-current-child-repair-{os.getpid()}.pt'
        try:
            # The optimizer state is not needed to deploy or independently
            # reload this child: the worker is explicitly fresh-optimizer,
            # single-turn training.  Omitting its Adam moments reduces the
            # archive from about1.46GB to the validated nine-tensor weights
            # payload, which fits the user's Polaris home quota alongside the
            # immutable starting child.  Exact same-runtime reload is retained.
            state = {n: p.detach().cpu().clone() for n, p in selected_t.items()}
            saved = dict(
                trainable_state=state,
                config=config,
                metrics=metrics,
                torch_rng_state=torch.get_rng_state(),
                python_rng_state=__import__('random').getstate(),
                cuda_rng_state=torch.cuda.get_rng_state_all() if device == 'cuda' else None,
                optimizer_state_stored=False,
                checkpoint_format='slim_trainable_state_no_optimizer',
            )
            torch.save(saved, scratch)
            probe = torch.tensor([probe_ids], device=device)
            with torch.no_grad(), lineage.helpers.autocast(device):
                before = net(input_ids=probe, use_cache=False).logits[:, -1].cpu().clone()
                for parameter in selected_t.values():
                    parameter.zero_()
                restored = torch.load(scratch, map_location='cpu', weights_only=False)
                lineage.helpers.restore_trainable(selected_t, restored)
                exact_tensors = all(
                    torch.equal(p.detach().cpu(), state[n])
                    for n, p in selected_t.items()
                )
                after = net(input_ids=probe, use_cache=False).logits[:, -1].cpu()
            if not exact_tensors or not torch.equal(before, after):
                raise RuntimeError('Slim checkpoint failed exact same-runtime reload')
            info = dict(
                reload_tensors_exact=True,
                reload_logits_exact=True,
                parameter_delta_l2=sum(
                    float((state[n] - initial[n]).double().square().sum())
                    for n in state
                ) ** .5,
                checkpoint_sha256=_hash(scratch),
                optimizer_state_stored=False,
                checkpoint_format='slim_trainable_state_no_optimizer',
            )
            shutil.copyfile(scratch, checkpoint)
            destination_sha = _hash(checkpoint)
            if destination_sha != info.get('checkpoint_sha256'):
                raise RuntimeError('Checkpoint scratch-to-home hash mismatch')
            return dict(info, checkpoint_sha256=destination_sha,
                        checkpoint_scratch_reload_exact=True,
                        checkpoint_copy_hash_exact=True)
        finally:
            scratch.unlink(missing_ok=True)

    lineage.helpers.save_reload = safe_save_reload
    result = repair.repair_worker(a)
    if result.get('updates') != repair.BUDGET['updates']:
        raise RuntimeError('Executed update count differs from admitted budget')
    result.update(
        feedback_weight=FEEDBACK_WEIGHT,
        replay_weight=REPLAY_WEIGHT,
        replay_rows=list(REPLAY_ROWS),
        feedback_rows=list(DEV_ROWS),
        executed_update_budget=multi.BUDGET['updates'],
        anti_collapse_contract='protected candidate outputs must be EOS-complete modules; no promotion on extraction failure',
    )
    dump(Path(a.output) / 'receipt.json', result)
    return result


def _common(p):
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--checkpoint', type=Path, required=True)
    p.add_argument('--child-preflight', type=Path, required=True)
    p.add_argument('--child-tensor-verification', type=Path, required=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=('admit', 'collect', 'repair-admit', 'repair-worker'))
    _common(p)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--admission', type=Path)
    p.add_argument('--model-path', type=Path)
    p.add_argument('--scaffold', type=Path)
    p.add_argument('--feedback', type=Path)
    p.add_argument('--eval-receipt', type=Path)
    a = p.parse_args()
    if a.mode == 'admit':
        if a.output.exists():
            raise ValueError('Admission output must not exist')
        a.output.parent.mkdir(parents=True, exist_ok=True)
        dump(a.output, scaffold(a))
    elif a.mode == 'collect':
        if a.admission is None or a.model_path is None:
            p.error('collect requires --admission and --model-path')
        print(json.dumps(collect(a), sort_keys=True))
    elif a.mode == 'repair-admit':
        for value in (a.scaffold, a.feedback, a.eval_receipt):
            if value is None:
                p.error('repair-admit requires scaffold, feedback, and eval-receipt')
        if a.output.exists():
            raise ValueError('Admission output must not exist')
        a.output.parent.mkdir(parents=True, exist_ok=True)
        dump(a.output, admit_training(a))
    else:
        for value in (a.admission, a.model_path, a.scaffold, a.feedback, a.eval_receipt):
            if value is None:
                p.error('repair-worker requires admission, model-path, scaffold, feedback, and eval-receipt')
        print(json.dumps(worker(a), sort_keys=True))


if __name__ == '__main__':
    main()
