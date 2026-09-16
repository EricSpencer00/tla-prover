"""SANY-feedback-conditioned full-module repair experiment.

The development feedback artifact contains only model drafts and the exact
owned SANY diagnostics.  It is converted into two response-only examples
whose targets are the immutable packet references.  Rows 47 and 107 remain
protected evaluation rows: row47 receives its already-recorded invalid draft
and diagnostic as repair context, while row107 is decoded normally.
"""
import argparse, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi


def load(path):
    return json.loads(Path(path).read_bytes())

INPUT_SHA = multi.INPUT_SHA
BASE_KIND = 'multiexample_4train_structural_fullmodule_probe'
DEV_ROWS = (45, 46)
EVAL_ROWS = (47, 107)
ROW_IDS = {
    45: 'w4-fullmodule:w4opus::d18-m9-p1-t2',
    46: 'w4-fullmodule:w4opus::d13-m1-p5-t1',
    47: 'w4-fullmodule:w4opus::d2-m7-p4-t2',
    107: 'w4-fullmodule:w4opus::d3-m0-p0-t0',
}
MODULE_NAMES = {45: 'W4Od18m9p1t2', 46: 'W4Od13m1p5t1', 47: 'W4Od2m7p4t2', 107: 'W4Od3m0p0t0'}
RESPONSE_SHAS = {
    45: 'bad6c0dff5965a7363ecf1abf1a6a3faab714ad81cceff6c88b223cd62dac9fb',
    46: '9f436f4463f97528db6c948e1d0befd03bd20d18cdb14065d53af6d40827872c',
    47: '36c548d2a475c0d086ddf0340f927b36002699ce86e955d702e061324ad2f07c',
    107: '5f6b169dc010369d4e6f65b7766b7961e44a4df15790988c5763861a06e3e853',
}
PROMPT_SHAS = {
    45: 'b64c4d644820db3e58bbfd73939d2bd152d1d595d60c8966a2ec301e55842e4d',
    46: '9fd26650efd01caf164643adf86025bcfa79f659b3f3c71073ad29c27597f934',
    47: '32eb750d7db375df72e8e93d929ac3e5c7a365d50a915202c62db6e3d675877f',
    107: '388d75fc27a48d38ccb3fd0258a72ddfd1b9dbb0852b0b058057521e8eaafb51',
}
BUDGET = dict(updates=128, lr=1e-5, max_new_tokens=1024, item_seconds=45,
              sany_seconds=30, dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
              response_only=True, final_layer_only=True, gate_claim=False,
              generalization_claim=False, proof_claim=False, tlc_claim=False,
              nonvacuity_claim=False, training_authorized=False)

REPAIR_ALGORITHM = 'response-only SANY-feedback-conditioned structural repair v7; pinned-header budget-reserved footer-constrained decoding; fresh final-layer AdamW; immutable reference targets'
STRUCTURAL_HINT_V2 = (
    'Structural requirements: emit exactly one complete TLA+ module and finish with one ==== footer. '
    'Use valid function-set syntax such as [1..N -> 0..Cap] (the arrow belongs inside the brackets), '
    'do not repeat declarations or Spec lines, and do not invent a second module. '
)


def load(path):
    return json.loads(Path(path).read_bytes())


def dump(path, value):
    lineage.helpers.dump(Path(path), value)


def selected(raw):
    if lineage.helpers.sha(raw) != INPUT_SHA:
        raise ValueError('Exact immutable TRAIN169 packet required')
    packet = json.loads(raw)
    rows = lineage.packet.validate_training_packet(packet)
    selected_rows = {}
    for i in (*DEV_ROWS, *EVAL_ROWS):
        row, enc = rows[i], packet['encodings'][i]
        if row['id'] != ROW_IDS[i] or row['response_sha256'] != RESPONSE_SHAS[i] or row['prompt_sha256'] != PROMPT_SHAS[i]:
            raise ValueError(f'pinned feedback row {i} changed')
        if row['split'] != 'train':
            raise ValueError(f'packet row {i} changed split')
        selected_rows[i] = (row, enc)
    return selected_rows, packet


def admit(input_path, base_admission_path):
    chosen, _ = selected(Path(input_path).read_bytes())
    base_admission = json.loads(Path(base_admission_path).read_bytes())
    if base_admission.get('kind') != BASE_KIND:
        raise ValueError('exact authenticated four-row admission required')
    if tuple(base_admission.get('rows', {}).get('train', ())) != (42, 43, 44, 49):
        raise ValueError('four-row training partition changed')
    if tuple(base_admission.get('rows', {}).get('eval', ())) != EVAL_ROWS:
        raise ValueError('protected eval partition changed')
    if base_admission.get('input_sha256') != INPUT_SHA:
        raise ValueError('base packet pin changed')
    # This is intentionally an admission-only artifact.  Feedback examples
    # must be produced and SANY-attested by the frozen checkpoint later.
    return dict(schema=1, kind='sany_feedback_repair_scaffold', budget=BUDGET,
        dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
        row_ids={str(i): ROW_IDS[i] for i in (*DEV_ROWS, *EVAL_ROWS)},
        response_shas={str(i): RESPONSE_SHAS[i] for i in (*DEV_ROWS, *EVAL_ROWS)},
        prompt_shas={str(i): PROMPT_SHAS[i] for i in (*DEV_ROWS, *EVAL_ROWS)},
        input_sha256=INPUT_SHA,
        base_admission_sha256=lineage.helpers.file_sha(Path(base_admission_path)),
        feedback_training_authorized=False, eval_rows_never_train=True,
        gate_claim=False, generalization_claim=False, proof_claim=False,
        tlc_claim=False, nonvacuity_claim=False,
        blocker='requires frozen four-row checkpoint plus authenticated dev SANY feedback records')


def validate_feedback(record, allowed_rows=None):
    """Validate draft/error records without admitting target answers."""
    if allowed_rows is None:
        allowed_rows = DEV_ROWS
    if not isinstance(record, dict) or set(record) != {'row', 'draft', 'diagnostic', 'draft_sha256'}:
        raise ValueError('feedback record must contain only row,draft,diagnostic,draft_sha256')
    i = record['row']
    if i not in allowed_rows:
        raise ValueError('feedback record is outside development rows')
    if not isinstance(record['draft'], str) or not record['draft']:
        raise ValueError('draft required')
    if not isinstance(record['diagnostic'], str) or not record['diagnostic']:
        raise ValueError('authenticated SANY diagnostic required')
    if lineage.helpers.sha(record['draft'].encode()) != record['draft_sha256']:
        raise ValueError('draft hash changed')
    if 'sany' not in record['diagnostic'].lower() and 'error' not in record['diagnostic'].lower():
        raise ValueError('diagnostic is not visibly a SANY/error report')
    return True


def load_feedback(path):
    """Load and authenticate the completed append-only collection artifact."""
    path = Path(path)
    receipt = load(path / 'receipt.json')
    if receipt.get('kind') != 'sany_feedback_collection' or receipt.get('complete') is not True:
        raise ValueError('completed SANY feedback collection required')
    stream = path / 'feedback.jsonl'
    if lineage.helpers.file_sha(stream) != receipt.get('feedback_sha256'):
        raise ValueError('feedback artifact hash changed')
    records = [json.loads(line) for line in stream.read_text().splitlines() if line.strip()]
    if [r.get('row') for r in records] != list(DEV_ROWS):
        raise ValueError('exact ordered development feedback records required')
    for record in records:
        validate_feedback(record)
    return receipt, {record['row']: record for record in records}


def feedback_prompt(row_prompt, draft, diagnostic, module_name=None):
    """Stable repair instruction; never includes the target/reference text."""
    module_hint = (f'Use exactly this module declaration: ---- MODULE {module_name} ----\n'
                   if module_name else '')
    return (row_prompt + '\n\n' + STRUCTURAL_HINT_V2 + '\n' + module_hint +
            'The previous generated TLA+ module failed the owned SANY check. '
            'Repair the module below and return only the complete corrected module.\n'
            '--- previous draft ---\n' + draft + '\n'
            '--- exact SANY diagnostic ---\n' + diagnostic + '\n'
            '--- end feedback ---')


def repair_encodings(tokenizer, chosen, records):
    """Build exact response-only encodings from feedback plus immutable targets."""
    encodings = {}
    for i in DEV_ROWS:
        row, _ = chosen[i]
        rec = records[i]
        prompt = feedback_prompt(row['prompt'], rec['draft'], rec['diagnostic'], MODULE_NAMES[i])
        enc = lineage.helpers.encode_candidate(tokenizer, prompt, row['response'], 8192)
        encodings[i] = dict(enc, prompt_sha256=lineage.helpers.sha(prompt.encode()),
                            target_sha256=row['response_sha256'], feedback_draft_sha256=rec['draft_sha256'],
                            diagnostic_sha256=lineage.helpers.sha(rec['diagnostic'].encode()))
    return encodings


def eval_feedback_prompt(row_prompt, draft, diagnostic):
    return feedback_prompt(row_prompt, draft, diagnostic, MODULE_NAMES[47])


def validate_eval_receipt(path):
    """Extract the immutable prior row47 draft/diagnostic without training on it."""
    receipt = load(path)
    if not isinstance(receipt.get('post'), dict) or '47' not in receipt['post']:
        raise ValueError('prior four-row evaluation receipt lacks row47')
    post = receipt['post']['47']; candidate = (receipt.get('candidate') or {}).get('47')
    draft = post.get('raw_reply')
    diagnostic = ((candidate or {}).get('process') or {}).get('output')
    if not isinstance(draft, str) or not draft or not isinstance(diagnostic, str) or not diagnostic:
        raise ValueError('row47 draft and exact SANY diagnostic required')
    if post.get('finish_reason') != 'eos' or (candidate or {}).get('status') != 'model_sany_reject':
        raise ValueError('row47 must be the recorded EOS SANY rejection')
    return dict(draft=draft, diagnostic=diagnostic,
                draft_sha256=lineage.helpers.sha(draft.encode()),
                diagnostic_sha256=lineage.helpers.sha(diagnostic.encode()),
                receipt_sha256=lineage.helpers.file_sha(path))


def _diagnostic(result):
    """Return the exact owned SANY diagnostic, without inventing feedback."""
    process = result.get('process') or {}
    text = process.get('output')
    if isinstance(text, str) and text:
        return text
    # Extraction and bounded-process outcomes have no SANY stdout, but must
    # still be represented explicitly rather than silently treated as passes.
    return 'SANY status: ' + str(result.get('status', 'unknown'))


def collect(a):
    """Decode only dev rows and attach an owned SANY diagnostic to each draft.

    This is deliberately inference-only: the frozen policy is restored from
    ``a.checkpoint`` and no optimizer or parameter update is constructed.
    Eval rows are admitted only as protected partition metadata and are never
    decoded, checked, or copied into the feedback stream.
    """
    import torch
    import transformers

    frozen = load(a.admission)
    # Revalidate the packet and parent admission before loading a large model.
    scaffold = admit(a.input, a.base_admission)
    if scaffold != frozen:
        raise ValueError('Admission drift')
    if a.output.exists():
        raise ValueError('Append-only output already exists')
    out = Path(a.output)
    out.mkdir(parents=True, exist_ok=False)
    chosen, packet = selected(Path(a.input).read_bytes())
    tasks = {}
    for i in DEV_ROWS:
        tasks[i] = multi.stage_task(multi.checker_task(packet, chosen[i][0]), out, str(i))
    current = multi.sany.identity(list(tasks.values()))

    tokenizer = transformers.AutoTokenizer.from_pretrained(str(a.model_path), local_files_only=True)
    net = lineage.helpers.load_policy(str(a.model_path))
    saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    selected_t = lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(a.model_path))
    # restore_policy deliberately leaves the layer frozen for safe inference;
    # explicitly opt into gradients only after checkpoint identity is verified.
    selected_t = lineage.helpers.select_final_layer(net, True)
    del selected_t, saved

    results = {}
    records = []
    started = time.monotonic()
    for i in DEV_ROWS:
        # The scaffold intentionally carries only hashes/partitions.  Decode
        # against the freshly revalidated immutable packet encoding selected
        # above, never against an unpinned admission field.
        draft = multi.decode(net, tokenizer, chosen[i][1])
        result = multi.sany.check(
            tasks[i], draft['raw_reply'], out / 'sany' / str(i), current,
            timeout=BUDGET['sany_seconds'])
        diagnostic = _diagnostic(result)
        record = dict(row=i, draft=draft['raw_reply'], diagnostic=diagnostic,
                      draft_sha256=lineage.helpers.sha(draft['raw_reply'].encode()))
        validate_feedback(record)
        records.append(record)
        results[str(i)] = dict(decode=draft, sany=result,
                               diagnostic_sha256=lineage.helpers.sha(diagnostic.encode()))

    feedback_path = out / 'feedback.jsonl'
    with feedback_path.open('x') as stream:
        for record in records:
            stream.write(json.dumps(record, sort_keys=True) + '\n')
    dump(out / 'sany_results.json', results)
    receipt = dict(schema=1, complete=True, kind='sany_feedback_collection',
                   dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
                   eval_rows_never_decoded=True, eval_rows_never_train=True,
                   input_sha256=INPUT_SHA,
                   base_admission_sha256=lineage.helpers.file_sha(a.base_admission),
                   admission_sha256=lineage.helpers.file_sha(a.admission),
                   policy_checkpoint_sha256=lineage.helpers.file_sha(a.checkpoint),
                   model_files=lineage.helpers.model_files(a.model_path),
                   sany_identity=current,
                   feedback_sha256=lineage.helpers.file_sha(feedback_path),
                   results_sha256=lineage.helpers.file_sha(out / 'sany_results.json'),
                   records=len(records), elapsed_seconds=time.monotonic() - started,
                   training_authorized=False, gate_claim=False,
                   generalization_claim=False, proof_claim=False,
                   tlc_claim=False, nonvacuity_claim=False)
    dump(out / 'receipt.json', receipt)
    return receipt


def _prompt_only(tokenizer, prompt):
    rendered = tokenizer.apply_chat_template([dict(role='user', content=prompt)],
                                             tokenize=False, add_generation_prompt=True)
    ids = tokenizer(rendered, add_special_tokens=False, truncation=False)['input_ids']
    if not ids:
        raise ValueError('empty repair prompt')
    return dict(input_ids=ids, prompt_tokens=len(ids), rendered_prompt=rendered)


def admit_training(a):
    """Admit one append-only repair run only after collection authentication."""
    chosen, _ = selected(a.input.read_bytes())
    scaffold = load(a.scaffold)
    if scaffold != admit(a.input, a.base_admission):
        raise ValueError('scaffold admission drift')
    collection_receipt, records = load_feedback(a.feedback)
    if collection_receipt['admission_sha256'] != lineage.helpers.file_sha(a.scaffold):
        raise ValueError('feedback does not bind exact scaffold admission')
    if collection_receipt['policy_checkpoint_sha256'] != lineage.helpers.file_sha(a.checkpoint):
        raise ValueError('feedback does not bind frozen four-row checkpoint')
    prior = validate_eval_receipt(a.eval_receipt)
    return dict(schema=1, kind='sany_feedback_repair_worker', algorithm=REPAIR_ALGORITHM,
        budget=BUDGET, dev_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
        input_sha256=INPUT_SHA, scaffold_sha256=lineage.helpers.file_sha(a.scaffold),
        feedback_receipt_sha256=lineage.helpers.file_sha(Path(a.feedback) / 'receipt.json'),
        feedback_sha256=collection_receipt['feedback_sha256'],
        policy_checkpoint_sha256=lineage.helpers.file_sha(a.checkpoint),
        eval_receipt_sha256=prior['receipt_sha256'], eval_row47_feedback=prior,
        eval_rows_never_train=True, feedback_targets_immutable=True,
        training_authorized=True, gate_claim=False, generalization_claim=False,
        proof_claim=False, tlc_claim=False, nonvacuity_claim=False)


def repair_worker(a):
    """Train feedback-conditioned dev examples, then run protected evaluation."""
    import torch, transformers
    frozen = load(a.admission)
    if admit_training(a) != frozen:
        raise ValueError('worker admission mismatch')
    if a.output.exists():
        raise ValueError('append-only output already exists')
    out = Path(a.output); out.mkdir(parents=True, exist_ok=False)
    dump(out / 'admission.json', frozen)
    chosen, packet = selected(a.input.read_bytes())
    _, records = load_feedback(a.feedback)
    prior47 = frozen['eval_row47_feedback']
    tasks = {i: multi.stage_task(multi.checker_task(packet, chosen[i][0]), out, str(i))
             for i in (*DEV_ROWS, *EVAL_ROWS)}
    current = multi.sany.identity(list(tasks.values()))
    tokenizer = transformers.AutoTokenizer.from_pretrained(str(a.model_path), local_files_only=True)
    net = lineage.helpers.load_policy(str(a.model_path))
    saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    selected_t = lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(a.model_path))
    initial = {n: p.detach().cpu().clone() for n, p in selected_t.items()}
    # Restore the immutable checkpoint first, then unfreeze only the audited
    # final layer; all other parameters remain frozen for the causal update.
    selected_t = lineage.helpers.select_final_layer(net, True)
    repair_enc = repair_encodings(tokenizer, chosen, records)
    original = {i: chosen[i][1] for i in (*DEV_ROWS, *EVAL_ROWS)}
    # The actual prompt used to train is also the only prompt used to decode
    # row47; target reference text is never part of the generated prefix.
    pre = {str(i): multi.teacher(net, repair_enc[i])[1] for i in DEV_ROWS}
    opt, steps = multi.update(net, selected_t, [repair_enc[i] for i in DEV_ROWS])
    post_train = {str(i): multi.teacher(net, repair_enc[i])[1] for i in DEV_ROWS}
    repair_prefix47 = _prompt_only(tokenizer, eval_feedback_prompt(
        chosen[47][0]['prompt'], prior47['draft'], prior47['diagnostic']))
    ordinary_prefix107 = _prompt_only(tokenizer, chosen[107][0]['prompt'])
    post = {'47': multi.decode(net, tokenizer, repair_prefix47,
                               forced_prefix='---- MODULE ' + MODULE_NAMES[47] + ' ----\n'),
            '107': multi.decode(net, tokenizer, ordinary_prefix107,
                                forced_prefix='---- MODULE ' + MODULE_NAMES[107] + ' ----\n')}
    candidate = {}
    for i in EVAL_ROWS:
        candidate[str(i)] = (multi.sany.check(tasks[i], post[str(i)]['raw_reply'],
                              out / 'sany_candidate' / str(i), current,
                              timeout=BUDGET['sany_seconds'])
                             if post[str(i)]['finish_reason'] == 'eos' else None)
    # Retain immutable reference SANY evidence for every protected task and
    # the repaired candidate, but make no TLC/TLAPS/non-vacuity assertion.
    reference = {str(i): multi.sany.check(tasks[i], chosen[i][0]['response'],
                             out / 'sany_reference' / str(i), current,
                             timeout=BUDGET['sany_seconds']) for i in EVAL_ROWS}
    delta = sum(float((p.detach().cpu() - initial[n]).double().square().sum())
                for n, p in selected_t.items()) ** .5
    config = dict(frozen, model_files=lineage.helpers.model_files(a.model_path),
                  dtype_profile=lineage.helpers.PROFILE, repair_encodings=repair_enc,
                  algorithm=REPAIR_ALGORITHM)
    saved_info = lineage.helpers.save_reload(
        net, selected_t, opt, initial, config, steps,
        repair_enc[DEV_ROWS[0]]['input_ids'][:64], out / 'policy_optimizer.pt', 'cuda')
    receipt = dict(schema=1, complete=True, kind='sany_feedback_repair_runtime',
                   algorithm=REPAIR_ALGORITHM, updates=len(steps), parameter_delta_l2=delta,
                   before_teacher=pre, after_teacher=post_train, steps=steps,
                   post=post, candidate=candidate, reference=reference,
                   train_rows=list(DEV_ROWS), eval_rows=list(EVAL_ROWS),
                   feedback_draft_sha256={str(i): records[i]['draft_sha256'] for i in DEV_ROWS},
                   eval_row47_feedback=prior47,
                   candidate_sany_pass={i: bool(candidate[str(i)] and candidate[str(i)].get('sany') == 1)
                                       for i in EVAL_ROWS},
                   reference_sany_pass={i: reference[str(i)].get('sany') == 1 for i in EVAL_ROWS},
                   reload=saved_info, train_only=False, gate_claim=False,
                   generalization_claim=False, proof_claim=False, tlc_claim=False,
                   nonvacuity_claim=False)
    dump(out / 'steps.json', steps); dump(out / 'receipt.json', receipt)
    return receipt


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode', choices=('admit', 'collect', 'repair-admit', 'repair-worker'))
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--base-admission', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--admission', type=Path)
    p.add_argument('--model-path', type=Path)
    p.add_argument('--checkpoint', type=Path)
    p.add_argument('--scaffold', type=Path)
    p.add_argument('--feedback', type=Path)
    p.add_argument('--eval-receipt', type=Path)
    a = p.parse_args()
    if a.mode == 'admit':
        if a.output.exists(): raise ValueError('append-only output already exists')
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(admit(a.input, a.base_admission), indent=2) + '\n')
    elif a.mode == 'collect':
        if a.admission is None or a.model_path is None or a.checkpoint is None:
            p.error('collect requires --admission, --model-path, and --checkpoint')
        print(json.dumps(collect(a), sort_keys=True))
    elif a.mode == 'repair-admit':
        for value in (a.scaffold, a.feedback, a.eval_receipt, a.checkpoint):
            if value is None: p.error('repair-admit requires scaffold, feedback, eval-receipt, checkpoint')
        if a.output.exists(): raise ValueError('Admission output must not exist')
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(admit_training(a), indent=2) + '\n')
    else:
        for value in (a.admission, a.scaffold, a.feedback, a.eval_receipt, a.checkpoint, a.model_path):
            if value is None: p.error('repair-worker requires admission, scaffold, feedback, eval-receipt, checkpoint, model-path')
        print(json.dumps(repair_worker(a), sort_keys=True))


if __name__ == '__main__': main()
