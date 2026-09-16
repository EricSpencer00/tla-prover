"""Expanded six-row SANY-feedback repair worker.

This reuses the audited response-only worker while replacing its partition with
the independently admitted six-row corpus.  Rows 47 and 107 remain protected.
"""
import argparse, json
from pathlib import Path
from tools import proof_fullmodule_sany_feedback_repair_probe as repair
from tools import proof_fullmodule_sany_feedback_corpus_probe as corpus
from tools import proof_fullmodule_learning_train as lineage

repair.INPUT_SHA = corpus.INPUT_SHA
repair.DEV_ROWS = corpus.DEV_ROWS
repair.EVAL_ROWS = corpus.EVAL_ROWS
repair.ROW_IDS = corpus.ROW_IDS
repair.PROMPT_SHAS = corpus.PROMPT_SHAS
repair.RESPONSE_SHAS = corpus.RESPONSE_SHAS
repair.MODULE_NAMES = {i: f'W4Od{str(i)}' for i in corpus.ALL_ROWS}
repair.MODULE_NAMES.update({45:'W4Od18m9p1t2',46:'W4Od13m1p5t1',47:'W4Od2m7p4t2',
                            50:'W4Od10m2p0t3',51:'W4Od4m2p0t1',52:'W4Od19m7p2t1',
                            53:'W4Od12m7p3t1',107:'W4Od3m0p0t0'})
repair.BUDGET = dict(updates=128, lr=1e-5, max_new_tokens=1024, item_seconds=45,
                     sany_seconds=30, dev_rows=list(corpus.DEV_ROWS), eval_rows=list(corpus.EVAL_ROWS),
                     response_only=True, final_layer_only=True, training_authorized=True,
                     gate_claim=False, generalization_claim=False, proof_claim=False,
                     tlc_claim=False, nonvacuity_claim=False)
repair.REPAIR_ALGORITHM = 'response-only expanded six-row SANY-feedback structural repair v8; protected held-out eval'


def admit_training(a):
    chosen, _ = repair.selected(a.input.read_bytes())
    scaffold = json.loads(Path(a.scaffold).read_bytes())
    expected = corpus.admit(a.input, a.base_admission)
    if scaffold != expected:
        raise ValueError('corpus scaffold admission drift')
    collection_receipt, _ = corpus.load_feedback(a.feedback)
    if collection_receipt['admission_sha256'] != lineage.helpers.file_sha(a.scaffold):
        raise ValueError('feedback does not bind exact corpus scaffold')
    if collection_receipt['policy_checkpoint_sha256'] != lineage.helpers.file_sha(a.checkpoint):
        raise ValueError('feedback does not bind frozen checkpoint')
    prior = repair.validate_eval_receipt(a.eval_receipt)
    return dict(schema=1, kind='sany_feedback_corpus_worker', algorithm=repair.REPAIR_ALGORITHM,
                budget=repair.BUDGET, dev_rows=list(corpus.DEV_ROWS), eval_rows=list(corpus.EVAL_ROWS),
                input_sha256=corpus.INPUT_SHA, scaffold_sha256=lineage.helpers.file_sha(a.scaffold),
                feedback_receipt_sha256=lineage.helpers.file_sha(Path(a.feedback) / 'receipt.json'),
                feedback_sha256=collection_receipt['feedback_sha256'],
                policy_checkpoint_sha256=lineage.helpers.file_sha(a.checkpoint),
                eval_receipt_sha256=prior['receipt_sha256'], eval_row47_feedback=prior,
                eval_rows_never_train=True, feedback_targets_immutable=True,
                training_authorized=True, gate_claim=False, generalization_claim=False,
                proof_claim=False, tlc_claim=False, nonvacuity_claim=False)


repair.admit_training = admit_training
repair.load_feedback = corpus.load_feedback
repair.validate_feedback = corpus.validate_feedback


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=('repair-admit', 'repair-worker'))
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--base-admission', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--admission', type=Path)
    p.add_argument('--model-path', type=Path)
    p.add_argument('--checkpoint', type=Path)
    p.add_argument('--scaffold', type=Path, required=True)
    p.add_argument('--feedback', type=Path, required=True)
    p.add_argument('--eval-receipt', type=Path, required=True)
    a = p.parse_args()
    if a.mode == 'repair-admit':
        if a.output.exists(): raise ValueError('append-only output already exists')
        a.output.parent.mkdir(parents=True, exist_ok=True)
        a.output.write_text(json.dumps(admit_training(a), indent=2) + '\n')
    else:
        for value in (a.admission, a.model_path, a.checkpoint):
            if value is None: p.error('repair-worker requires --admission, --model-path, --checkpoint')
        print(json.dumps(repair.repair_worker(a), sort_keys=True))
