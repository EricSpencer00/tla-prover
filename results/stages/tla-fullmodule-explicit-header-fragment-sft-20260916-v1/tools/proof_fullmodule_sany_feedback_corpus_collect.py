"""Inference-only collector for the six-row expanded SANY feedback corpus."""
import argparse, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_learning_train as lineage
from tools import proof_fullmodule_multiexample_probe as multi
from tools import proof_fullmodule_sany_feedback_corpus_probe as corpus


def load(path):
    return json.loads(Path(path).read_bytes())


def diagnostic(result):
    text = (result.get('process') or {}).get('output')
    return text if isinstance(text, str) and text else 'SANY status: ' + str(result.get('status', 'unknown'))


def collect(a):
    import torch
    import transformers

    scaffold = load(a.admission)
    if scaffold != corpus.admit(a.input, a.base_admission):
        raise ValueError('Admission drift')
    if a.output.exists():
        raise ValueError('Append-only output already exists')
    out = Path(a.output)
    out.mkdir(parents=True, exist_ok=False)
    chosen, packet = corpus.selected(Path(a.input).read_bytes())
    tasks = {i: multi.stage_task(multi.checker_task(packet, chosen[i][0]), out, str(i))
             for i in corpus.DEV_ROWS}
    current = multi.sany.identity(list(tasks.values()))
    tokenizer = transformers.AutoTokenizer.from_pretrained(str(a.model_path), local_files_only=True)
    net = lineage.helpers.load_policy(str(a.model_path))
    saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    lineage.helpers.restore_policy(net, saved, lineage.helpers.model_files(a.model_path))
    del saved
    results, records = {}, []
    started = time.monotonic()
    for i in corpus.DEV_ROWS:
        draft = multi.decode(net, tokenizer, chosen[i][1])
        result = multi.sany.check(tasks[i], draft['raw_reply'], out / 'sany' / str(i), current,
                                  timeout=corpus.BUDGET['sany_seconds'])
        rec = dict(row=i, draft=draft['raw_reply'], diagnostic=diagnostic(result),
                   draft_sha256=lineage.helpers.sha(draft['raw_reply'].encode()))
        corpus.validate_feedback(rec)
        records.append(rec)
        results[str(i)] = dict(decode=draft, sany=result,
                               diagnostic_sha256=lineage.helpers.sha(rec['diagnostic'].encode()))
    stream = out / 'feedback.jsonl'
    with stream.open('x') as f:
        for rec in records:
            f.write(json.dumps(rec, sort_keys=True) + '\n')
    lineage.helpers.dump(out / 'sany_results.json', results)
    receipt = dict(schema=1, complete=True, kind='sany_feedback_collection',
                   dev_rows=list(corpus.DEV_ROWS), eval_rows=list(corpus.EVAL_ROWS),
                   eval_rows_never_decoded=True, eval_rows_never_train=True,
                   input_sha256=corpus.INPUT_SHA,
                   base_admission_sha256=lineage.helpers.file_sha(a.base_admission),
                   admission_sha256=lineage.helpers.file_sha(a.admission),
                   policy_checkpoint_sha256=lineage.helpers.file_sha(a.checkpoint),
                   model_files=lineage.helpers.model_files(a.model_path),
                   sany_identity=current, feedback_sha256=lineage.helpers.file_sha(stream),
                   results_sha256=lineage.helpers.file_sha(out / 'sany_results.json'),
                   records=len(records), elapsed_seconds=time.monotonic() - started,
                   training_authorized=False, gate_claim=False,
                   generalization_claim=False, proof_claim=False, tlc_claim=False,
                   nonvacuity_claim=False)
    lineage.helpers.dump(out / 'receipt.json', receipt)
    return receipt


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('mode', choices=('collect',))
    p.add_argument('--input', type=Path, required=True)
    p.add_argument('--base-admission', type=Path, required=True)
    p.add_argument('--admission', type=Path, required=True)
    p.add_argument('--checkpoint', type=Path, required=True)
    p.add_argument('--model-path', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    collect(a)
