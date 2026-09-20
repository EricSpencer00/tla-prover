"""Read-only decode-budget discriminator for the multi-example checkpoint."""
import argparse, json, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_fullmodule_multiexample_probe as multi
from tools import proof_fullmodule_sany_checks as sany
from tools import proof_fullmodule_learning_train as lineage

EVAL_ROWS = (47, 107)
PACKET_SHA = multi.INPUT_SHA
CHECKPOINT_SHA = 'a4d45777920eb2b12d71671afbc088ca037b0e2e8414e0d9e2553bf8b390257f'
# Descriptive alias used by the harness and downstream receipt readers.
CHILD_CHECKPOINT_SHA = CHECKPOINT_SHA
RECEIPT_SHA = 'ffc80e66cf58bddda7ff6bc0977e60abcf0eb36f221bb651852a472baccce480'
BUDGET = dict(max_new_tokens=4096, item_seconds=45, sany_seconds=30,
              train_only=False, gate_claim=False, generalization_claim=False,
              proof_claim=False, tlc_claim=False, nonvacuity_claim=False)

def sha(path): return lineage.helpers.file_sha(Path(path))
def dump(path, value): lineage.helpers.dump(Path(path), value)

def output_fields(tokens, reply, elapsed, *, max_new_tokens, item_seconds):
    tokens = list(tokens)
    eos = set(lineage.common.EOS_IDS)
    if not all(type(x) is int and 0 <= x < 128256 for x in tokens):
        raise ValueError('Invalid generated token IDs')
    finish = ('eos' if tokens and tokens[-1] in eos and elapsed <= item_seconds
              else 'token_limit' if len(tokens) >= max_new_tokens else 'time_limit')
    return dict(token_ids=tokens, raw_reply=reply,
                raw_reply_sha256=lineage.helpers.sha(reply.encode()),
                output_tokens=len(tokens), finish_reason=finish,
                deadline_exceeded=elapsed > item_seconds,
                elapsed_seconds=elapsed, max_new_tokens=max_new_tokens,
                item_seconds=item_seconds)


def decode(net, tokenizer, enc, *, max_new_tokens=None, item_seconds=None, device='cuda'):
    import torch
    max_new_tokens = BUDGET['max_new_tokens'] if max_new_tokens is None else max_new_tokens
    item_seconds = BUDGET['item_seconds'] if item_seconds is None else item_seconds
    ids = torch.tensor([enc['input_ids'][:enc['prompt_tokens']]], device=device)
    started = time.monotonic()
    with torch.inference_mode(), lineage.helpers.autocast(device):
        result = net.generate(input_ids=ids, attention_mask=torch.ones_like(ids),
            do_sample=False, num_beams=1, num_return_sequences=1,
            max_new_tokens=max_new_tokens, max_time=item_seconds,
            pad_token_id=tokenizer.pad_token_id or tokenizer.eos_token_id)
    if device == 'cuda': torch.cuda.synchronize()
    elapsed = time.monotonic() - started
    tokens = lineage.common.trim_output(result[0, ids.shape[1]:].tolist(), set(lineage.common.EOS_IDS))
    reply = lineage.common.decode_reply(tokenizer, tokens)
    return output_fields(tokens, reply, elapsed, max_new_tokens=max_new_tokens,
                         item_seconds=item_seconds)

def worker(a):
    if a.max_new_tokens not in (2048, 4096):
        raise ValueError('Probe budget must be exactly 2048 or 4096')
    import torch, transformers
    raw = a.input.read_bytes()
    chosen, packet = multi.selected(raw)
    if lineage.helpers.sha(raw) != PACKET_SHA: raise ValueError('Exact packet required')
    if sha(a.checkpoint) != CHECKPOINT_SHA: raise ValueError('Exact multi-example checkpoint required')
    if sha(a.multiexample_receipt) != RECEIPT_SHA: raise ValueError('Exact multi-example receipt required')
    out = a.output; out.mkdir(parents=True, exist_ok=False)
    dump(out / 'admission.json', dict(packet_sha256=PACKET_SHA, checkpoint_sha256=CHECKPOINT_SHA,
        receipt_sha256=RECEIPT_SHA, rows=list(EVAL_ROWS), budget=BUDGET))
    tasks = {}
    for i in EVAL_ROWS:
        tasks[i] = multi.stage_task(multi.checker_task(packet, chosen[i][0]), out, str(i))
    current = sany.identity(list(tasks.values()))
    model_dir = str(a.model_path)
    if not Path(model_dir).is_dir() or not (Path(model_dir) / 'config.json').is_file():
        raise FileNotFoundError(f'Model snapshot is not readable: {model_dir}')
    tokenizer = transformers.AutoTokenizer.from_pretrained(model_dir, local_files_only=True)
    net = lineage.helpers.load_policy(Path(model_dir))
    parent = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
    selected = lineage.helpers.restore_policy(net, parent, lineage.helpers.model_files(a.model_path))
    encs = {str(i): chosen[i][1] for i in EVAL_ROWS}
    budget = dict(BUDGET, max_new_tokens=a.max_new_tokens)
    post = {str(i): decode(net, tokenizer, encs[str(i)],
                           max_new_tokens=budget['max_new_tokens'],
                           item_seconds=budget['item_seconds']) for i in EVAL_ROWS}
    candidates = {str(i): (sany.check(tasks[i], post[str(i)]['raw_reply'], out / 'sany_candidate' / str(i), current, timeout=BUDGET['sany_seconds'])
                          if post[str(i)]['finish_reason'] == 'eos' else None) for i in EVAL_ROWS}
    receipt = dict(complete=True, rows=list(EVAL_ROWS), budget=budget, post=post, candidate=candidates,
                   parameter_updates=0,
                   candidate_sany_pass={str(i): bool(candidates[str(i)] and candidates[str(i)]['sany'] == 1) for i in EVAL_ROWS},
                   train_only=False, gate_claim=False, generalization_claim=False, proof_claim=False,
                   tlc_claim=False, nonvacuity_claim=False, identity=current)
    dump(out / 'receipt.json', receipt); return receipt

def main():
    p=argparse.ArgumentParser(); p.add_argument('mode', choices=('worker',))
    p.add_argument('--input', type=Path, required=True); p.add_argument('--model-path', type=Path, required=True)
    p.add_argument('--checkpoint', type=Path, required=True); p.add_argument('--multiexample-receipt', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--max-new-tokens', type=int, default=4096)
    a=p.parse_args(); print(json.dumps(worker(a)))
if __name__ == '__main__': main()
