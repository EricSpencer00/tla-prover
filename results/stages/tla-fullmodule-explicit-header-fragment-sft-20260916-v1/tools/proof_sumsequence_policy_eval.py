"""Frozen TRAIN4 baseline generation; no optimizer and no proof-score claims."""
import argparse
import json
import os
from pathlib import Path
import sys

for _name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[_name] = '4'
os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_cuda_broader_eval as common
from tools.proof_cuda_eval import digest, sha, dump, read_rows
from tools.proof_cuda_train import file_sha
from harness.proof_owned_process import run_owned, as_runner_tuple

CHILD_SHA = 'f41f4a147b0fbc4cbd62ba87403d76516b4cd9da96fcc577979b033fa96b1a91'
BUDGET = dict(max_new_tokens=3072, max_tokens=8192, seconds=1000,
              max_time=180, seed=20260930, do_sample=False, requested_tasks=4,
              cpu_threads=4, maximum_reserved_bytes=36*1024**3)
SOURCES = ('tools/proof_sumsequence_policy_eval.py','tools/proof_sumsequence_policy_eval.pbs','tools/proof_sumsequence_packet.py',
    'tools/proof_cuda_broader_eval.py','tools/proof_cuda_eval.py','tools/proof_cuda_train.py',
    'harness/proof_owned_process.py','tools/proof_sequence_train.py',
    'tools/proof_broader_packet.py','tools/proof_whole_packet.py',
    'tools/proof_repair_pilot.py','tools/proof_candidate_rank.py')


def packet(path):
    from tools.proof_sumsequence_packet import validate_export
    raw = Path(path).read_bytes()
    return raw, validate_export(json.loads(raw))


def admit(prompts, expected_sha, model_path, checkpoint):
    from tools.proof_cuda_train import model_files, PROFILE
    import torch
    import transformers
    torch.set_num_threads(4)
    raw, tasks = packet(prompts)
    if sha(raw) != expected_sha:
        raise ValueError('Exact prompt packet hash required')
    files = model_files(Path(model_path))
    if (digest(files) != common.MODEL_FILES_SHA or common.runtime_versions() != common.FIRST_VERSIONS
        or PROFILE != common.BUDGET['profile']):
        raise ValueError('Frozen base model and runtime required')
    if checkpoint and file_sha(Path(checkpoint)) != CHILD_SHA:
        raise ValueError('Exact current child checkpoint required')
    eos = json.loads((Path(model_path)/'generation_config.json').read_bytes())['eos_token_id']
    if eos != common.EOS_IDS:
        raise ValueError('Frozen EOS required')
    tokenizer = transformers.AutoTokenizer.from_pretrained(model_path, local_files_only=True)
    encoded = [common.encode_prompt(tokenizer,t) for t in tasks]
    if any(r['status'] != 'ready' for r in encoded):
        raise ValueError('Full output/context budget required')
    return dict(budget=BUDGET, prompts_sha256=sha(raw), model_files=files,
        model_files_sha256=digest(files), versions=common.runtime_versions(),
        checkpoint_sha256=CHILD_SHA if checkpoint else None,
        arm='checkpoint' if checkpoint else 'base', eos_token_ids=eos,
        input_evidence=encoded, implementation_sha256={p:file_sha(ROOT/p) for p in SOURCES})


def validate_rows(admission, rows):
    if admission['budget'] != BUDGET or admission['eos_token_ids'] != common.EOS_IDS:
        raise ValueError('Frozen generation budget/EOS required')
    if (admission['versions'] != common.FIRST_VERSIONS
        or admission['model_files_sha256'] != common.MODEL_FILES_SHA
        or digest(admission['model_files']) != admission['model_files_sha256']
        or admission['arm'] not in ('base','checkpoint')
        or admission['checkpoint_sha256'] != (CHILD_SHA if admission['arm']=='checkpoint' else None)):
        raise ValueError('Frozen model/checkpoint identity required')
    inputs = admission['input_evidence']
    if len(inputs) != 4 or len(rows) > 4:
        raise ValueError('Four-task denominator required')
    if [r['id'] for r in inputs] != ['sumsequence-'+n for n in ('FrontDef','Lemma2','Lemma2a','Lemma3')]:
        raise ValueError('Exact ordered TRAIN4 required')
    for original, row in zip(inputs, rows):
        for key, value in original.items():
            if key != 'status' and row.get(key) != value:
                raise ValueError('Exact ordered input evidence required')
        tokens = row.get('token_ids')
        if not isinstance(tokens, list) or any(type(i) is not int or i < 0 for i in tokens):
            raise ValueError('Exact generated token IDs required')
        expected = common.output_fields(tokens, set(admission['eos_token_ids']), row['raw_reply'])
        if any(row.get(k) != v for k,v in expected.items()):
            raise ValueError('Output termination/hash evidence mismatch')


def validate_decoding(tasks, rows, tokenizer):
    for task,row in zip(tasks, rows):
        expected = common.encode_prompt(tokenizer, task)
        for key,value in expected.items():
            if key != 'status' and row.get(key) != value:
                raise ValueError('Tokenizer input reconstruction mismatch')
        if common.decode_reply(tokenizer,row['token_ids']) != row['raw_reply']:
            raise ValueError('Tokenizer output reconstruction mismatch')


def write_batch_summary(output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    ids = ['sumsequence-'+n for n in ('FrontDef','Lemma2','Lemma2a','Lemma3')]
    arms = {}
    for arm in ('base','child'):
        path = output/arm/'summary.json'
        summary = json.loads(path.read_bytes()) if path.exists() else None
        arms[arm] = dict(requested_ids=ids, summary=summary,
            status='reported' if summary is not None else 'unattempted',
            unattempted_ids=summary['unattempted_ids'] if summary else ids)
    dump(output/'batch-summary.json', dict(requested_samples=8, requested_per_arm=4,
        per_arm=arms, complete=all(a['summary'] and a['summary'].get('complete') for a in arms.values()),
        proof_verification_pending=True, optimizer_updates=0))


def worker(a):
    import torch
    import transformers
    from tools.proof_cuda_train import load_policy, restore_policy
    admission = json.loads(a.admission.read_bytes())
    current = admit(a.prompts, a.expected_input_sha256, a.model_path, a.checkpoint)
    if current != admission:
        raise ValueError('Worker admission changed')
    torch.manual_seed(BUDGET['seed'])
    torch.backends.cuda.matmul.allow_tf32 = False
    torch.cuda.reset_peak_memory_stats()
    net = load_policy(a.model_path, device='cuda')
    if a.checkpoint:
        saved = torch.load(a.checkpoint, map_location='cpu', weights_only=False)
        selected = restore_policy(net, saved, admission['model_files'])
        if not all(torch.equal(p.detach().cpu(), saved['trainable_state'][n]) for n,p in selected.items()):
            raise ValueError('Exact checkpoint restore failed')
        del saved
    net.eval()
    for p in net.parameters():
        p.requires_grad_(False)
    if net.generation_config.eos_token_id != common.EOS_IDS:
        raise ValueError('Loaded model EOS changed')
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    pad = tokenizer.pad_token_id if tokenizer.pad_token_id is not None else tokenizer.eos_token_id
    if type(pad) is not int:
        raise ValueError('Scalar padding token required')
    _, tasks = packet(a.prompts)
    with (a.output/'generations.jsonl').open('x') as stream:
        for task, frozen in zip(tasks, admission['input_evidence']):
            row = common.encode_prompt(tokenizer, task)
            if row != frozen:
                raise ValueError('Input reconstruction drift')
            inputs = torch.tensor([row['input_token_ids']], device='cuda')
            with torch.inference_mode(), torch.autocast('cuda', dtype=torch.bfloat16):
                output = net.generate(input_ids=inputs, attention_mask=torch.ones_like(inputs),
                    do_sample=False, num_beams=1, num_return_sequences=1,
                    max_new_tokens=3072, max_time=180, pad_token_id=pad)
            torch.cuda.synchronize()
            ids = common.trim_output(output[0, inputs.shape[1]:].tolist(), set(common.EOS_IDS))
            row.update(common.output_fields(ids, set(common.EOS_IDS), common.decode_reply(tokenizer, ids)))
            stream.write(json.dumps(row)+'\n'); stream.flush()
            runtime = dict(allocated=torch.cuda.max_memory_allocated(),
                reserved=torch.cuda.max_memory_reserved(), optimizer_updates=0,
                checkpoint_restored_exactly=bool(a.checkpoint))
            dump(a.output/'runtime.json', runtime)
            if runtime['reserved'] > BUDGET['maximum_reserved_bytes']:
                raise ValueError('Frozen memory guard exceeded')
    if admit(a.prompts,a.expected_input_sha256,a.model_path,a.checkpoint) != admission:
        raise ValueError('Post-generation provenance drift')


def generate(a):
    admission = json.loads(a.admission.read_bytes())
    if admit(a.prompts,a.expected_input_sha256,a.model_path,a.checkpoint) != admission:
        raise ValueError('Full pre-submission admission mismatch')
    a.output.mkdir(parents=True, exist_ok=False)
    dump(a.output/'admission.json', admission)
    all_ids = [r['id'] for r in admission['input_evidence']]
    initial = dict(complete=False, requested_tasks=4, accounted_rows=0,
        unattempted_ids=all_ids, proof_verification_pending=True, optimizer_updates=0,
        generalization_claim=False, status='worker_pending')
    dump(a.output/'summary.json', initial)
    command = [sys.executable,str(Path(__file__).resolve()),'worker',
        '--prompts',str(a.prompts.resolve()),'--expected-input-sha256',a.expected_input_sha256,
        '--model-path',str(a.model_path.resolve()),'--admission',str((a.output/'admission.json').resolve()),
        '--output',str(a.output.resolve())]
    if a.checkpoint:
        command += ['--checkpoint',str(a.checkpoint.resolve())]
    try:
        process = run_owned(command, ROOT, BUDGET['seconds'])
        dump(a.output/'process.json', process)
        rc, _, _, timeout = as_runner_tuple(process)
        rows = read_rows(a.output/'generations.jsonl')
        validate_rows(admission, rows)
    except BaseException as exc:
        dump(a.output/'failure.json', dict(error=type(exc).__name__+': '+str(exc)))
        dump(a.output/'summary.json', dict(initial,status='unmeasured_execution_or_ledger_error',
            note='Raw ledger retained; all four requested outcomes remain unverified'))
        raise
    complete = rc == 0 and not timeout and len(rows) == 4
    dump(a.output/'summary.json', dict(complete=complete, requested_tasks=4,
        accounted_rows=len(rows), unattempted_ids=[r['id'] for r in admission['input_evidence'][len(rows):]],
        eos_completed=sum(r['finish_reason']=='eos' for r in rows),
        proof_verification_pending=True, optimizer_updates=0, generalization_claim=False,
        returncode=rc, timed_out=timeout))
    if not complete:
        raise RuntimeError('Generation incomplete; preserve unknowns and raw process evidence')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['admit','generate','worker','account'])
    parser.add_argument('--expected-input-sha256', required=True)
    for name in ('prompts','model-path','checkpoint','admission','output'):
        parser.add_argument('--'+name, type=Path, required=name in ('prompts','model-path','output'))
    args = parser.parse_args()
    if args.mode == 'account':
        write_batch_summary(args.output)
    elif args.mode == 'admit':
        dump(args.output, admit(args.prompts,args.expected_input_sha256,args.model_path,args.checkpoint))
    else:
        if args.admission is None:
            parser.error('An actual saved admission is required')
        globals()[args.mode](args)
