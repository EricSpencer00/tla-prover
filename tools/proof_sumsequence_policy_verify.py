"""Matched BASE/current-child TRAIN4 strict verification; never a holdout claim."""
import argparse
import json
import re
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import proof_sumsequence_policy_eval as policy
from tools import proof_sumsequence_packet as packet
from tools import proof_token_rl_stochastic_tlaps as stochastic
from tools.proof_fenced_extract import extract, _target_identity
from tools.proof_cuda_eval import digest, sha, dump
from tools.proof_cuda_train import file_sha
from harness.proof_owned_process import as_runner_tuple

SOURCES = tuple(sorted(set(policy.SOURCES + stochastic.SOURCES) | {
    'tools/proof_sumsequence_policy_verify.py', 'tools/proof_fenced_extract.py',
    'harness/proof_fragment_check.py', 'harness/runner.py',
    'tools/proof_sumsequence_controls.py', 'tools/proof_sumsequence_lemma2a.py',
    'tools/proof_sumsequence_lemma3.py', 'tools/proof_sumsequence_exclusions.py',
    'tools/proof_sumsequence_extended_exclusions.py'}))
ARMS = ('base', 'child')
MAX_SECONDS = 300


def load(path):
    return json.loads(Path(path).read_bytes())


def extraction_context(task):
    """Adapt exact packet metadata, never rewrite the target or model reply."""
    statement = task['statement']
    match = re.match(r'\A\s*(?:THEOREM|LEMMA)\s+' + re.escape(task['theorem_name']) + r'\s*==', statement)
    if match is None or not task['prefix'].endswith(statement):
        raise ValueError('Exact task statement/prefix binding required before extraction')
    context = dict(task, target_goal=statement[match.end():].strip())
    _target_identity(context)  # Metadata failures are infrastructure errors, not model rejections.
    return context


def identity(a, tasks):
    import transformers
    import torch
    import psutil
    from tools.proof_hierarchical_packet import runtime_identity
    from tools import proof_sumsequence_controls as controls
    from tools import proof_sumsequence_lemma2a as second
    from tools import proof_sumsequence_lemma3 as third
    runtime = runtime_identity()
    packet.audit_controls(tasks, runtime)
    paths = [a.prompts, a.checkpoint]
    paths += sorted(p for p in a.tokenizer_path.iterdir() if p.is_file())
    paths += sorted(p for p in a.generations.rglob('*') if p.is_file())
    return dict(runtime=runtime, local_decoder_runtime=dict(python=sys.version,
        transformers=transformers.__version__,torch=torch.__version__,psutil=psutil.__version__),
        control_sources=dict(base=controls.file_identity(),
        second=second.identity(), third=third.identity()),
        sources={n:file_sha(ROOT/n) for n in SOURCES},
        inputs={str(p.resolve()):file_sha(p) for p in paths}, tasks_sha256=digest(tasks))


def validate_process(process, arm, prompts_sha, remote_root, remote_checkpoint, remote_model):
    root=Path(remote_root)
    if not all(Path(p).is_absolute() for p in (remote_root,remote_checkpoint,remote_model)):
        raise ValueError('Observed canonical absolute remote paths required')
    expected=['/home/eric-spencer/ChatTLA/.venv/bin/python',
        str(root/'tools/proof_sumsequence_policy_eval.py'),'worker',
        '--prompts',str(root/'prompts.json'),'--expected-input-sha256',prompts_sha,
        '--model-path',remote_model,'--admission',str(root/'results'/arm/'admission.json'),
        '--output',str(root/'results'/arm)]
    if arm=='child':expected+=['--checkpoint',remote_checkpoint]
    if process['cwd'] != remote_root or process['command'] != expected:
        raise ValueError('Frozen generation process command/cwd mismatch')
    result=as_runner_tuple(process)
    if result[0]==0 and not result[3] and not 0 <= result[2] <= policy.BUDGET['seconds']:
        raise ValueError('Generation exceeded frozen process budget')
    return result


def prepare(a):
    import transformers
    exported, tasks = packet.export_tasks()  # Full local raw-control and exclusion admission.
    for task in tasks:
        extraction_context(task)
    raw, portable = policy.packet(a.prompts)
    if json.loads(raw) != exported or file_sha(a.checkpoint) != policy.CHILD_SHA:
        raise ValueError('Exact locally admitted packet and collected child required')
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.tokenizer_path, local_files_only=True)
    arms = {}
    batch = load(a.generations/'batch-summary.json')
    if batch.get('requested_samples') != 8 or batch.get('requested_per_arm') != 4:
        raise ValueError('Eight requested paired samples required')
    for arm in ARMS:
        root = a.generations/arm
        admission = load(root/'admission.json')
        if (admission['prompts_sha256'] != sha(raw)
            or admission['arm'] != ('base' if arm == 'base' else 'checkpoint')
            or admission['implementation_sha256'] != {n:file_sha(ROOT/n) for n in policy.SOURCES}):
            raise ValueError('Frozen actual generation source/arm/prompt identity required')
        expected_files = {n:h for n,h in admission['model_files'].items()
            if n.endswith('.json') or n in {'tokenizer.model','chat_template.jinja'}}
        actual_files = {p.name:file_sha(p) for p in a.tokenizer_path.iterdir()
            if p.is_file() and (p.suffix == '.json' or p.name in {'tokenizer.model','chat_template.jinja'})}
        if actual_files != expected_files:
            raise ValueError('Exact tokenizer artifact set/hash required')
        encoded = [policy.common.encode_prompt(tokenizer,t) for t in portable]
        if admission['input_evidence'] != encoded:
            raise ValueError('Frozen complete input evidence mismatch')
        ledger = (root/'generations.jsonl').read_bytes()
        if ledger and not ledger.endswith(b'\n'):
            raise ValueError('Incomplete raw generation ledger; no salvaged certification')
        rows = [json.loads(s) for s in ledger.splitlines()]
        policy.validate_rows(admission, rows)
        policy.validate_decoding(portable, rows, tokenizer)
        process = load(root/'process.json')
        rc, _, _, timeout = validate_process(process, arm, sha(raw), a.remote_root,
            a.remote_checkpoint_path,a.remote_model_path)
        summary = load(root/'summary.json')
        complete = rc == 0 and not timeout and len(rows) == 4
        if (summary.get('requested_tasks') != 4 or summary.get('accounted_rows') != len(rows)
            or summary.get('unattempted_ids') != list(packet.TRAIN_IDS[len(rows):])
            or summary.get('complete') is not complete
            or summary.get('returncode') != rc or summary.get('timed_out') != timeout
            or summary.get('optimizer_updates') != 0
            or summary.get('eos_completed') != sum(r['finish_reason']=='eos' for r in rows)
            or batch['per_arm'][arm]['summary'] != summary
            or batch['per_arm'][arm]['requested_ids'] != list(packet.TRAIN_IDS)):
            raise ValueError('Generation summary/process/denominator mismatch')
        runtime = load(root/'runtime.json') if (root/'runtime.json').exists() else None
        if complete and (not runtime or runtime.get('optimizer_updates') != 0
            or runtime.get('checkpoint_restored_exactly') is not (arm == 'child')
            or not 0 < runtime.get('reserved',0) <= policy.BUDGET['maximum_reserved_bytes']
            or not 0 < runtime.get('allocated',0) <= runtime['reserved']):
            raise ValueError('Actual no-update restore/memory evidence required')
        arms[arm] = dict(admission=admission, rows=rows, execution_complete=complete)
    return tasks, arms


def audit_result(task, fragment, result, work):
    process = load(work/'process.json')
    payload = load(work/'input.json')
    if process != result['process'] or payload != dict(task=task,fragment=fragment,timeout=28.5):
        raise ValueError('Raw isolated checker evidence mismatch')
    expected = [sys.executable,str(ROOT/'tools/proof_token_rl_stochastic_tlaps.py'),'worker',
        '--input',str(work/'input.json'),'--output',str(work/'worker')]
    if process['command'] != expected or Path(process['cwd']).resolve() != work:
        raise ValueError('Isolated checker command/cwd mismatch')
    rc, _, seconds, timed_out = as_runner_tuple(process)
    if result['seconds'] != seconds:
        raise ValueError('Checker elapsed evidence mismatch')
    if timed_out or rc != 0 or seconds > 30:
        if result['certified'] or result['measured_model_outcome'] or 'strict' in result:
            raise ValueError('Incomplete checker cannot certify or reject model')
    else:
        strict = load(work/'worker/result.json')
        diagnostic = stochastic.audit_strict(task,fragment,strict)
        if (strict != result['strict'] or result['classification'] != diagnostic['classification']
            or result['measured_model_outcome'] != diagnostic['measured_model_outcome']
            or result['certified'] != (diagnostic['classification']=='proof_success')):
            raise ValueError('Raw strict verdict mismatch')


def evaluate(a, *, checker=stochastic.check, clock=time.monotonic):
    a.output = a.output.resolve(); a.output.mkdir(parents=True,exist_ok=False)
    rows = [dict(arm=arm,task_id=task,certified=False,measured=False,status='unmeasured_pending',evidence=None)
        for arm in ARMS for task in packet.TRAIN_IDS]
    def save(complete=False):
        dump(a.output/'rows.json',rows)
        dump(a.output/'summary.json',dict(complete=complete,requested_samples=8,
            per_arm={arm:dict(requested_tasks=4,certified_tasks=sum(r['certified'] for r in rows if r['arm']==arm) if complete else 0,
                measured_outcomes=sum(r['measured'] for r in rows if r['arm']==arm),
                unknown_outcomes=sum(not r['measured'] for r in rows if r['arm']==arm)) for arm in ARMS},
            generalization_claim=False,optimizer_updates=0,
            scope='Greedy TRAIN4 pass@1, two separately reported frozen policies; not holdout or population-general reliability'))
    save()
    try:
        tasks,arms = prepare(a)
        before = identity(a,tasks); dump(a.output/'identity_before.json',before)
        frozen = digest(dict(tasks=tasks,arms=arms))
        dump(a.output/'config.json',dict(input_sha256=frozen,timeout=30,total_check_seconds=300,
            extraction='Unchanged proof_fenced_extract.extract; no repair/retry',
            process_budget='30-second outer owned deadline, 28.5-second inner timeout including 0.5-second cleanup reserve',
            generation_cap_and_timeout='Unmeasured; never passed to proof checker',
            remote_root=a.remote_root,remote_checkpoint_path=a.remote_checkpoint_path,
            remote_model_path=a.remote_model_path))
        started = clock()
        with (a.output/'events.jsonl').open('x') as stream:
            for index,r in enumerate(rows):
                arm = arms[r['arm']]; task = tasks[index % 4]
                generated = arm['rows'][index % 4] if index % 4 < len(arm['rows']) else None
                r['status'] = 'unmeasured_generation'
                if arm['execution_complete'] and generated and generated['finish_reason']=='eos':
                    extraction = extract(generated['raw_reply'],extraction_context(task))
                    r['extraction'] = extraction
                    if extraction['fragment'] is None:
                        r.update(status='model_extraction',measured=True)
                    elif clock()-started > MAX_SECONDS-30:
                        r['status']='unmeasured_budget'
                    else:
                        work=a.output/'checks'/r['arm']/task['id']
                        result=checker(task,extraction['fragment'],work,30)
                        audit_result(task,extraction['fragment'],result,work)
                        r.update(status=result['classification'],certified=result['certified'],
                            measured=result['measured_model_outcome'],evidence=result)
                stream.write(json.dumps(r)+'\n');stream.flush();save()
        after = identity(a,tasks); dump(a.output/'identity_after.json',after)
        exported_after,tasks_after = packet.export_tasks()
        if (after != before or tasks_after != tasks or digest(dict(tasks=tasks,arms=arms)) != frozen
            or json.loads(a.prompts.read_bytes()) != exported_after):
            raise ValueError('Raw input/control/runtime/source identity drift')
        save(True)
        return load(a.output/'summary.json')
    except BaseException as exc:
        save(False)
        dump(a.output/'failure.json',dict(error=type(exc).__name__+': '+str(exc),complete=False))
        raise


def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('prompts','generations','tokenizer-path','checkpoint','output'):
        p.add_argument('--'+name,type=Path,required=True)
    p.add_argument('--remote-root',required=True)
    p.add_argument('--remote-checkpoint-path',required=True)
    p.add_argument('--remote-model-path',required=True)
    print(json.dumps(evaluate(p.parse_args())))


if __name__ == '__main__':main()
