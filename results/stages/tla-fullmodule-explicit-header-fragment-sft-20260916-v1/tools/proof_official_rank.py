#!/usr/bin/env python3
"""Frozen FULL119 neural ranking of symbolic candidates; no training."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.proof_candidate_rank import encode_candidate, response_logps, rank_scores


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def freeze_tasks(manifest_path, candidate_limit=8):
    from tools.proof_official_extension import build_task, source_aware_candidates
    from tools.proof_fact_search import proposals, libraries
    from harness.runner import TLA_LIBRARY
    from harness.proof_fragment_check import validate_fragment
    if not 1 <= candidate_limit <= 8:
        raise ValueError('Candidate limit must be 1..8')
    manifest = json.loads(manifest_path.read_bytes())
    official_bytes = Path(manifest['official_manifest_path']).read_bytes()
    if sha(official_bytes) != manifest['official_manifest_sha256']:
        raise ValueError('Official manifest hash changed')
    official = json.loads(official_bytes)
    tasks = manifest['tasks']
    if len(tasks) != 119 or len(official) != 119 or len({e['id'] for e in official}) != 119:
        raise ValueError('Full119 official population required')
    if [t['id'] for t in tasks] != [e['id'] for e in official]:
        raise ValueError('Official119 ID order/membership mismatch')
    frozen = []
    for task, entry in zip(tasks, official):
        source = Path(task['source_path'])
        parts = Path(entry['module_file']).parts
        if source.parts[-len(parts):] != parts:
            raise ValueError('Official source path mismatch')
        derived = build_task(entry, source.parents[len(parts)-1])
        for key in ('official_id','category','source_sha256','theorem_name','prefix','suffix','target_goal','split','task_kind'):
            if task[key] != derived[key]:
                raise ValueError('Official source/target binding mismatch: '+key)
        if task.get('dependencies') or task.get('reference_fragment'):
            raise ValueError('Unexpected external dependencies or reference answer')
        paths = list(task['library_sha256'])
        resolved = [str(p.resolve()) for p in libraries(task['prefix'], [], TLA_LIBRARY.split(':'))]
        if paths != resolved:
            raise ValueError('Retrieval library paths are not the explicit imported library set')
        for path, expected in task['library_sha256'].items():
            if sha(Path(path).read_bytes()) != expected:
                raise ValueError('Imported library changed')
        library_texts = [Path(p).read_text() for p in paths]
        expected_candidates, actual_context = proposals(task['prefix'], task['theorem_name'], task['target_goal'], [],
                                                       library_texts)
        if manifest.get('source_aware_backends', False):
            expected_candidates, visible = source_aware_candidates(expected_candidates, [task['prefix'], *library_texts])
            if task.get('smt_visible') != visible:
                raise ValueError('Prepared backend visibility differs from source')
        if task['symbolic_candidates'] != expected_candidates:
            raise ValueError('Prepared candidate pool differs from deterministic source proposals')
        if actual_context != task['retrieval']:
            raise ValueError('Prepared statement context differs from visible source')
        context = dict(visible_facts=actual_context['visible_facts'],
                       imported_facts=actual_context['ranked_imported_facts'][:8])
        facts = context['visible_facts']+context['imported_facts']
        if any(f['name'] == task['theorem_name'] for f in facts):
            raise ValueError('Target self-citation in retrieval')
        candidates = ['\n'+c for c in task['symbolic_candidates'][:candidate_limit]]
        if not candidates or len(set(candidates)) != len(candidates):
            raise ValueError('Empty/duplicate candidate pool')
        for fragment in candidates:
            if re.search(r'\b'+re.escape(task['theorem_name'])+r'\b', fragment):
                raise ValueError('Candidate cites its own target theorem')
            validate_fragment(task['prefix'], fragment, task['suffix'], task['theorem_name'])
        prompt = ('Complete the missing TLA+ proof for the final named theorem. The theorem and all '
                  'existing declarations are immutable. Return only a valid TLAPS proof fragment; '
                  'do not introduce axioms, omit proofs, or repeat the module.\n\n'+task['prefix']+
                  '\n<PROOF_HOLE>'+task['suffix']+
                  '\n\nVisible statements and assumptions (cite names as facts, not definitions):\n'+
                  '\n'.join(f"{f['name']} == {f['statement']}" for f in facts))
        clean = {k:derived[k] for k in ('id','official_id','category','source_path','source_sha256',
                    'theorem_name','prefix','suffix','target_goal','split','task_kind')}
        clean.update(candidates=candidates, prompt=prompt, prompt_sha256=sha(prompt.encode()),
                     scoring_candidates=[c[1:] for c in candidates], insertion_separator='\n',
                     context=context, library_sha256=task['library_sha256'])
        frozen.append(clean)
    return frozen


def preflight_pool(tokenizer, task, max_tokens):
    encodings = []
    for index, candidate in enumerate(task['candidates']):
        try:
            # Encode without truncation so over-budget lengths are measured.
            # The newline is deterministic insertion scaffolding, not sampled
            # proof text: Qwen BPE merges it into the assistant-header newline
            # and would otherwise violate the exact prompt boundary contract.
            score_text = task.get('scoring_candidates', task['candidates'])[index]
            encoding = encode_candidate(tokenizer, task['prompt'], score_text, 10**9)
            encoding.update(candidate_fragment=candidate, scoring_text=score_text)
        except ValueError as exc:
            return encodings, 'preflight_encoding_error', str(exc)
        encodings.append(encoding)
    if any(len(e['input_ids']) > max_tokens for e in encodings):
        return encodings, 'preflight_context_budget', 'At least one candidate exceeds token budget; entire pool unranked'
    return encodings, 'ready', ''


def dispatch(tasks, rankings, limit=4):
    for rank in range(1, limit+1):
        for task in tasks:
            pool = rankings.get(task['id'], [])
            if len(pool) >= rank:
                yield task, rank, pool[rank-1]


def summary(tasks, statuses, rankings, checked):
    one = {r['task'] for r in checked if r['certified'] and r['rank']==1}
    four = {r['task'] for r in checked if r['certified']}
    attempted = {r['task'] for r in checked}
    return dict(requested_tasks=len(tasks), fully_scored_tasks=len(rankings),
                unranked_tasks=len(tasks)-len(rankings), top1_verified=len(one), top4_verified=len(four),
                checked_tasks=len(attempted), unchecked_tasks=len(tasks)-len(attempted),
                checker_attempts=len(checked), task_statuses=statuses,
                by_category={c:dict(requested=sum(t['category']==c for t in tasks),
                    fully_scored=sum(t['category']==c and t['id'] in rankings for t in tasks),
                    top1_verified=sum(t['category']==c and t['id'] in one for t in tasks),
                    top4_verified=sum(t['category']==c and t['id'] in four for t in tasks))
                    for c in sorted({t['category'] for t in tasks})},
                parameter_updates=0, reference_fragment_used=False,
                method='neural-ranked symbolic search; mean response logp including EOS; not free proof generation')


def worker(a):
    from harness.proof_fragment_check import certify_fragment
    from tools.proof_sequence_train import restore_trainable
    config = json.loads((a.output/'config.json').read_bytes())
    data = (a.output/'frozen.json').read_bytes()
    if sha(data) != config['frozen_sha256']:
        raise ValueError('Frozen task data changed')
    for path, expected in config['implementation_sha256'].items():
        if sha((ROOT/path).read_bytes()) != expected:
            raise ValueError('Implementation changed after freeze')
    if sha(a.manifest.read_bytes()) != config['manifest_sha256']:
        raise ValueError('Prepared manifest changed')
    tasks = json.loads(data)
    if tasks != freeze_tasks(a.manifest, a.candidates):
        raise ValueError('Frozen source/context changed')
    os.environ.update(HF_HUB_OFFLINE='1', TRANSFORMERS_OFFLINE='1', TOKENIZERS_PARALLELISM='false')
    import torch
    import transformers
    torch.set_num_threads(4)
    torch.manual_seed(20260912)
    started = time.monotonic()
    tokenizer = transformers.AutoTokenizer.from_pretrained(a.model_path, local_files_only=True)
    statuses, encoded, rankings, checked = {}, {}, {}, []
    for task in tasks:
        pool, status, reason = preflight_pool(tokenizer, task, a.max_tokens)
        encoded[task['id']] = pool
        statuses[task['id']] = dict(scoring=status, reason=reason, verification='unattempted')
    dump(a.output/'encodings.json', encoded)
    def save():
        dump(a.output/'rankings.json', rankings)
        dump(a.output/'summary.json', summary(tasks, statuses, rankings, checked))
    save()
    if a.preflight_only:
        return
    model_files = {p.name:sha(p.read_bytes()) for p in a.model_path.iterdir()
                   if p.is_file() and p.suffix in {'.json','.safetensors'}}
    if model_files != config['model_files']:
        raise ValueError('Base model changed after freeze')
    net = transformers.AutoModelForCausalLM.from_pretrained(a.model_path, local_files_only=True,
             torch_dtype=torch.float32).to(a.device).eval()
    net.requires_grad_(False)
    if a.resume:
        if sha(a.resume.read_bytes()) != config['checkpoint_sha256']:
            raise ValueError('Checkpoint changed after freeze')
        saved = torch.load(a.resume, map_location='cpu', weights_only=False)
        if saved['config']['model_files'] != model_files:
            raise ValueError('Checkpoint base identity mismatch')
        names = {id(p) for p in net.model.layers[-1].parameters()}
        restore_trainable({n:p for n,p in net.named_parameters() if id(p) in names}, saved)
    dump(a.output/'runtime.json', dict(torch=torch.__version__, transformers=transformers.__version__,
         device=a.device, dtype='float32', model_files=model_files, parameter_updates=0))
    with (a.output/'scores.jsonl').open('x') as stream:
        for task in tasks:
            key = task['id']
            if statuses[key]['scoring'] != 'ready':
                continue
            rows = []
            for index, encoding in enumerate(encoded[key]):
                if time.monotonic()-started >= a.score_seconds:
                    break
                with torch.inference_mode():
                    ids = torch.tensor([encoding['input_ids']], device=a.device)
                    logits = net(input_ids=ids, use_cache=False).logits[0]
                    score = response_logps(logits, encoding['labels'])
                    del logits, ids
                row = dict(task=key, candidate_index=index, fragment=task['candidates'][index], **score)
                rows.append(row)
                stream.write(json.dumps(row)+'\n'); stream.flush()
            if len(rows) == len(encoded[key]):
                rankings[key] = rank_scores(rows)
                statuses[key]['scoring'] = 'fully_scored'
            else:
                statuses[key]['scoring'] = 'incomplete_scoring_budget'
            save()
    scoring_elapsed = time.monotonic()-started
    del net
    if a.device == 'mps':
        torch.mps.empty_cache()
    check_start = time.monotonic()
    passed = set()
    with (a.output/'checks.jsonl').open('x') as stream:
        for task, rank, row in dispatch(tasks, rankings):
            if task['id'] in passed:
                continue
            if time.monotonic()-check_start > a.check_seconds-a.timeout:
                break
            result = certify_fragment(task['prefix'], row['fragment'], task['suffix'],
                theorem_name=task['theorem_name'], work_root=a.output/'checks'/task['id']/str(rank), timeout=a.timeout)
            result.update(task=task['id'], rank=rank, fragment=row['fragment'], candidate_index=row['candidate_index'])
            checked.append(result)
            stream.write(json.dumps(result)+'\n'); stream.flush()
            statuses[task['id']]['verification'] = result['status']
            if result['certified']:
                passed.add(task['id'])
            save()
    result = dict(**summary(tasks, statuses, rankings, checked), scoring_seconds=scoring_elapsed,
                  verification_seconds=time.monotonic()-check_start)
    dump(a.output/'summary.json', result)
    print(json.dumps(result), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('manifest','model-path','output'):
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--resume', type=Path)
    p.add_argument('--device', choices=['cpu','mps'], default='mps')
    p.add_argument('--candidates', type=int, default=8)
    p.add_argument('--max-tokens', type=int, default=8192)
    p.add_argument('--score-seconds', type=int, default=1200)
    p.add_argument('--check-seconds', type=int, default=900)
    p.add_argument('--timeout', type=int, default=5)
    p.add_argument('--preflight-only', action='store_true')
    p.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    a = p.parse_args()
    if not (1 <= a.candidates <= 8 and 128 <= a.max_tokens <= 8192 and
            1 <= a.timeout <= 5 and 1 <= a.score_seconds <= 1200 and 1 <= a.check_seconds <= 900):
        p.error('Budget limits:8 candidates,8192 tokens,1200 scoring seconds,900 verification seconds,5 seconds/check')
    a.output = a.output.resolve()
    a.model_path = a.model_path.resolve()
    if a.worker:
        worker(a)
        return
    tasks = freeze_tasks(a.manifest, a.candidates)
    a.output.mkdir(parents=True, exist_ok=False)
    dump(a.output/'frozen.json', tasks)
    dump(a.output/'config.json', dict(args={k:str(v) if isinstance(v,Path) else v for k,v in vars(a).items()},
         manifest_sha256=sha(a.manifest.read_bytes()), frozen_sha256=sha((a.output/'frozen.json').read_bytes()),
         checkpoint_sha256=sha(a.resume.read_bytes()) if a.resume else None,
         model_files={p.name:sha(p.read_bytes()) for p in a.model_path.iterdir()
                      if p.is_file() and p.suffix in {'.json','.safetensors'}},
         implementation_sha256={str(path.relative_to(ROOT)):sha(path.read_bytes()) for path in
             [Path(__file__).resolve(), ROOT/'tools/proof_candidate_rank.py', ROOT/'tools/proof_sequence_train.py',
              ROOT/'harness/proof_fragment_check.py', ROOT/'harness/runner.py', ROOT/'tools/proof_official_extension.py',
              ROOT/'tools/proof_fact_search.py', ROOT/'tools/proof_premise_search.py',
              ROOT/'tools/proof_source_scope.py']},
         hypothesis='Frozen learned weights improve official candidate order under matched pool and checker budgets',
         measurement='FULL119 top1/top4, protocol and math categories; mean conditional response logp with EOS',
         stop='Separate scoring/check budgets; context overflow and incomplete pools remain unranked',
         response_contract='Score proof body plus EOS; deterministic leading newline is insertion scaffolding, not a scored token',
         historical_contamination_flags={'2_TCommit':'Historical corpus195 trace overlap; legacy index unused; retained in119'},
         reference_fragment_used=False, legacy_retrieval_index_used=False, parameter_updates=0))
    (a.output/'tool.py').write_bytes(Path(__file__).read_bytes())
    from harness.runner import run_cmd
    command = [sys.executable,'-u',str(Path(__file__).resolve()),*sys.argv[1:],'--worker']
    code, output, elapsed, timed_out = run_cmd(command, ROOT, a.score_seconds+a.check_seconds+180)
    (a.output/'console.log').write_text(output)
    dump(a.output/'execution.json', dict(exit_code=code, elapsed_seconds=elapsed, timed_out=timed_out))
    print(output[-5000:])
    raise SystemExit(0 if code == 0 and not timed_out else 1)


if __name__ == '__main__':
    main()
