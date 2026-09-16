#!/usr/bin/env python3
"""Freeze and evaluate the ORIGINAL18 whole-target type-invariance benchmark.

This is evaluation only. Candidate construction never receives assistant answers.
The original119 evaluator remains separate and its denominator is unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.proof_fragment_check import _code, certify_fragment, validate_fragment
from harness.runner import TLA_LIBRARY
from tools.proof_fact_search import libraries, proposals
from tools.proof_official_extension import source_aware_candidates

REPOSITORY = Path('/Users/eric/GitHub/ChatTLA/ChatTLA')
COMMIT = 'fd1fd3671ca62940c78210f7125a0a42c4a1a857'
EVAL_PATH = 'data/processed/prover_eval.jsonl'
EVAL_SHA = '2a0e846e5ff7cfd1c4fae282a9ae1a64e8b3f677dac27fe32379dd839c710357'
MODULES = ('AtomicCommit AtomicRegister ByzantineQuorum CircuitBreaker DistributedLock '
           'EventCount HeartbeatFailureDetector IdempotencyKey LeaderLease ResourceLease '
           'RetryWithBackoff RoundRobinScheduler SleepingBarber SzymanskiMutex TokenRing '
           'TwoPhaseLockingDeadlock VotingMajority WitnessReplication').split()
TARGET = 'ChatTLA_TypeOKSafety'
SCOPE = 'Original18 type-invariance theorem extension; not intended protocol safety, not leaf repair'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def git_blob(repository, path):
    return subprocess.check_output(['git', '-C', str(repository), 'show', COMMIT+':'+path], timeout=30)


def public_rows(raw):
    if sha(raw) != EVAL_SHA:
        raise ValueError('Original18 eval Git blob hash mismatch')
    records = [json.loads(line) for line in raw.splitlines() if line.strip()]
    if [r.get('_module') for r in records] != MODULES:
        raise ValueError('Original18 exact ordered population required')
    # Explicit allowlist: references never leave this loader.
    clean = []
    for row in records:
        messages = [{'role':m['role'], 'content':m['content']} for m in row['messages']
                    if m['role'] in ('developer', 'user')]
        if [m['role'] for m in messages] != ['developer', 'user']:
            raise ValueError('Original18 developer/user prompt contract mismatch')
        clean.append(dict(module=row['_module'], messages=messages))
    return clean


def build_task(row):
    user = row['messages'][1]['content']
    blocks = list(re.finditer(r'```tla\r?\n(.*?)\r?\n```', user, re.S))
    if len(blocks) != 1:
        raise ValueError('Exactly one original TLA prompt block required')
    prefix = blocks[0][1]  # preserve exact text and string literals
    code = _code(prefix)
    targets = list(re.finditer(r'(?m)^THEOREM\s+'+TARGET+r'\s*==', code))
    if len(targets) != 1 or re.search(r'(?m)^={4,}', code):
        raise ValueError('Original18 named target/module boundary mismatch')
    goal = prefix[targets[0].end():].strip()
    goal_code = code[targets[0].end():].strip()
    if re.search(r'\b(?:PROOF|BY|OBVIOUS|OMITTED|THEOREM|LEMMA)\b|<\d+>', goal_code):
        raise ValueError('Original18 target must be bare final theorem')
    if not re.search(r'(?:^|\bPROVE\s+)Spec\s*=>\s*\[\]TypeOK\s*$', goal_code):
        raise ValueError('Original18 frozen TypeOK goal required')
    suffix = '\n====\n'
    module = validate_fragment(prefix, '\nBY SMT', suffix, TARGET)
    if module != row['module']:
        raise ValueError('Original18 module identity mismatch')
    paths = libraries(prefix, [], TLA_LIBRARY.split(':'))
    library_texts = [path.read_text() for path in paths]
    candidates, context = proposals(prefix, TARGET, goal, [], library_texts)
    candidates, smt = source_aware_candidates(candidates, [prefix, *library_texts])
    return dict(id=row['module'], module_name=module, theorem_name=TARGET,
                split='original18_test', task_kind='whole_target_proof_extension',
                human_target_skeleton=False, prefix=prefix, suffix=suffix,
                target_goal=goal, source_sha256=sha(prefix.encode()),
                assembled_unproved_sha256=sha((prefix+suffix).encode()),
                source_identity='Exact TLA block in commit-bound original user message',
                insertion_scaffolding='Candidate starts with newline; suffix is newline + ==== + newline',
                messages=row['messages'], prompt_sha256=sha(user.encode()),
                dependencies=[], dependency_sha256={}, smt_visible=smt,
                symbolic_candidates=candidates, retrieval=context,
                candidate_family='source-scoped single-leaf BY/DEF; no human or induction skeleton',
                library_sha256={str(p.resolve()):sha(p.read_bytes()) for p in paths})


def provenance(repository):
    return dict(repository=str(repository.resolve()), commit=COMMIT, eval_path=EVAL_PATH,
                eval_sha256=EVAL_SHA,
                baseline_artifact='outputs/prover_diagnose_stage0_161622.json',
                baseline_parse=3, baseline_any_proved=0, baseline_requested=18,
                baseline_checkpoint='checkpoint-200 on EricSpencer00/chattla-20b',
                baseline_budget=dict(greedy=True, max_new_tokens=1024, verification_seconds=60),
                comparison_limit='Candidate search is not matched-budget free generation; strict full certification differs from legacy any-obligation metric',
                pretraining_caveat='Local training exclusion is not proof of absence from unknown base-model pretraining')


def overlap_audit(repository, tasks):
    """Isolated reference-content audit; never return reference text or proposals."""
    from harness.corpora import normalize_tla, shingle_set, normalized_hash
    from tools.proof_family_manifest import comparison, named_goals
    path = 'outputs/hf_publish/chattla-tla-prover-corpora-v1/data/traces/tlaps_verified_autoprover_traces_v1.jsonl'
    raw = git_blob(repository, path)
    traces = {r['module']:r['proof_module'] for r in map(json.loads, raw.splitlines())}
    if set(traces) != set(MODULES):
        raise ValueError('Original18 reference-audit population mismatch')
    sets = {}
    manifests = [('train6','proof-training-cycle-20260905-v1/manifest.json'),
                 ('train17','proof-multistep-manifest-20260905-v2/manifest.json'),
                 ('train50','proof-leaf-manifest-20260905-v1/defs-complete/manifest.json')]
    hashes = {}
    for label, relative in manifests:
        manifest = ROOT/'results/runs'/relative
        data = manifest.read_bytes(); hashes[str(manifest)] = sha(data)
        sources, goals = {}, {}
        for t in json.loads(data)['tasks']:
            if t['split'] != 'train':
                continue
            for name in [t['source_path'], *t.get('dependencies', [])]:
                content = Path(name).read_bytes()
                expected = t['source_sha256'] if name == t['source_path'] else t['dependency_sha256'][name]
                if sha(content) != expected:
                    raise ValueError('Training audit source changed: '+name)
                sources['source:'+name] = content.decode()
            assembled = t['prefix']+t['reference_fragment']+t['suffix']
            sources['assembled:'+t['id']] = assembled
            goals[t['id']] = t.get('target_goal') or named_goals(assembled)[-1]
        sets[label] = sources, goals
    official_path = ROOT/'corpus/lmgpa/manifest.json'
    data = official_path.read_bytes(); hashes[str(official_path)] = sha(data)
    sources = {}
    for entry in json.loads(data):
        content = (Path('/Users/eric/GitHub/lmgpa')/entry['module_file']).read_bytes()
        if sha(content) != entry['sha256']:
            raise ValueError('Official119 audit source changed')
        sources[entry['id']] = content.decode()
    sets['official119'] = sources, {n+':'+str(i):g for n,s in sources.items() for i,g in enumerate(named_goals(s))}
    results = {}
    for label, (sources, goals) in sets.items():
        pool = [(n,shingle_set(normalize_tla(s))) for n,s in sources.items()]
        goal_pool = [(n,shingle_set(normalize_tla(s))) for n,s in goals.items()]
        rows = []
        for task in tasks:
            name = task['id']; original = traces[name]
            rows.append(dict(id=name, prompt=comparison(task['prefix'], pool),
                original_reference_module=comparison(original, pool),
                named_goal=comparison(named_goals(task['prefix'])[-1], goal_pool),
                canonical_exact_matches=[n for n,s in sources.items() if normalized_hash(s) in
                                         (normalized_hash(task['prefix']), normalized_hash(original))]))
        results[label] = rows
    return dict(reference_audit_only=True, reference_text_exported=False, training=False,
                reference_blob_path=path, reference_blob_sha256=sha(raw),
                manifest_hashes=hashes, threshold=.65, comparisons=results,
                caveat='Lexical exclusion, not semantic equivalence or unknown pretraining certification')


def prepare(repository, output, audit=True):
    tasks = [build_task(row) for row in public_rows(git_blob(repository, EVAL_PATH))]
    payload = dict(schema_version=1, requested_tasks=18, scope=SCOPE, training=False,
                   reference_fragments_used=False, reference_answers_exported=False,
                   provenance=provenance(repository), tasks=tasks)
    evidence = overlap_audit(repository, tasks) if audit else None
    output.mkdir(parents=True, exist_ok=False)
    dump(output/'manifest.json', payload)
    if evidence is not None:
        dump(output/'decontamination.json', evidence)
    (output/'builder.py').write_bytes(Path(__file__).read_bytes())
    return payload


def validate_manifest(manifest):
    repository = Path(manifest['provenance']['repository'])
    if manifest['provenance'] != provenance(repository):
        raise ValueError('Original18 provenance mismatch')
    if (manifest.get('requested_tasks') != 18 or manifest.get('training') is not False or
            manifest.get('reference_fragments_used') is not False or
            manifest.get('reference_answers_exported') is not False or manifest.get('scope') != SCOPE):
        raise ValueError('Original18 evaluation contract mismatch')
    expected = [build_task(row) for row in public_rows(git_blob(repository, EVAL_PATH))]
    if manifest['tasks'] != expected:
        raise ValueError('Original18 source/target/candidates/library reconstruction mismatch')
    return expected


def summary(tasks, rows, statuses):
    passed = {r['task'] for r in rows if r['certified']}
    attempted = {r['task'] for r in rows}
    return dict(requested_tasks=18, attempted_tasks=len(attempted),
                unattempted_tasks=18-len(attempted), certified_tasks=len(passed),
                first_choice_certified=sum(r['certified'] and r['attempt']==0 for r in rows),
                attempts=len(rows), task_statuses=statuses,
                scope=SCOPE, model_used=False, model_updates=0)


def evaluate(manifest_path, output, attempts=4, timeout=5, seconds=360, checker=certify_fragment):
    if not (1 <= attempts <= 4 and 0 < timeout <= 5 and 0 < seconds <= 360):
        raise ValueError('Maximum budget: 4 candidates/task, 5 seconds/check, 360 seconds total')
    raw = manifest_path.read_bytes(); manifest = json.loads(raw)
    tasks = validate_manifest(manifest)
    output.mkdir(parents=True, exist_ok=False)
    (output/'manifest.json').write_bytes(raw)
    config = dict(manifest_sha256=sha(raw), attempts_per_task=attempts, timeout_per_check=timeout,
                  seconds=seconds, training=False, reference_fragments_used=False,
                  hypothesis='Source-scoped symbolic BY candidates close some original TypeOK targets',
                  stop='Fixed round-robin candidate and verification wall budgets; retain all18',
                  provenance=manifest['provenance'])
    paths = [Path(__file__), ROOT/'harness/proof_fragment_check.py', ROOT/'harness/runner.py',
             ROOT/'tools/proof_fact_search.py', ROOT/'tools/proof_premise_search.py',
             ROOT/'tools/proof_source_scope.py', ROOT/'tools/proof_official_extension.py']
    config['implementation_sha256'] = {str(p.relative_to(ROOT)):sha(p.read_bytes()) for p in paths}
    dump(output/'config.json', config)
    rows = []; statuses = {t['id']:'unattempted_budget' for t in tasks}; start = time.monotonic()
    def persist():
        result = dict(**summary(tasks, rows, statuses), elapsed_seconds=time.monotonic()-start, **config)
        dump(output/'summary.json', result)
        return result
    persist()
    with (output/'rows.jsonl').open('x') as stream:
        for attempt in range(attempts):
            for task in tasks:
                if statuses[task['id']] == 'certified' or attempt >= len(task['symbolic_candidates']):
                    continue
                if time.monotonic()-start > seconds-timeout:
                    return persist()
                fragment = '\n'+task['symbolic_candidates'][attempt]
                row = checker(task['prefix'], fragment, task['suffix'], theorem_name=TARGET,
                              work_root=output/'checks'/task['id']/str(attempt), timeout=timeout)
                row.update(task=task['id'], attempt=attempt, fragment=fragment,
                           source_sha256=task['source_sha256'])
                rows.append(row); stream.write(json.dumps(row)+'\n'); stream.flush()
                statuses[task['id']] = 'certified' if row['certified'] else row['status']
                persist()
    return persist()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    p = sub.add_parser('prepare'); p.add_argument('--repository', type=Path, default=REPOSITORY)
    p.add_argument('--output', type=Path, required=True)
    p = sub.add_parser('symbolic'); p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--attempts', type=int, default=4); p.add_argument('--timeout', type=float, default=5)
    p.add_argument('--seconds', type=float, default=360)
    a = parser.parse_args()
    if a.mode == 'prepare':
        result = prepare(a.repository, a.output)
        print(json.dumps(dict(prepared=len(result['tasks']), reference_answers_exported=False)))
    else:
        print(json.dumps(evaluate(a.manifest, a.output, a.attempts, a.timeout, a.seconds)))


if __name__ == '__main__':
    main()
