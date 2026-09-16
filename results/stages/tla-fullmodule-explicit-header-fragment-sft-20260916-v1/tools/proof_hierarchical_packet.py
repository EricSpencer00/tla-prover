#!/usr/bin/env python3
"""Prepare the frozen17 TRAIN repair spans; no checker, model, or GPU execution.

The six leaf and eleven hierarchical spans overlap within three source families.
This is not seventeen independent theorems or whole-target proof generation.
"""
import argparse
import json
from pathlib import Path
import re
import os
import subprocess
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.corpora import normalize_tla, normalized_hash, shingle_set
from harness.proof_fragment_check import classify_result, validate_fragment
from tools.proof_cuda_train import ALGORITHM, sha, file_sha, dump
from tools.proof_family_manifest import comparison, named_goals
from tools.proof_original18 import REPOSITORY, EVAL_PATH, MODULES, git_blob, public_rows
from tools.proof_repair_pilot import prompt_for, with_dependency_context
from tools.proof_sequence_train import training_tasks
from harness import runner
from harness.proof_fragment_check import certify_fragment

MANIFEST_SHA = 'c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344'
REFERENCE_PATH = 'outputs/hf_publish/chattla-tla-prover-corpora-v1/data/traces/tlaps_verified_autoprover_traces_v1.jsonl'
THRESHOLD = .65


def runtime_identity():
    """Conservative complete library/backend inventory, not inferred version names.

    Includes every available library so transitive/INSTANCE imports are covered.
    Backend files include Isabelle heaps, wrappers and executable dependencies
    bundled with TLAPS. System dynamic libraries are outside this attestation.
    """
    tlapm=Path(runner.TLAPM).resolve()
    library_roots=[Path(p).resolve() for p in runner.TLA_LIBRARY.split(':')]
    backend_root=tlapm.parent.parent/'lib/tlapm/backends'
    libraries=sorted({p.resolve() for root in library_roots for p in root.rglob('*.tla') if p.is_file()})
    backends=sorted({p.resolve() for p in backend_root.rglob('*') if p.is_file()})
    if not libraries or not backends:
        raise ValueError('Complete installed verifier library/backend inventory required')
    config=subprocess.run([str(tlapm),'--config'],capture_output=True,text=True,timeout=30,check=True)
    sources=[ROOT/p for p in ('tools/proof_hierarchical_packet.py','harness/proof_fragment_check.py',
                             'harness/runner.py')]
    effective_paths=set(re.findall(r"PATH='([^']+)'",config.stdout))
    if len(effective_paths)!=1:
        raise ValueError('Unambiguous configured backend PATH required')
    effective_path=effective_paths.pop()
    executables={}
    for name in ('z3','zenon','isabelle','ls4','ptl_to_trp','cvc4','yices','veriT','SPASS','zipperposition'):
        found=shutil.which(name,path=effective_path)
        executables[name]=None if found is None else dict(path=str(Path(found).resolve()),sha256=file_sha(found))
    return dict(schema_version=1,tlapm_path=str(tlapm),tlapm_sha256=file_sha(tlapm),
        library_roots=list(map(str,library_roots)),
        library_inventory_sha256={str(p):file_sha(p) for p in libraries},
        backend_inventory_sha256={str(p):file_sha(p) for p in backends},
        resolved_backend_executables=executables,effective_backend_path=effective_path,
        checker_source_sha256={str(p):file_sha(p) for p in sources},
        config_stdout=config.stdout,config_stderr=config.stderr,
        path_environment=os.environ.get('PATH',''),
        scope='Full configured library and bundled backend inventory; system dynamic libraries not attested')


def validate_identity(path, controls_path, manifest_sha, current=None):
    evidence=json.loads(path.read_text())
    if (evidence.get('complete') is not True or evidence.get('manifest_sha256')!=manifest_sha or
            evidence.get('controls_sha256')!=file_sha(controls_path) or
            evidence.get('requested_controls')!=34 or evidence.get('completed_controls')!=34):
        raise ValueError('Complete exact fresh17 verifier identity required')
    actual=runtime_identity() if current is None else current
    if evidence.get('before')!=actual or evidence.get('after')!=actual:
        raise ValueError('Verifier identity changed since fresh controls')
    rows=json.loads(controls_path.read_text())
    if (len(rows)!=34 or len({r['id'] for r in rows})!=17 or
            {(r['id'],r['control']) for r in rows}!=
            {(r['id'],label) for r in rows for label in ('reference','omitted')}):
        raise ValueError('Exact34 fresh control rows required')
    for row in rows:
        if row['control']=='reference' and Path(row['command'][0]).resolve()!=Path(actual['tlapm_path']).resolve():
            raise ValueError('Control did not invoke attested tlapm')
    return evidence


def fresh_controls(manifest_path, output, timeout=30, seconds=600,
                   checker=certify_fragment, identity=runtime_identity, clock=time.monotonic):
    if not 0<timeout<=30 or not 0<seconds<=600:
        raise ValueError('Maximum30 seconds/check and600 seconds total')
    raw=manifest_path.read_bytes()
    if sha(raw)!=MANIFEST_SHA:
        raise ValueError('Only exact frozen17 manifest supported')
    tasks=training_tasks(json.loads(raw)); task_sources(tasks)
    if len(tasks)!=17:
        raise ValueError('Exact17 training spans required')
    output.mkdir(parents=True,exist_ok=False)
    started=clock(); before=identity(); rows=[]
    config=dict(manifest_sha256=sha(raw),requested_controls=34,timeout=timeout,seconds=seconds,
                hypothesis='Exact frozen17 human restoration remains strictly provable on current verifier',
                stop='34 controls or600-second wall budget, per-process-group deadlines; no training')
    dump(output/'config.json',config)
    dump(output/'verifier_before.json',before)
    complete=False
    try:
        for task in tasks:
            for label,fragment,expected in [('reference',task['reference_fragment'],True),('omitted','OMITTED',False)]:
                remaining=seconds-(clock()-started)
                if remaining<1:
                    raise TimeoutError('Fresh control total wall budget exhausted')
                row=checker(task['prefix'],fragment,task['suffix'],theorem_name=task['theorem_name'],
                    dependencies=tuple(map(Path,task.get('dependencies',[]))),
                    work_root=output/'controls'/task['id']/label,timeout=min(timeout,remaining))
                row.update(id=task['id'],control=label,expected=expected)
                rows.append(row); dump(output/'controls.json',rows)
            check_control(task,rows[-2],rows[-1])
        after=identity()
        if before!=after:
            raise ValueError('Verifier identity changed during controls')
        complete=True
        dump(output/'verifier_identity.json',dict(**config,complete=True,completed_controls=len(rows),
             before=before,after=after,controls_sha256=file_sha(output/'controls.json')))
    finally:
        dump(output/'summary.json',dict(**config,completed_controls=len(rows),complete=complete,
             elapsed_seconds=clock()-started,training_executed=False))
    return rows


def checked_text(path, expected):
    data = Path(path).read_bytes()
    if sha(data) != expected:
        raise ValueError('Source/dependency artifact changed: '+str(path))
    return data.decode()


def check_control(task, good, bad):
    """Reclassify raw logs and bind on-disk candidate and input bytes, no execution."""
    assembled = task['prefix']+task['reference_fragment']+task['suffix']
    expected = sha(assembled.encode())
    if expected != task['assembled_sha256']:
        raise ValueError('Assembled training hash mismatch')
    validate_fragment(task['prefix'], task['reference_fragment'], task['suffix'], task['theorem_name'])
    if (not good.get('certified') or good.get('returncode') != 0 or
            good.get('timed_out') is not False or good.get('sha256') != expected or
            good.get('status') != 'pass' or good.get('expected') is not True or
            not {'--strict','--nofp'}.issubset(good.get('command', []))):
        raise ValueError('Strict uncached positive control required: '+task['id'])
    status, proved, total = classify_result(good['returncode'], good['output'], good['timed_out'])
    if status != 'pass' or not proved == total > 0 or (proved,total) != (good['proved'],good['total']):
        raise ValueError('Positive raw log does not prove all obligations')
    candidate = Path(good['candidate_path'])
    checked_text(candidate, expected)
    work = Path(good['workdir'])
    if candidate.resolve().parent != work.resolve() or good['command'][-1] != candidate.name:
        raise ValueError('Control workdir/command mismatch')
    if (work/'tlapm.log').read_text() != good['output']:
        raise ValueError('Raw control log changed')
    inp = json.loads((work/'input.json').read_text())
    if inp != {k:task[k] for k in ('prefix','suffix','theorem_name')} | {'fragment':task['reference_fragment']}:
        raise ValueError('Control input scaffold/response mismatch')
    dependencies = {Path(p).name:h for p,h in task.get('dependency_sha256',{}).items()}
    if good.get('dependency_sha256') != dependencies:
        raise ValueError('Controlled dependency hashes mismatch')
    for name, digest in dependencies.items():
        checked_text(work/name, digest)
    omitted = sha((task['prefix']+'OMITTED'+task['suffix']).encode())
    if (bad.get('certified') is not False or bad.get('expected') is not False or
            bad.get('status') != 'contract_reject' or bad.get('sha256') != omitted):
        raise ValueError('Exact omitted negative control required')
    bad_input = json.loads((Path(bad['workdir'])/'input.json').read_text())
    if bad_input != {k:task[k] for k in ('prefix','suffix','theorem_name')} | {'fragment':'OMITTED'}:
        raise ValueError('Omitted control input mismatch')
    return dict(id=task['id'], proved=proved, total=total, assembled_sha256=expected,
                candidate_sha256=file_sha(candidate), log_sha256=file_sha(work/'tlapm.log'),
                input_sha256=file_sha(work/'input.json'), command=good['command'])


def task_sources(tasks):
    sources, goals = {}, {}
    for task in tasks:
        sources['source:'+task['source_path']] = checked_text(task['source_path'],task['source_sha256'])
        for path in task.get('dependencies',[]):
            sources['dependency:'+path] = checked_text(path,task['dependency_sha256'][path])
        assembled = task['prefix']+task['reference_fragment']+task['suffix']
        if sha(assembled.encode()) != task['assembled_sha256']:
            raise ValueError('Assembled source changed')
        sources['assembled:'+task['id']] = assembled
        goals[task['id']] = task.get('target_goal') or named_goals(assembled)[-1]
    return sources,goals


def compare_population(train_sources, train_goals, sources, goals):
    """Compare every source/dependency/assembled context and target goal anew."""
    if not sources or not goals:
        raise ValueError('Nonempty exclusion source and goal pools required')
    pool = [(n,shingle_set(normalize_tla(s))) for n,s in sources.items()]
    goal_pool = [(n,shingle_set(normalize_tla(s))) for n,s in goals.items()]
    source_rows = {n:comparison(s,pool) for n,s in train_sources.items()}
    goal_rows = {n:comparison(s,goal_pool) for n,s in train_goals.items()}
    exact = [(a,b) for a,s in train_sources.items() for b,t in sources.items()
             if normalized_hash(s)==normalized_hash(t)]
    exact_goals = [(a,b) for a,s in train_goals.items() for b,t in goals.items()
                   if normalized_hash(s)==normalized_hash(t)]
    maximum = max(r['max_jaccard'] for r in [*source_rows.values(),*goal_rows.values()])
    if exact or exact_goals or maximum >= THRESHOLD:
        raise ValueError('Training/evaluation lexical overlap detected')
    return dict(source_comparisons=source_rows,goal_comparisons=goal_rows,
                max_jaccard=maximum,canonical_matches=len(exact)+len(exact_goals),
                source_sha256={n:sha(s.encode()) for n,s in sources.items()},
                goal_sha256={n:sha(s.encode()) for n,s in goals.items()})


def exclusion_evidence(manifest, train, repository):
    ts,tg = task_sources(train)
    populations = {}; comparisons = {}
    for kind,path in [('official119',ROOT/'corpus/lmgpa/manifest.json'),
                      ('official30',ROOT/'corpus/holdout_30.json')]:
        if file_sha(path)!=manifest[kind+'_manifest_sha256']:
            raise ValueError('Official population manifest changed')
    for kind,count in [('official119',119),('official30',30)]:
        entries = [e for e in manifest['official_sources'] if e['id'].startswith(kind+':')]
        if len(entries)!=count or len({e['id'] for e in entries})!=count:
            raise ValueError('Full unique official population required')
        sources = {e['id']:checked_text(e['path'],e['sha256']) for e in entries}
        goals = {n+':'+str(i):g for n,s in sources.items() for i,g in enumerate(named_goals(s))}
        comparisons[kind] = compare_population(ts,tg,sources,goals)
        populations[kind] = [e['id'] for e in entries]
    dev = [t for t in manifest['tasks'] if t['split']=='development']
    if len(dev)!=4:
        raise ValueError('Frozen four-task development population required')
    ds,dg = task_sources(dev)
    comparisons['development'] = compare_population(ts,tg,ds,dg)
    populations['development'] = [t['id'] for t in dev]
    # Archived assistant answers are inspected only here for exclusions. Neither
    # references nor original prompts are forwarded into exported TRAIN rows.
    raw = git_blob(repository,EVAL_PATH)
    public = public_rows(raw)
    reference_raw = git_blob(repository,REFERENCE_PATH)
    references = {r['module']:r['proof_module'] for r in map(json.loads,reference_raw.splitlines())}
    if set(references)!=set(MODULES) or len(references)!=18:
        raise ValueError('Original18 reference population mismatch')
    originals = {}
    for row in public:
        blocks=re.findall(r'```tla\r?\n(.*?)\r?\n```',row['messages'][1]['content'],re.S)
        if len(blocks)!=1:
            raise ValueError('Original18 exact TLA prompt block required')
        originals[row['module']+':prompt']=blocks[0]
    originals.update({n+':reference':s for n,s in references.items()})
    og = {n+':'+str(i):g for n,s in references.items() for i,g in enumerate(named_goals(s))}
    comparisons['original18'] = compare_population(ts,tg,originals,og)
    populations['original18'] = MODULES
    return dict(populations=populations,comparisons=comparisons,threshold=THRESHOLD,
                canonical_matches=0,max_jaccard=max(c['max_jaccard'] for c in comparisons.values()),
                original18_eval_sha256=sha(raw),original18_reference_blob_sha256=sha(reference_raw),
                original18_reference_text_exported=False,
                pretraining_caveat='Local lexical source/goal exclusion only; unknown pretraining not certified')


def prepare(manifest_path, controls_path, output, repository=REPOSITORY, verifier_identity=None,
            require_training_ready=False):
    raw=manifest_path.read_bytes()
    if sha(raw)!=MANIFEST_SHA:
        raise ValueError('Only exact frozen17 manifest supported')
    manifest=json.loads(raw); train=training_tasks(manifest)
    if len(train)!=17 or len({t['source_family'] for t in train})!=3:
        raise ValueError('Exact17 spans in three families required')
    controls_raw=controls_path.read_bytes(); controls=json.loads(controls_raw)
    pairs={}
    for row in controls:
        key=row['id'],row['control']
        if key in pairs:
            raise ValueError('Duplicate control row')
        pairs[key]=row
    verified=[]; rows=[]
    for task in train:
        try:
            verified.append(check_control(task,pairs[task['id'],'reference'],pairs[task['id'],'omitted']))
        except KeyError as exc:
            raise ValueError('Missing reference/omitted controls for '+task['id']) from exc
        prompt=prompt_for(with_dependency_context(task)); response=task['reference_fragment']
        rows.append(dict(id=task['id'],split='train',source_family=task['source_family'],
            source_sha256=task['source_sha256'],assembled_sha256=task['assembled_sha256'],
            prompt=prompt,prompt_sha256=sha(prompt.encode()),response=response,response_sha256=sha(response.encode())))
    evidence=exclusion_evidence(manifest,train,repository)
    fresh=None
    if verifier_identity is not None:
        fresh=validate_identity(verifier_identity,controls_path,sha(raw))
    if require_training_ready and fresh is None:
        raise ValueError('Training-ready packet requires fresh verifier identity')
    evidence.update(manifest_sha256=sha(raw),controls_sha256=sha(controls_raw),strict_controls_verified=True,
                    controls=verified,verifier_identity=fresh,
                    verifier_identity_sha256=file_sha(verifier_identity) if fresh else None)
    packet=dict(schema_version=1,packet_kind='frozen17_hierarchical_repair_spans',
        algorithm=ALGORITHM,split='train',manifest_sha256=sha(raw),evidence=evidence,
        training_ready=fresh is not None,
        task_shape=dict(train_spans=17,leaf_spans=6,hierarchical_spans=11,source_families=3,
                        independent_theorem_count_claimed=False,whole_target_generation=False),
        evaluation_responses_exported=False,train_ids=[r['id'] for r in rows],rows=rows)
    output.mkdir(parents=True,exist_ok=False)
    dump(output/'train.json',packet)
    dump(output/'summary.json',dict(train_tasks=17,training_executed=False,checker_executed=False,
         training_ready=fresh is not None,
         train_packet_sha256=file_sha(output/'train.json'),task_shape=packet['task_shape'],
         cuda_trainer_compatible=False,limitation='Current CUDA trainer intentionally requires50 leaf rows; explicit generalization required'))
    return packet


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh-controls',action='store_true')
    parser.add_argument('--manifest',type=Path,required=True)
    parser.add_argument('--controls',type=Path)
    parser.add_argument('--verifier-identity',type=Path)
    parser.add_argument('--require-training-ready',action='store_true')
    parser.add_argument('--timeout',type=float,default=30)
    parser.add_argument('--seconds',type=float,default=600)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--repository',type=Path,default=REPOSITORY)
    args=parser.parse_args()
    if args.fresh_controls:
        rows=fresh_controls(args.manifest,args.output,args.timeout,args.seconds)
        print(json.dumps(dict(completed_controls=len(rows),training_executed=False)))
        return
    if args.controls is None:
        parser.error('--controls required for packet preparation')
    packet=prepare(args.manifest,args.controls,args.output,args.repository,args.verifier_identity,args.require_training_ready)
    print(json.dumps(dict(train_tasks=len(packet['rows']),max_jaccard=packet['evidence']['max_jaccard'],training_executed=False)))


if __name__=='__main__':
    main()
