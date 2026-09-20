#!/usr/bin/env python3
"""Freeze six exact whole-target TRAIN candidates; never silently shrink selection.

Selection is not training admission. Uses a separately versioned full-proof
contract; the legacy fragment contract remains unchanged. Exact source bytes
remain in selection.json even when a candidate is rejected.
"""
import argparse
import copy
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.corpora import normalize_tla, shingle_set, normalized_hash, jaccard
from harness.proof_full_fragment_check import certify_fragment, validate_fragment, CONTRACT_VERSION
from harness.runner import TLA_LIBRARY, TLAPM
from tools.proof_family_manifest import validate_split
from tools.proof_original18 import REPOSITORY, EVAL_PATH, git_blob, public_rows, MODULES
from tools.proof_source_scope import top_level_code, named_declarations

COMMIT = '47b0e2cc0268836b89f5ce451f38e5df5f1cf773'
EXAMPLES = ROOT/'tools/tlaplus-examples'
PARENT = ROOT/'results/runs/proof-multistep-manifest-20260905-v2/manifest.json'
PARENT_SHA = 'c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344'
HASHES = {
 'locks_auxiliary_vars/Lock.tla':'f10562642cb5d9cb6a3d3912d93917fa692a97ab9a879fa3b3f2c7989098765f',
 'barriers/Barriers.tla':'34883b1e21d7b3c3fb02e5343844fa29f8663f9e602da0b3fc3f50653abc68ee',
 'barriers/Barrier.tla':'e4a28b2900e3769602e700c3d474e5ac2147a1187ce80ef2f365a029abc5c220',
 'MisraReachability/ReachabilityProofs.tla':'7dc8f697765747cf4723139d3b79d9a883d90c15696bc68e2d53e9b1430a7a0c',
 'MisraReachability/Reachability.tla':'00d8f9751c26e8eb5fd542fa569b123ff6fb961e71325f4765887dc3b4d1dfae',
}
# One-based inclusive lines: declaration, first proof token line, final proof line.
# These explicit endpoints exclude comments introducing later declarations.
SELECTION = (
 ('locks_auxiliary_vars/Lock.tla','MutualExclusion',92,93,117),
 ('barriers/Barriers.tla','LockExclusion',268,269,322),
 ('MisraReachability/ReachabilityProofs.tla','Reachable0',23,30,67),
 ('MisraReachability/ReachabilityProofs.tla','Reachable1',86,94,252),
 ('MisraReachability/ReachabilityProofs.tla','Reachable2',258,262,304),
 ('MisraReachability/ReachabilityProofs.tla','Reachable3',310,311,311),
)
THRESHOLD = .65


def sha(data):
    return hashlib.sha256(data).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def imports(text):
    """Direct EXTENDS plus INSTANCE names; preserve INSTANCE source unchanged."""
    code = top_level_code(text)
    names = []
    pattern = r'(?m)^\s*EXTENDS\s+(\w+(?:[ \t]*,[ \t\r\n]*\w+)*)'
    for match in re.finditer(pattern, code):
        names.extend(re.findall(r'\w+', match[1]))
    names.extend(re.findall(r'\bINSTANCE\s+(\w+)', code))
    return list(dict.fromkeys(names))


def check_dependency(text):
    code = top_level_code(text)
    if re.search(r'\b(?:THEOREM|LEMMA|COROLLARY|PROPOSITION|AXIOM|OMITTED)\b', code):
        raise ValueError('custom dependency contains theorem declaration or admission')
    # ASSUME parameter constraints are recorded, never promoted to proved facts.
    return [line.strip() for line in code.splitlines() if re.match(r'\s*ASSUME\b', line)]


def checked_source(relative):
    path = EXAMPLES/'specifications'/relative
    data = path.read_bytes()
    if sha(data) != HASHES[relative]:
        raise ValueError('frozen source hash changed: '+relative)
    blob = subprocess.check_output(['git','-C',str(EXAMPLES),'show',
                                   COMMIT+':specifications/'+relative], timeout=30)
    if blob != data:
        raise ValueError('source differs from pinned commit: '+relative)
    return path, data.decode()


def closure(path, text):
    deps, standard, visiting = {}, {}, set()
    def visit(current, content):
        for name in imports(content):
            local = current.parent/(name+'.tla')
            if local.is_file():
                rel = str(local.relative_to(EXAMPLES/'specifications'))
                if rel not in HASHES:
                    raise ValueError('unfrozen custom dependency: '+rel)
                actual, raw = checked_source(rel)
                assumptions = check_dependency(raw)
                if str(actual) in visiting:
                    raise ValueError('cyclic custom dependency')
                if str(actual) not in deps:
                    visiting.add(str(actual)); visit(actual, raw); visiting.remove(str(actual))
                    deps[str(actual)] = dict(sha256=sha(raw.encode()), assumptions=assumptions)
            else:
                found = next((Path(d)/(name+'.tla') for d in TLA_LIBRARY.split(':')
                              if (Path(d)/(name+'.tla')).is_file()), None)
                if found is None and name in {'Naturals','Integers','Reals','Sequences'}:
                    standard['tlapm-builtin:'+name] = sha(Path(TLAPM).read_bytes())
                    continue
                if found is None:
                    raise ValueError('unresolved dependency: '+name)
                standard[str(found.resolve())] = sha(found.read_bytes())
    visit(path, text)
    return deps, standard


def goal_bodies(text):
    """Scope-aware goal extraction; labels excluded, literal bytes preserved.

    A conservative lexical boundary, not a full parser. Stops at any declaration,
    including unnamed theorems, then the first actual proof keyword/step.
    """
    code = top_level_code(text)
    all_starts = [m.start() for m in re.finditer(
        r'(?m)^\s*(?:THEOREM|LEMMA|AXIOM|COROLLARY|PROPOSITION)\b', code)]
    goals = []
    for d in named_declarations(text):
        if d.kind not in ('THEOREM','LEMMA'):
            continue
        end = next((x for x in all_starts if x > d.body_start), len(code))
        match = re.search(r'(?m)^\s*(?:PROOF\b|BY\b|OBVIOUS\b|OMITTED\b|<\d+>)',
                          code[d.body_start:end])
        if match:
            end = d.body_start+match.start()
        body = text[d.body_start:end].strip()
        if body:
            goals.append((d.name, body))
    return goals


def extract(text, theorem, begin, proof, end):
    lines = text.splitlines(keepends=True)
    start = sum(map(len, lines[:proof-1]))
    finish = sum(map(len, lines[:end]))
    declaration = sum(map(len, lines[:begin-1]))
    code = top_level_code(text)
    ds = [d for d in named_declarations(text) if d.name == theorem]
    if len(ds) != 1 or not declaration <= ds[0].start <= declaration+len(lines[begin-1]):
        raise ValueError('frozen target declaration boundary mismatch')
    if not re.match(r'\s*(?:<1>|BY\b|PROOF\b)', code[start:finish]):
        raise ValueError('frozen proof start mismatch')
    body_start = ds[0].body_start
    if re.search(r'(?m)^\s*(?:THEOREM|LEMMA|COROLLARY|PROPOSITION)\b', code[start:finish]):
        raise ValueError('proof boundary contains another target')
    # Exact original substring, including comments/indentation/trailing newline.
    prefix, reference, suffix = text[:start], text[start:finish], '\n====\n'
    reason = None
    try:
        validate_fragment(prefix, reference, suffix, theorem)
    except ValueError as exc:
        reason = str(exc)
    return dict(prefix=prefix,reference_fragment=reference,suffix=suffix,
                target_goal=text[body_start:start].strip(),
                goal_offsets=[body_start,start],proof_offsets=[start,finish],
                source_theorem_lines=[begin,end],source_fragment_lines=[proof,end],
                assembled_sha256=sha((prefix+reference+suffix).encode()),
                contract_rejection=reason,fragment_contract=CONTRACT_VERSION)


@lru_cache(maxsize=4096)
def comparison_key(text):
    return shingle_set(normalize_tla(text)), normalized_hash(text)


def compare(text, population):
    tokens, digest = comparison_key(text)
    ranked = [(jaccard(tokens,comparison_key(value)[0]), ident)
              for ident,value in population]
    score, nearest = max(ranked, default=(0.0,None))
    exact = [ident for ident,value in population if digest==comparison_key(value)[1]]
    return dict(max_jaccard=score,nearest=nearest,exact_normalized=exact)


def exclusions(parent):
    sources, provenance = [], {}
    for row in parent['official_sources']:
        path = Path(row['path']); raw = path.read_bytes()
        if sha(raw) != row['sha256']:
            raise ValueError('exclusion source hash changed: '+str(path))
        sources.append((row['id'],raw.decode())); provenance[str(path)] = sha(raw)
    dev = [copy.deepcopy(t) for t in parent['tasks'] if t['split']=='development']
    if len(dev)!=4:
        raise ValueError('exact four development tasks required')
    for task in dev:
        for p in [task['source_path']]+task.get('dependencies',[]):
            path=Path(p);raw=path.read_bytes()
            expected=task['source_sha256'] if p==task['source_path'] else task['dependency_sha256'][p]
            if sha(raw)!=expected:
                raise ValueError('development source changed')
            sources.append(('DEV:'+p,raw.decode())); provenance[p]=sha(raw)
    raw=git_blob(REPOSITORY,EVAL_PATH)
    provenance['original18_public']=sha(raw)
    for row in public_rows(raw):
        block=re.search(r'```tla\r?\n(.*?)\r?\n```',row['messages'][1]['content'],re.S)
        if not block:
            raise ValueError('missing original18 source block')
        sources.append(('original18:'+row['module'],block[1]))
    reference_path='outputs/hf_publish/chattla-tla-prover-corpora-v1/data/traces/tlaps_verified_autoprover_traces_v1.jsonl'
    raw=git_blob(REPOSITORY,reference_path); provenance['original18_reference_audit']=sha(raw)
    refs=[json.loads(line) for line in raw.splitlines()]
    if {r['module'] for r in refs}!=set(MODULES) or len(refs)!=18:
        raise ValueError('exact original18 reference exclusion population required')
    sources.extend(('original18-reference:'+r['module'],r['proof_module']) for r in refs)
    # Neither reference text nor reference proof candidates leave this function.
    goals=[(ident+':'+name,body) for ident,text in sources for name,body in goal_bodies(text)]
    return sources,goals,provenance,dev


def construct():
    raw=PARENT.read_bytes()
    if sha(raw)!=PARENT_SHA:
        raise ValueError('frozen parent manifest changed')
    parent=json.loads(raw)
    sources,goals,provenance,dev=exclusions(parent)
    tasks=[]
    for relative,theorem,begin,proof,end in SELECTION:
        path,text=checked_source(relative); deps,standard=closure(path,text)
        task=extract(text,theorem,begin,proof,end)
        task.update(id='breadth-'+path.stem+'-'+theorem,module_name=path.stem,
            theorem_name=theorem,split='train',source_family='tlaplus/Examples:'+relative.split('/')[0],
            source_path=str(path),source_sha256=sha(text.encode()),source_commit=COMMIT,
            source_repository='https://github.com/tlaplus/Examples',dependencies=list(deps),
            dependency_sha256={p:r['sha256'] for p,r in deps.items()},dependency_audit=deps,
            standard_library_sha256=standard,task_kind='whole_target_proof_extension',
            transformation='Exact source prefix and proof substring; later material replaced by module terminator')
        checks={'source':compare(text,sources),
                'assembled':compare(task['prefix']+task['reference_fragment']+task['suffix'],sources),
                'goal_body':compare(task['target_goal'],goals)}
        checks.update({'dependency:'+p:compare(Path(p).read_text(),sources) for p in deps})
        task['decontamination']=checks
        task['context_goal_audit']={name:compare(body,goals) for name,body in goal_bodies(task['prefix'])
                                    if name!=theorem}
        task['context_overlap_disclosure']='Preceding human proofs remain; generic helper templates can overlap DEV/original18. Target-label removal is not semantic equivalence.'
        task['rejection_reasons']=([task['contract_rejection']] if task['contract_rejection'] else [])
        if any(r['max_jaccard']>=THRESHOLD or r['exact_normalized'] for r in checks.values()):
            task['rejection_reasons'].append('source/dependency/assembled/goal-body lexical overlap')
        tasks.append(task)
    validate_split(tasks+dev)
    return dict(schema_version=1,kind='breadth_whole_target_selection_only',tasks=tasks+dev,
                parent_manifest_sha256=PARENT_SHA,source_commit=COMMIT,
                official_sources=parent['official_sources'],exclusion_sha256=provenance,
                requested_train=6,development=4,admitted_train=0,
                rejected_train=sum(bool(t['rejection_reasons']) for t in tasks),
                control_eligible=sum(not t['rejection_reasons'] for t in tasks),
                training_authorized=False,fragment_contract=CONTRACT_VERSION,
                scope='New source families; lexical local exclusion only, not unknown-pretraining absence or gate evidence')


def wrong_conclusion(task):
    start,end=task['goal_offsets']
    # Control-only mutation; training task and source statement stay immutable.
    return task['prefix'][:start]+' FALSE\n'+task['prefix'][end:]


def control_identity():
    """Full runtime attestation, only on explicitly requested control execution."""
    from tools.proof_hierarchical_packet import runtime_identity
    result=runtime_identity()
    paths=[Path(__file__),ROOT/'harness/proof_full_fragment_check.py',
           ROOT/'tools/proof_source_scope.py',ROOT/'tools/proof_family_manifest.py',
           ROOT/'tools/proof_original18.py',ROOT/'harness/corpora.py']
    result['breadth_source_sha256']={str(p.resolve()):sha(p.read_bytes()) for p in paths}
    result['breadth_fragment_contract']=CONTRACT_VERSION
    return result


def controls(selection, output, seconds=480, timeout=30, checker=certify_fragment, identity=None):
    if not 0<seconds<=480 or not 0<timeout<=30:
        raise ValueError('maximum 480 seconds total, 30 seconds/control')
    started=time.monotonic(); rows=[]; admitted=[]
    identity=identity or control_identity
    before=identity(); dump(output/'verifier_before.json',before)
    train=[t for t in selection['tasks'] if t['split']=='train']
    for task in train:
        if task['rejection_reasons']:
            rows.append(dict(id=task['id'],status='selection_reject',reasons=task['rejection_reasons']))
            continue
        pair=[]
        for label,prefix in [('reference',task['prefix']),('wrong_conclusion',wrong_conclusion(task))]:
            remaining=seconds-(time.monotonic()-started)
            if remaining<1:
                rows.append(dict(id=task['id'],control=label,status='unmeasured_budget'))
                break
            result=checker(prefix,task['reference_fragment'],task['suffix'],
                theorem_name=task['theorem_name'],dependencies=tuple(map(Path,task['dependencies'])),
                work_root=output/'controls'/task['id']/label,timeout=min(timeout,remaining))
            row=dict(id=task['id'],control=label,**result);pair.append(row);rows.append(row)
            dump(output/'controls.json',rows)
        if len(pair)==2:
            good,bad=pair
            expected_deps={Path(p).name:value for p,value in task['dependency_sha256'].items()}
            provenance=all(r.get('contract_version')==CONTRACT_VERSION
                and r.get('dependency_sha256')==expected_deps
                and '--strict' in r.get('command',[]) and '--nofp' in r.get('command',[])
                for r in pair)
            provenance=provenance and good.get('sha256')==task['assembled_sha256']
            provenance=provenance and bad.get('sha256')==sha((wrong_conclusion(task)+task['reference_fragment']+task['suffix']).encode())
            # Fail closed: syntax/name/tool errors and timeouts aren't intended negatives.
            negative=(bad.get('status')=='verifier_reject' and bad.get('returncode')==10
                and re.search(r'(?i)(obligation|proof).*fail|fail.*(obligation|proof)',bad.get('output',''))
                and not re.search(r'(?i)parse|syntax|unknown operator|not found|exception|cannot find',bad.get('output','')))
            if (provenance and good.get('returncode')==0 and good.get('certified') is True
                    and good.get('proved',0)==good.get('total',0)>0 and negative):
                admitted.append(task)
    dump(output/'controls.json',rows)
    after=identity(); dump(output/'verifier_after.json',after)
    stable=before==after
    if not stable:
        admitted=[]
    summary=dict(requested_train=6,admitted_train=len(admitted),verifier_identity_stable=stable,
                 unadmitted_train=6-len(admitted),completed_controls=sum('control'in r and 'command'in r for r in rows),
                 elapsed_seconds=time.monotonic()-started,complete_population=len(admitted)==6)
    dump(output/'summary.json',summary)
    # Never silently substitute an easier three-task population for requested six.
    if len(admitted)==6 and stable:
        manifest=copy.deepcopy(selection)
        manifest.update(kind='controlled_breadth_whole_target_train',training_authorized=True,
                        admitted_train=6,controls_sha256=sha((output/'controls.json').read_bytes()),
                        verifier_identity=before)
        dump(output/'manifest.json',manifest)
    return summary


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--controls',action='store_true')
    parser.add_argument('--seconds',type=float,default=480)
    parser.add_argument('--timeout',type=float,default=30)
    args=parser.parse_args()
    selection=construct()
    args.output.mkdir(parents=True,exist_ok=False)
    dump(args.output/'selection.json',selection)
    dump(args.output/'config.json',dict(hypothesis='Six new-family whole-target human proofs pass exact strict controls',
        seconds=args.seconds,timeout=args.timeout,controls=args.controls,
        stop='All requested controls or wall deadline; no training and no omitted population'))
    (args.output/'builder.py').write_bytes(Path(__file__).read_bytes())
    if args.controls:
        print(json.dumps(controls(selection,args.output,args.seconds,args.timeout)))
    else:
        print(json.dumps({k:selection[k] for k in ('requested_train','admitted_train','rejected_train','control_eligible','development')}))


if __name__=='__main__':
    main()
