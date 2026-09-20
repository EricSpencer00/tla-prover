#!/usr/bin/env python3
"""Frozen26 broader TRAIN discovery and strict controls; no partial-population admission."""
import argparse
import copy
import json
import math
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_breadth_manifest as legacy
from tools.proof_breadth_manifest import (sha, dump, imports, check_dependency, extract,
    compare, goal_bodies, exclusions, validate_split,
    CONTRACT_VERSION, certify_fragment, TLA_LIBRARY, TLAPM)
COMMIT=legacy.COMMIT
EXAMPLES=ROOT/'tools/tlaplus-examples'
PARENT=legacy.PARENT
PARENT_SHA=legacy.PARENT_SHA
THRESHOLD=.65
SELECTION = (
 ('LoopInvariance/Quicksort.tla','AutomorphismsCompose',58,61,61),
 ('LoopInvariance/Quicksort.tla','PermsOfLemma',63,69,69),
 ('LoopInvariance/Quicksort.tla','PermsOfPermsOf',71,74,84),
 ('LoopInvariance/Quicksort.tla','MinIsMin',93,96,96),
 ('LoopInvariance/Quicksort.tla','MaxIsMax',98,101,101),
 ('LoopInvariance/Quicksort.tla','IntervalMinMax',179,182,182),
 ('LoopInvariance/Quicksort.tla','PartitionsLemma',200,208,208),
 ('LoopInvariance/BinarySearch.tla','SortedLess',29,33,35),
 ('glowingRaccoon/clean_proof.tla','NatMinNat',18,21,21),
 ('glowingRaccoon/clean_proof.tla','PrimerPositive',63,64,66),
 ('lamport_mutex/LamportMutex_proofs.tla','BroadcastType',13,17,17),
 ('lamport_mutex/LamportMutex_proofs.tla','NotContainsAtMostOne',112,115,115),
 ('lamport_mutex/LamportMutex_proofs.tla','NotContainsPrecedes',117,121,121),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesHead',123,128,134),
 ('lamport_mutex/LamportMutex_proofs.tla','AtMostOneTail',136,140,140),
 ('lamport_mutex/LamportMutex_proofs.tla','ContainsTail',142,146,152),
 ('lamport_mutex/LamportMutex_proofs.tla','AtMostOneHead',154,158,158),
 ('lamport_mutex/LamportMutex_proofs.tla','ContainsSend',160,163,163),
 ('lamport_mutex/LamportMutex_proofs.tla','NotContainsSend',165,169,169),
 ('lamport_mutex/LamportMutex_proofs.tla','AtMostOneSend',171,175,175),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesSend',177,181,187),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesTail',189,193,203),
 ('lamport_mutex/LamportMutex_proofs.tla','PrecedesInTail',205,211,225),
 ('tcp/tcp_proof.tla','NetworkType',21,25,25),
 ('tcp/tcp_proof.tla','PrefixOneNonEmpty',42,47,61),
 ('tcp/tcp_proof.tla','PrefixTwoNonEmpty',63,69,77),
)
HASHES = {
 'LoopInvariance/Quicksort.tla':'65c70e42eb28bef01e7754cffe66d87ac1d00b4cd27b107ce389da3f31ad7672',
 'LoopInvariance/BinarySearch.tla':'fa56deb7c8d1cce2e5b9c4559ab7a1ced1fea5098edc46eb8d99c257e8eaecec',
 'glowingRaccoon/clean_proof.tla':'f653d9241d938ead6ee72c509b6e46fdd46eab05678f576d0c8878155863f0f4',
 'lamport_mutex/LamportMutex_proofs.tla':'9cbecb6501595b2222e663e09145f48d3cd73df2c817f07acc4d76acb9ca9f61',
 'tcp/tcp_proof.tla':'23e7180bc27ce366579f604dfda04887e0b32e5642531c5efaf768ebea1e8cd7',
 'glowingRaccoon/clean.tla':'48ba67d167d158f4e34238e13b135ad83cb705ea12d842c0a3506ff851990d73',
 'lamport_mutex/LamportMutex.tla':'dfa726da541fb0515ad482c3b5ca82c81b6f54df6626c3b9edfcebedc2a9c05a',
 'tcp/tcp.tla':'c77f6c0c33e54d4b3ce8ecfd934967569be3f7c613c89b4fdcdfa3768fc56e92',
}

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
        task.update(id='breadth26-'+path.stem+'-'+theorem,module_name=path.stem,
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
    return dict(schema_version=1,kind='breadth26_whole_target_selection_only',tasks=tasks+dev,
                parent_manifest_sha256=PARENT_SHA,source_commit=COMMIT,
                official_sources=parent['official_sources'],exclusion_sha256=provenance,
                requested_train=26,development=4,admitted_train=0,
                rejected_train=sum(bool(t['rejection_reasons']) for t in tasks),
                control_eligible=sum(not t['rejection_reasons'] for t in tasks),
                training_authorized=False,fragment_contract=CONTRACT_VERSION,
                scope='New source families; lexical local exclusion only, not unknown-pretraining absence or gate evidence')


def wrong_conclusion(task):
    """Preserve NEW bindings/assumptions; mutate only the target conclusion."""
    from tools.proof_source_scope import top_level_code
    start,end=task['goal_offsets'];prefix=task['prefix']
    code=top_level_code(prefix)[start:end]
    proves=list(re.finditer(r'\bPROVE\b',code))
    if re.match(r'\s*ASSUME\b',code):
        if len(proves)!=1 or len(re.findall(r'\bASSUME\b',code))!=1:
            raise ValueError('Exactly one non-nested target ASSUME and PROVE required')
        conclusion=start+proves[0].end()
        if re.search(r'\bASSUME\b',code[proves[0].end():]):
            raise ValueError('Nested target sequent is unsupported')
        return prefix[:conclusion]+' FALSE\n'+prefix[end:]
    if proves:raise ValueError('PROVE outside supported ASSUME target')
    return prefix[:start]+' FALSE\n'+prefix[end:]


def control_identity():
    result=legacy.control_identity()
    result['breadth26_source_sha256']={str(Path(__file__).resolve()):sha(Path(__file__).read_bytes())}
    result['breadth26_inputs_sha256']={str(EXAMPLES/'specifications'/name):sha((EXAMPLES/'specifications'/name).read_bytes())
                                      for name in HASHES}
    selection=construct()
    result['breadth26_selection_sha256']=selection_digest(selection)
    paths={str(PARENT)}
    paths.update(name for name in selection['exclusion_sha256'] if Path(name).is_file())
    paths.update(name for t in selection['tasks'] if t['split']=='train'
                 for name in t['standard_library_sha256'] if not name.startswith('tlapm-builtin:'))
    result['breadth26_exclusion_and_standard_sha256']={p:sha(Path(p).read_bytes()) for p in sorted(paths)}
    result['breadth26_exclusion_audit_sha256']=selection['exclusion_sha256']
    result['negative_contract']='preserve-assumptions-conclusion-only-FALSE-v1'
    return result


def selection_digest(selection):
    return sha(json.dumps(selection,sort_keys=True,separators=(',',':')).encode())


def intended_false_failure(result):
    text=result.get('output','')
    counts=re.findall(r'\[ERROR\]:\s+([0-9]+)/([1-9][0-9]*) obligations? failed\.',text)
    return (result.get('status')=='verifier_reject' and result.get('certified') is False
        and result.get('returncode')==10 and result.get('timed_out') is False
        and len(counts)==1 and counts[0][0]=='1'
        and re.search(r'(?m)^\s*PROVE\s+FALSE\s*$',text) is not None
        and re.search(r'(?i)parse|syntax|unknown operator|not found|exception|cannot find|could not load|segmentation|out of memory',text) is None)


def valid_pair(task,good,bad):
    expected_deps={Path(p).name:h for p,h in task['dependency_sha256'].items()}
    for result,prefix in ((good,task['prefix']),(bad,wrong_conclusion(task))):
        if (result.get('contract_version')!=CONTRACT_VERSION or result.get('dependency_sha256')!=expected_deps
                or result.get('sha256')!=sha((prefix+task['reference_fragment']+task['suffix']).encode())
                or result.get('timed_out') is not False
                or not {'--strict','--nofp'}.issubset(result.get('command',[]))):
            return False
    return (good.get('status')=='pass' and good.get('returncode')==0 and good.get('certified') is True
            and good.get('proved',0)==good.get('total',0)>0 and intended_false_failure(bad))


def controls(selection,output,seconds=1800,timeout=30,checker=certify_fragment,identity=None):
    if (not math.isfinite(seconds) or not math.isfinite(timeout)
            or not 0<seconds<=1800 or not 0<timeout<=30):
        raise ValueError('Maximum 1800 seconds total, 30 seconds/control')
    train=[t for t in selection['tasks'] if t['split']=='train']
    if (selection.get('requested_train')!=26 or len(train)!=26
            or len({t['id'] for t in train})!=26):
        raise ValueError('Exactly 26 distinct requested TRAIN candidates required')
    started=time.monotonic();rows=[];admitted=[];outcomes=[]
    identity=identity or control_identity
    before=identity();dump(output/'verifier_before.json',before)
    if before.get('breadth26_selection_sha256',selection_digest(selection))!=selection_digest(selection):
        raise ValueError('Supplied selection differs from currently reconstructed frozen sources/exclusions')
    for task in train:
        pair=[]
        for label in ('reference','wrong_conclusion'):
            remaining=seconds-(time.monotonic()-started)
            if task['rejection_reasons']:
                result=dict(status='selection_reject',certified=False,reasons=task['rejection_reasons'])
            elif remaining<1:
                result=dict(status='unmeasured_budget',certified=False)
            else:
                try:
                    prefix=task['prefix'] if label=='reference' else wrong_conclusion(task)
                    result=checker(prefix,task['reference_fragment'],task['suffix'],
                        theorem_name=task['theorem_name'],dependencies=tuple(map(Path,task['dependencies'])),
                        work_root=output/'controls'/task['id']/label,timeout=min(timeout,remaining))
                except Exception as exc:
                    result=dict(status='control_error',certified=False,reason=str(exc))
            row=dict(id=task['id'],control=label,**result);pair.append(row);rows.append(row)
            dump(output/'controls.json',rows)
        try:accepted=valid_pair(task,*pair)
        except (KeyError,ValueError):accepted=False
        if accepted:admitted.append(task['id'])
        outcomes.append(dict(id=task['id'],admitted=accepted,control_statuses=[r['status'] for r in pair]))
        dump(output/'outcomes.json',outcomes)
    try:after=identity()
    except Exception as exc:
        after=dict(identity_error=type(exc).__name__+': '+str(exc))
    dump(output/'verifier_after.json',after)
    stable=before==after
    if not stable:
        admitted=[]
        for row in outcomes:row.update(admitted=False,reason='verifier_or_source_identity_changed')
        dump(output/'outcomes.json',outcomes)
    summary=dict(requested_train=26,requested_controls=52,ledgered_controls=len(rows),
        admitted_train=len(admitted),unadmitted_train=26-len(admitted),admitted_task_ids=admitted,
        verifier_identity_stable=stable,complete_population=len(admitted)==26,
        completed_controls=sum('command' in r for r in rows),elapsed_seconds=time.monotonic()-started,
        training_authorized=len(admitted)==26 and stable)
    dump(output/'summary.json',summary)
    if summary['training_authorized']:
        manifest=copy.deepcopy(selection)
        manifest.update(kind='controlled_breadth26_whole_target_train',training_authorized=True,admitted_train=26,
            controls_sha256=sha((output/'controls.json').read_bytes()),
            outcomes_sha256=sha((output/'outcomes.json').read_bytes()),verifier_identity=before,
            negative_contract='preserve-assumptions-conclusion-only-FALSE-v1')
        dump(output/'manifest.json',manifest)
    return summary


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True);p.add_argument('--controls',action='store_true')
    p.add_argument('--seconds',type=float,default=1800);p.add_argument('--timeout',type=float,default=30)
    a=p.parse_args();selection=construct()
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'selection.json',selection)
    dump(a.output/'config.json',dict(hypothesis='Broader four-family whole-target proofs survive exact strict controls',
        requested_train=26,requested_controls=52,seconds=a.seconds,timeout=a.timeout,controls=a.controls,
        stop='All52 statuses or declared deadline; no subset admission or training',
        negative_contract='preserve-assumptions-conclusion-only-FALSE-v1'))
    (a.output/'builder.py').write_bytes(Path(__file__).read_bytes())
    result=controls(selection,a.output,a.seconds,a.timeout) if a.controls else {
        k:selection[k] for k in ('requested_train','admitted_train','rejected_train','control_eligible','development')}
    print(json.dumps(result))


if __name__=='__main__':main()
