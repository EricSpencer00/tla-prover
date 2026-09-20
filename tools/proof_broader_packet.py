#!/usr/bin/env python3
"""Explicit 32 whole-target TRAIN packet; local evidence preparation, no training.

Both source populations remain complete. Remote validation requires this module
and the stdlib-only original whole-packet helper, not local checker/corpus paths.
Callers must additionally pin the exported file's complete byte hash.
"""
import argparse
import json
import math
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.proof_whole_packet import (sha,digest,dump,checked,task_prompt,
    TOKENIZER,TOKENIZER_HASHES,ALGORITHM,CONTRACT,DEV_IDS)
from tools.proof_whole_packet import TRAIN_IDS as ORIGINAL_IDS

MANIFEST6=ROOT/'results/runs/proof-breadth-controls-20260905-v1/manifest.json'
MANIFEST26=ROOT/'results/runs/proof-breadth26-controls-20260905-v1/manifest.json'
SOURCE_MANIFEST_SHA256=dict(
    original6='23d15fba5fcb08e8d8436d02deb727a34976bc220e8d66ec7bc333728949627e',
    broader26='fa9891e67e8c099e2956d5d9f78a29780f186c132a6446d0ed02e5dc89487526')
MANIFEST_SHA256=digest([SOURCE_MANIFEST_SHA256['original6'],SOURCE_MANIFEST_SHA256['broader26']])
CONTROLS_SHA256=dict(original6='44a91acff9e2a3c8d1dd374fd6dcb66758a3a379d77c9af6e078dec2baeccab3',
    broader26='74f03d5a2375500fd7b71433237c096310a6990a20667fe18ce1ef1a408b50fe')
OUTCOMES_SHA256='8b48ecd13d4d490bbc24e4cc15c54d245c0ec28e4e0a9cae5f5cfeb086aab9ae'
NEW_IDS=(['breadth26-Quicksort-'+name for name in (
    'AutomorphismsCompose','PermsOfLemma','PermsOfPermsOf','MinIsMin','MaxIsMax','IntervalMinMax','PartitionsLemma')]+
    ['breadth26-BinarySearch-SortedLess','breadth26-clean_proof-NatMinNat','breadth26-clean_proof-PrimerPositive']+
    ['breadth26-LamportMutex_proofs-'+name for name in ('BroadcastType','NotContainsAtMostOne','NotContainsPrecedes',
     'PrecedesHead','AtMostOneTail','ContainsTail','AtMostOneHead','ContainsSend','NotContainsSend','AtMostOneSend',
     'PrecedesSend','PrecedesTail','PrecedesInTail')]+
    ['breadth26-tcp_proof-'+name for name in ('NetworkType','PrefixOneNonEmpty','PrefixTwoNonEmpty')])
TRAIN_IDS=ORIGINAL_IDS+NEW_IDS
KIND='frozen32_broader_whole_target_proofs'
SHAPE=dict(train_spans=32,leaf_spans=17,hierarchical_spans=15,source_families=7,
           whole_target_count=32,independent_theorem_count_claimed=False,whole_target_generation=True)
FAMILY_COUNTS={'tlaplus/Examples:'+name:count for name,count in (
    ('locks_auxiliary_vars',1),('barriers',1),('MisraReachability',4),('LoopInvariance',8),
    ('glowingRaccoon',2),('lamport_mutex',13),('tcp',3))}
IMPLEMENTATION=('tools/proof_broader_packet.py','tools/proof_whole_packet.py',
    'tools/proof_breadth_manifest.py','tools/proof_breadth26_manifest.py',
    'tools/proof_candidate_rank.py','tools/proof_cuda_eval.py','tools/proof_repair_pilot.py')


def load_manifests(manifest6=MANIFEST6,manifest26=MANIFEST26):
    result={name:json.loads(checked(path,SOURCE_MANIFEST_SHA256[name])) for name,path in
            [('original6',manifest6),('broader26',manifest26)]}
    for name,count in [('original6',6),('broader26',26)]:
        data=result[name]
        if (data.get('training_authorized') is not True or data.get('admitted_train')!=count or
                data.get('fragment_contract')!=CONTRACT or data.get('controls_sha256')!=CONTROLS_SHA256[name]):
            raise ValueError('Exact complete admitted populations required')
    return result


def combined_tasks(manifests):
    old=manifests['original6']['tasks'];new=manifests['broader26']['tasks']
    if old[6:]!=new[26:]:
        raise ValueError('Development tasks changed between population manifests')
    tasks=old[:6]+new[:26]+old[6:]
    if [t['id'] for t in tasks]!=TRAIN_IDS+DEV_IDS:
        raise ValueError('Exact ordered 32 TRAIN and four DEV required')
    for index,task in enumerate(tasks):
        if task['split']!=('train' if index<32 else 'development'):
            raise ValueError('Frozen split mismatch')
    for field in ('source_family','source_sha256','assembled_sha256'):
        if {t[field] for t in tasks[:32]} & {t[field] for t in tasks[32:]}:
            raise ValueError('Training/development family or source overlap')
    return tasks


def export_tasks(manifest6=MANIFEST6,manifest26=MANIFEST26):
    tasks=combined_tasks(load_manifests(manifest6,manifest26));rows=[]
    for task in tasks:
        checked(task['source_path'],task['source_sha256'])
        if sha((task['prefix']+task['reference_fragment']+task['suffix']).encode())!=task['assembled_sha256']:
            raise ValueError('Immutable task assembly mismatch')
        if set(task['dependencies'])!=set(task['dependency_sha256']):
            raise ValueError('Incomplete dependency source hashes')
        prompt=task_prompt(task)
        rows.append(dict(id=task['id'],split=task['split'],prompt=prompt,prompt_sha256=sha(prompt.encode())))
    packet=dict(schema=1,manifest_sha256=MANIFEST_SHA256,source_manifest_sha256=SOURCE_MANIFEST_SHA256,
                tasks=rows,requested_tasks=36,reference_fragments_exported=False,candidates_exported=False)
    validate_export(packet)
    return packet,tasks


def validate_export(packet):
    if (set(packet)!={'schema','manifest_sha256','source_manifest_sha256','tasks','requested_tasks',
                     'reference_fragments_exported','candidates_exported'} or packet['schema']!=1 or
            packet['manifest_sha256']!=MANIFEST_SHA256 or packet['source_manifest_sha256']!=SOURCE_MANIFEST_SHA256 or
            packet['requested_tasks']!=36 or packet['reference_fragments_exported'] is not False or
            packet['candidates_exported'] is not False):
        raise ValueError('Reference-free broader prompt contract mismatch')
    rows=packet['tasks']
    if [r['id'] for r in rows]!=TRAIN_IDS+DEV_IDS:
        raise ValueError('Exact ordered 36 prompts required')
    for row in rows:
        if (set(row)!={'id','split','prompt','prompt_sha256'} or row['split']!=('train' if row['id'] in TRAIN_IDS else 'development') or
                not isinstance(row['prompt'],str) or not row['prompt'] or sha(row['prompt'].encode())!=row['prompt_sha256']):
            raise ValueError('Prompt fields, split or hash mismatch')
    return rows


def broader_control_binding(task,row,label,identity):
    """New26 negatives preserve ASSUME/NEW scope; no legacy-global mutation."""
    from harness.proof_fragment_check import classify_result
    from harness.proof_full_fragment_check import validate_fragment
    from tools.proof_breadth26_manifest import wrong_conclusion,intended_false_failure
    prefix=task['prefix'] if label=='reference' else wrong_conclusion(task)
    fragment=task['reference_fragment'];suffix=task['suffix']
    validate_fragment(prefix,fragment,suffix,task['theorem_name'])
    assembled=(prefix+fragment+suffix).encode();expected=sha(assembled)
    deps={Path(p).name:h for p,h in task['dependency_sha256'].items()}
    if (row['id']!=task['id'] or row['control']!=label or row.get('contract_version')!=CONTRACT or
            row.get('timed_out') is not False or row.get('sha256')!=expected or row.get('dependency_sha256')!=deps or
            not {'--strict','--nofp'}.issubset(row.get('command',[])) or
            Path(row['command'][0]).resolve()!=Path(identity['tlapm_path']).resolve()):
        raise ValueError('Strict attested broader control required')
    work=Path(row['workdir']);candidate=Path(row['candidate_path'])
    if (candidate.resolve().parent!=work.resolve() or candidate.name!=row['command'][-1] or
            checked(candidate,expected)!=assembled or (work/'tlapm.log').read_text()!=row['output']):
        raise ValueError('Raw control module/log/command mismatch')
    if json.loads((work/'input.json').read_text())!=dict(prefix=prefix,fragment=fragment,suffix=suffix,
            theorem_name=task['theorem_name'],contract_version=CONTRACT):
        raise ValueError('Raw control immutable input mismatch')
    for name,value in deps.items():checked(work/name,value)
    status,proved,total=classify_result(row['returncode'],row['output'],False)
    if (status,proved,total)!=(row['status'],row['proved'],row['total']):
        raise ValueError('Raw control classification mismatch')
    if label=='reference':
        if not (row['certified'] is True and row['returncode']==0 and status=='pass' and proved==total>0):
            raise ValueError('Every positive obligation must be proved')
    elif label!='wrong_conclusion' or not intended_false_failure(row):
        raise ValueError('Exactly one parsed PROVE FALSE obligation must fail')
    return dict(id=task['id'],control=label,proved=proved,total=total,status=status,
        returncode=row['returncode'],certified=row['certified'],candidate_sha256=expected,
        input_sha256=sha((work/'input.json').read_bytes()),log_sha256=sha((work/'tlapm.log').read_bytes()),
        dependency_sha256=deps,command=row['command'],negative_contract='preserve-assumptions-conclusion-only-FALSE-v1')


def current_identity():
    from tools.proof_breadth26_manifest import control_identity
    from tools.proof_breadth_manifest import control_identity as old_identity
    return dict(original6=old_identity(),broader26=control_identity())


def reconstruct(manifests):
    from tools.proof_breadth_manifest import construct as original
    from tools.proof_breadth26_manifest import construct as broader
    selections=dict(original6=original(),broader26=broader())
    for name,count,kind in [('original6',6,'controlled_breadth_whole_target_train'),
                            ('broader26',26,'controlled_breadth26_whole_target_train')]:
        expected=dict(selections[name],kind=kind,training_authorized=True,admitted_train=count,
            controls_sha256=CONTROLS_SHA256[name],verifier_identity=manifests[name]['verifier_identity'])
        if name=='broader26':
            expected.update(outcomes_sha256=OUTCOMES_SHA256,negative_contract='preserve-assumptions-conclusion-only-FALSE-v1')
        if expected!=manifests[name]:
            raise ValueError('Current full source/exclusion reconstruction differs: '+name)
    return selections


def token_feasibility(rows,prompts,tokenizer_path=TOKENIZER):
    from tools.proof_whole_packet import token_feasibility as old_feasibility
    from tools.proof_candidate_rank import encode_candidate
    from transformers import AutoTokenizer
    result=old_feasibility(rows,prompts,tokenizer_path)
    tokenizer=AutoTokenizer.from_pretrained(tokenizer_path,local_files_only=True)
    by_id={r['id']:r for r in result['rows']}
    for row in rows:
        encoded=encode_candidate(tokenizer,row['prompt'],row['response'],8192)
        response_ids=encoded['input_ids'][encoded['prompt_tokens']:]
        if response_ids[-1]!=tokenizer.eos_token_id or tokenizer.eos_token_id in response_ids[:-1]:
            raise ValueError('Actual first EOS must terminate the TRAIN response')
        by_id[row['id']].update(terminal_eos_token_id=response_ids[-1],actual_eos_verified=True,
            response_token_ids_sha256=digest(response_ids),training_token_ids_sha256=digest(encoded['input_ids']))
    result['terminal_eos_token_id']=tokenizer.eos_token_id
    return result


def _hash(value):
    return isinstance(value,str) and re.fullmatch('[0-9a-f]{64}',value) is not None


def validate_training_packet(packet):
    """Standalone data-contract validation, never local paths or model execution."""
    if (packet.get('schema_version')!=1 or packet.get('packet_kind')!=KIND or packet.get('algorithm')!=ALGORITHM or
            packet.get('split')!='train' or packet.get('training_ready') is not True or
            packet.get('evaluation_responses_exported') is not False or packet.get('manifest_sha256')!=MANIFEST_SHA256 or
            packet.get('source_manifest_sha256')!=SOURCE_MANIFEST_SHA256 or packet.get('train_ids')!=TRAIN_IDS or
            packet.get('task_shape')!=SHAPE):
        raise ValueError('Complete frozen32 whole-target TRAIN contract required')
    rows=packet['rows']; fields={'id','split','source_family','source_sha256','assembled_sha256',
                                'prompt','prompt_sha256','response','response_sha256'}
    if [r['id'] for r in rows]!=TRAIN_IDS:
        raise ValueError('Exact ordered32 TRAIN rows required')
    for row in rows:
        if set(row)!=fields or row['split']!='train':raise ValueError('Unexpected TRAIN row fields or split')
        for name in ('prompt','response'):
            if not isinstance(row[name],str) or not row[name] or sha(row[name].encode())!=row[name+'_sha256']:
                raise ValueError('TRAIN text hash mismatch')
        if not all(_hash(row[name]) for name in ('source_sha256','assembled_sha256')):
            raise ValueError('Source and assembly identity required')
    counts={family:sum(r['source_family']==family for r in rows) for family in {r['source_family'] for r in rows}}
    if counts!=FAMILY_COUNTS or sum(bool(re.search(r'(?m)^\s*<1>',r['response'])) for r in rows)!=15:
        raise ValueError('Exact seven families,15 hierarchical17 leaf targets required')
    evidence=packet['evidence']
    if (evidence.get('manifest_sha256')!=MANIFEST_SHA256 or evidence.get('strict_controls_verified') is not True or
            evidence.get('source_manifest_sha256')!=SOURCE_MANIFEST_SHA256 or evidence.get('controls_sha256')!=CONTROLS_SHA256 or
            evidence.get('original18_reference_text_exported') is not False or evidence.get('threshold')!=.65 or
            evidence.get('canonical_matches')!=0 or not math.isfinite(evidence['max_jaccard']) or
            not 0<=evidence['max_jaccard']<.65):
        raise ValueError('Full bound local exclusion evidence required')
    populations=evidence['populations']
    if set(populations)!={'original18','official119','official30','development'}:
        raise ValueError('All exclusion populations required')
    for name,count in [('original18',18),('official119',119),('official30',30),('development',4)]:
        if len(populations[name])!=count or len(set(populations[name]))!=count:
            raise ValueError('Complete distinct excluded population required')
    if populations['development']!=DEV_IDS:raise ValueError('Unchanged DEV required')
    identity=evidence['verifier_identity']
    if (set(identity)!={'before','after','controlled'} or not identity['before'] or
            identity['before']!=identity['after'] or identity['before']!=identity['controlled'] or
            set(identity['before'])!={'original6','broader26'} or digest(identity)!=evidence['verifier_identity_sha256'] or
            identity['before']['broader26'].get('negative_contract')!='preserve-assumptions-conclusion-only-FALSE-v1'):
        raise ValueError('Both full current/control verifier identities must match')
    controls=evidence['controls']
    if [(c['id'],c['control']) for c in controls]!=[(i,label) for i in TRAIN_IDS for label in ('reference','wrong_conclusion')]:
        raise ValueError('Exactly64 ordered raw control bindings required')
    for control in controls:
        if not {'--strict','--nofp'}.issubset(control['command']) or not all(_hash(control[n]) for n in
                ('candidate_sha256','input_sha256','log_sha256')):
            raise ValueError('Strict raw artifact bindings required')
        if control['control']=='reference':
            row=rows[TRAIN_IDS.index(control['id'])]
            if not (control['candidate_sha256']==row['assembled_sha256'] and control['proved']==control['total']>0 and
                    control['status']=='pass' and control['returncode']==0 and control['certified'] is True):
                raise ValueError('All exact positive obligations must pass')
        elif not (control['returncode']==10 and control['status']=='verifier_reject' and control['certified'] is False):
            raise ValueError('Intended negative control required')
        if control['id'] in NEW_IDS and control.get('negative_contract')!='preserve-assumptions-conclusion-only-FALSE-v1':
            raise ValueError('New26 assumption-preserving negative contract required')
    for name in ('selection_sha256','raw_source_sha256','implementation_sha256','exclusion_audit_sha256'):
        values=evidence[name]
        if not isinstance(values,dict) or not values or not all(_hash(x) for x in values.values()):
            raise ValueError('Complete preparation source/implementation/exclusion hashes required')
    if set(evidence['implementation_sha256'])!=set(IMPLEMENTATION):raise ValueError('Exact implementation inventory required')
    token=packet['token_feasibility']
    if (token['max_tokens']!=8192 or token['max_new_tokens']!=3072 or token['tokenizer_files']!=TOKENIZER_HASHES or
            token['terminal_eos_token_id']!=128009 or [r['id'] for r in token['rows']]!=TRAIN_IDS+DEV_IDS):
        raise ValueError('Pinned actual token feasibility for36 tasks required')
    for row in token['rows']:
        if not 0<row['prompt_tokens']<=5120 or not _hash(row['input_token_ids_sha256']):
            raise ValueError('Frozen generation context overflow or missing actual prefix hash')
        if row['id'] in TRAIN_IDS and not (row['training_inference_prefix_equal'] is True and
                row['actual_eos_verified'] is True and row['terminal_eos_token_id']==128009 and
                2<=row['response_tokens']<=3072 and row['total_tokens']==row['prompt_tokens']+row['response_tokens'] and
                _hash(row['response_token_ids_sha256']) and _hash(row['training_token_ids_sha256'])):
            raise ValueError('Actual EOS and exact inference-prefix TRAIN encoding required')
    return rows


def prepare(output,manifest6=MANIFEST6,manifest26=MANIFEST26,tokenizer_path=TOKENIZER):
    from tools.proof_whole_packet import control_binding as original_binding
    from tools.proof_original18 import MODULES
    manifests=load_manifests(manifest6,manifest26);before=current_identity()
    controlled={k:v['verifier_identity'] for k,v in manifests.items()}
    if before!=controlled:raise ValueError('Control runtime/source identity no longer current')
    implementation={p:sha((ROOT/p).read_bytes()) for p in IMPLEMENTATION}
    selections=reconstruct(manifests);prompts,tasks=export_tasks(manifest6,manifest26)
    controls=[];source_hashes={}
    for name,path,selected,binder in [('original6',manifest6,tasks[:6],original_binding),
                                    ('broader26',manifest26,tasks[6:32],broader_control_binding)]:
        raw_controls=json.loads(checked(path.parent/'controls.json',CONTROLS_SHA256[name]))
        if [(r['id'],r['control']) for r in raw_controls]!=[(t['id'],label) for t in selected for label in ('reference','wrong_conclusion')]:
            raise ValueError('Complete raw control population required')
        if name=='broader26':
            outcomes=json.loads(checked(path.parent/'outcomes.json',OUTCOMES_SHA256))
            if [r['id'] for r in outcomes]!=NEW_IDS or any(r['admitted'] is not True for r in outcomes):
                raise ValueError('All26 admitted outcomes required')
        for index,task in enumerate(selected):
            controls.extend(binder(task,raw_controls[2*index+j],label,before[name])
                            for j,label in enumerate(('reference','wrong_conclusion')))
            source_hashes[task['source_path']]=task['source_sha256']
            source_hashes.update(task['dependency_sha256'])
    rows=[]
    for task,prompt in zip(tasks[:32],prompts['tasks'][:32]):
        response=task['reference_fragment']
        rows.append({k:task[k] for k in ('id','split','source_family','source_sha256','assembled_sha256')} |
                    dict(prompt=prompt['prompt'],prompt_sha256=prompt['prompt_sha256'],response=response,response_sha256=sha(response.encode())))
    feasibility=token_feasibility(rows,prompts,tokenizer_path)
    after=current_identity()
    if before!=after or implementation!={p:sha((ROOT/p).read_bytes()) for p in IMPLEMENTATION}:
        raise ValueError('Current verifier/source/implementation changed during preparation')
    identity=dict(before=before,after=after,controlled=controlled)
    comparisons=[r for task in tasks[:32] for r in task['decontamination'].values()]
    evidence=dict(manifest_sha256=MANIFEST_SHA256,source_manifest_sha256=SOURCE_MANIFEST_SHA256,
        strict_controls_verified=True,controls_sha256=CONTROLS_SHA256,controls=controls,
        selection_sha256={k:digest(v) for k,v in selections.items()},
        raw_source_sha256=source_hashes,implementation_sha256=implementation,
        exclusion_audit_sha256={k:digest(v['exclusion_sha256']) for k,v in selections.items()},
        verifier_identity=identity,verifier_identity_sha256=digest(identity),threshold=.65,
        canonical_matches=sum(len(r['exact_normalized']) for r in comparisons),max_jaccard=max(r['max_jaccard'] for r in comparisons),
        original18_reference_text_exported=False,populations=dict(original18=list(MODULES),development=DEV_IDS,
            official119=[r['id'] for r in selections['original6']['official_sources'] if r['id'].startswith('official119:')],
            official30=[r['id'] for r in selections['original6']['official_sources'] if r['id'].startswith('official30:')]),
        scope='Local lexical exclusion only. Preceding human proofs and overlapping generic helper goal templates remain; unknown pretraining absence not certified.')
    packet=dict(schema_version=1,packet_kind=KIND,algorithm=ALGORITHM,split='train',training_ready=True,
        manifest_sha256=MANIFEST_SHA256,source_manifest_sha256=SOURCE_MANIFEST_SHA256,train_ids=TRAIN_IDS,
        rows=rows,task_shape=SHAPE,evaluation_responses_exported=False,evidence=evidence,token_feasibility=feasibility)
    validate_training_packet(packet)
    output.mkdir(parents=True,exist_ok=False)
    dump(output/'train.json',packet);dump(output/'prompts.json',prompts)
    dump(output/'summary.json',dict(training_ready=True,train_packet_sha256=sha((output/'train.json').read_bytes()),
        prompts_sha256=sha((output/'prompts.json').read_bytes()),task_shape=SHAPE,token_feasibility=feasibility,
        checker_executed=False,training_executed=False,requested_train=32,requested_development=4,verified_controls=64))
    return packet


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest6',type=Path,default=MANIFEST6)
    parser.add_argument('--manifest26',type=Path,default=MANIFEST26)
    parser.add_argument('--tokenizer-path',type=Path,default=TOKENIZER)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();packet=prepare(args.output,args.manifest6,args.manifest26,args.tokenizer_path)
    print(json.dumps(dict(training_ready=True,train_tasks=len(packet['rows']),checker_executed=False,training_executed=False)))


if __name__=='__main__':main()
