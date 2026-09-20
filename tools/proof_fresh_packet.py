"""Reference-free fresh14 evaluation exports; never produces TRAIN data."""
import json
from pathlib import Path
import re

from tools.proof_whole_packet import sha,digest,dump,checked,whole_prompt,TOKENIZER,TOKENIZER_HASHES

ROOT=Path(__file__).resolve().parents[1]
EVAL_IDS=(['fresh-DieHard-DieHard_proof-MinNat','fresh-Paxos-Consensus-LivenessTheorem',
           'fresh-byzpaxos-Consensus-EnabledDef','fresh-byzpaxos-Consensus-LiveSpecEquals']+
    ['fresh-ewd840-EWD840_proof-'+name for name in ('Safety','EnabledSystem')]+
    ['fresh-ewd840-SyncTerminationDetection_proof-'+name for name in ('CorrectDetection','Quiescent','Enabled_ST')]+
    ['fresh-ewd998-AsyncTerminationDetection_proof-'+name for name in ('Safety','Stability','EnabledDT')]+
    ['fresh-spanning-spanning_proof-'+name for name in ('SntMsgStep','SntMsgInv')])
IMPLEMENTATION=('tools/proof_fresh_packet.py','tools/proof_broader_packet.py','tools/proof_whole_packet.py',
                'tools/proof_breadth26_manifest.py','tools/proof_cuda_eval.py','tools/proof_candidate_rank.py')


def _hash(value):return isinstance(value,str) and re.fullmatch('[0-9a-f]{64}',value) is not None


def validate_export(packet):
    """Stdlib-only data validator; caller additionally pins the complete packet SHA."""
    if (set(packet)!={'schema','manifest_sha256','selection_sha256','tasks','requested_tasks',
                     'reference_fragments_exported','candidates_exported','training_authorized','evaluation_authorized'} or
            packet['schema']!=1 or not _hash(packet['manifest_sha256']) or not _hash(packet['selection_sha256']) or
            packet['requested_tasks']!=14 or packet['reference_fragments_exported'] is not False or
            packet['candidates_exported'] is not False or packet['training_authorized'] is not False or
            packet['evaluation_authorized'] is not True):
        raise ValueError('Reference-free evaluation-only packet required')
    rows=packet['tasks']
    if [r['id'] for r in rows]!=EVAL_IDS:raise ValueError('Exact ordered14 fresh evaluation IDs required')
    for row in rows:
        if (set(row)!={'id','split','prompt','prompt_sha256'} or row['split']!='fresh_evaluation' or
                not isinstance(row['prompt'],str) or not row['prompt'] or sha(row['prompt'].encode())!=row['prompt_sha256']):
            raise ValueError('Evaluation prompt fields, split or hash mismatch')
    return rows


def _callbacks(construct,identity):
    if construct is None or identity is None:
        from tools import proof_fresh_selection as selection
        construct=construct or selection.construct
        identity=identity or selection.identity
    if not callable(construct) or not callable(identity):raise ValueError('Explicit selection and identity callbacks required')
    return construct,identity


def audit_manifest(manifest_path,expected_manifest_sha256,*,construct=None,identity=None):
    """Reconstruct exact14 selection and reclassify all28 raw controls, read-only."""
    from tools.proof_broader_packet import broader_control_binding
    if not _hash(expected_manifest_sha256):raise ValueError('Caller-pinned controlled manifest SHA required')
    manifest_path=Path(manifest_path)
    manifest=json.loads(checked(manifest_path,expected_manifest_sha256))
    if (manifest.get('kind')!='controlled_fresh14_evaluation' or manifest.get('training_authorized') is not False or
            manifest.get('evaluation_authorized') is not True or manifest.get('admitted_evaluation')!=14 or
            manifest.get('verification_complete') is not True):
        raise ValueError('All14 controlled evaluation tasks required; never TRAIN')
    construct,identity=_callbacks(construct,identity)
    before=identity();selection=construct()
    if (selection.get('requested_evaluation')!=14 or selection.get('training_authorized') is not False or
            [t['id'] for t in selection['tasks']]!=EVAL_IDS or
            any(t.get('split')!='fresh_evaluation' or t.get('rejection_reasons') for t in selection['tasks'])):
        raise ValueError('Exact14 eligible evaluation-only selection required')
    selection_sha=digest(selection)
    if (not isinstance(before,dict) or before.get('fresh_selection_sha256')!=selection_sha or
            before!=manifest['verifier_identity']):
        raise ValueError('Current full source/exclusion/runtime identity differs from controls')
    expected=dict(selection,kind='controlled_fresh14_evaluation',training_authorized=False,evaluation_authorized=True,
        admitted_evaluation=14,verification_complete=True,controls_sha256=manifest['controls_sha256'],
        outcomes_sha256=manifest['outcomes_sha256'],verifier_identity=before,
        negative_contract='preserve-assumptions-conclusion-only-FALSE-v1',
        reference_scope='Local checker controls only; evaluation references must never enter inference or TRAIN exports')
    if expected!=manifest:raise ValueError('Controlled manifest differs from reconstructed source/exclusion selection')
    controls=json.loads(checked(manifest_path.parent/'controls.json',manifest['controls_sha256']))
    outcomes=json.loads(checked(manifest_path.parent/'outcomes.json',manifest['outcomes_sha256']))
    if ([(r['id'],r['control']) for r in controls]!=[(i,label) for i in EVAL_IDS for label in ('reference','wrong_conclusion')] or
            any(r.get('split')!='fresh_evaluation' or r.get('training_authorized') is not False for r in controls) or
            [r['id'] for r in outcomes]!=EVAL_IDS or
            any(r.get('admitted') is not True or r.get('training_authorized') is not False or
                r.get('split')!='fresh_evaluation' for r in outcomes)):
        raise ValueError('Complete28 evaluation controls and14 admitted outcomes required')
    bindings=[];source_hashes={};rows=[]
    for index,task in enumerate(selection['tasks']):
        checked(task['source_path'],task['source_sha256']);source_hashes[task['source_path']]=task['source_sha256']
        if set(task['dependencies'])!=set(task['dependency_sha256']):raise ValueError('Missing dependency source identity')
        for path,value in task['dependency_sha256'].items():checked(path,value);source_hashes[path]=value
        if sha((task['prefix']+task['reference_fragment']+task['suffix']).encode())!=task['assembled_sha256']:
            raise ValueError('Immutable source assembly changed')
        bindings.extend(broader_control_binding(task,controls[2*index+j],label,before)
                        for j,label in enumerate(('reference','wrong_conclusion')))
        # whole_prompt is split-agnostic. Never masquerade EVAL as TRAIN.
        prompt=whole_prompt(task)
        rows.append(dict(id=task['id'],split='fresh_evaluation',prompt=prompt,prompt_sha256=sha(prompt.encode())))
    after=identity()
    if before!=after or digest(construct())!=selection_sha:
        raise ValueError('Runtime/source/exclusion identity changed during reattestation')
    packet=dict(schema=1,manifest_sha256=expected_manifest_sha256,selection_sha256=selection_sha,tasks=rows,
        requested_tasks=14,reference_fragments_exported=False,candidates_exported=False,
        training_authorized=False,evaluation_authorized=True)
    validate_export(packet)
    evidence=dict(manifest_sha256=expected_manifest_sha256,selection_sha256=selection_sha,
        controls_sha256=manifest['controls_sha256'],outcomes_sha256=manifest['outcomes_sha256'],
        raw_source_sha256=source_hashes,controls=bindings,verifier_identity=dict(before=before,after=after),
        training_authorized=False,evaluation_authorized=True,reference_text_exported=False)
    return packet,selection['tasks'],evidence


def export_tasks(manifest_path,expected_manifest_sha256,*,construct=None,identity=None):
    packet,tasks,_=audit_manifest(manifest_path,expected_manifest_sha256,construct=construct,identity=identity)
    return packet,tasks


local_load_tasks=export_tasks


def token_feasibility(packet,tokenizer_path=TOKENIZER):
    from transformers import AutoTokenizer
    from tools.proof_cuda_eval import encode_prompt
    validate_export(packet);tokenizer_path=Path(tokenizer_path)
    for name,value in TOKENIZER_HASHES.items():checked(tokenizer_path/name,value)
    tokenizer=AutoTokenizer.from_pretrained(tokenizer_path,local_files_only=True)
    rows=[]
    for task in packet['tasks']:
        actual=encode_prompt(tokenizer,task)
        if actual['input_tokens']+3072>8192:raise ValueError('Fresh task exceeds unchanged generation context budget')
        rows.append(dict(id=task['id'],input_tokens=actual['input_tokens'],
            input_token_ids_sha256=digest(actual['input_token_ids']),rendered_prompt_sha256=sha(actual['rendered_prompt'].encode())))
    return dict(max_tokens=8192,max_new_tokens=3072,tokenizer_files=TOKENIZER_HASHES,rows=rows)


def prepare(manifest_path,expected_manifest_sha256,output,*,construct=None,identity=None,tokenizer_path=TOKENIZER):
    construct,identity=_callbacks(construct,identity)
    sources={name:sha((ROOT/name).read_bytes()) for name in IMPLEMENTATION}
    packet,_,evidence=audit_manifest(manifest_path,expected_manifest_sha256,construct=construct,identity=identity)
    tokens=token_feasibility(packet,tokenizer_path)
    if (identity()!=evidence['verifier_identity']['after'] or digest(construct())!=packet['selection_sha256'] or
            sources!={name:sha((ROOT/name).read_bytes()) for name in IMPLEMENTATION}):
        raise ValueError('Preparation inputs/runtime/implementation changed')
    evidence.update(token_feasibility=tokens,implementation_sha256=sources)
    output=Path(output);output.mkdir(parents=True,exist_ok=False)
    dump(output/'prompts.json',packet);dump(output/'evidence.json',evidence)
    dump(output/'summary.json',dict(requested_evaluation=14,verified_controls=28,evaluation_ready=True,
        training_authorized=False,training_executed=False,checker_executed=False,reference_text_exported=False,
        prompts_sha256=sha((output/'prompts.json').read_bytes()),evidence_sha256=sha((output/'evidence.json').read_bytes()),
        token_feasibility=tokens))
    return packet
