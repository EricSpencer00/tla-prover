#!/usr/bin/env python3
"""Freeze six controlled whole-target proofs for response-only SFT.

Local preparation reattests sources, exclusions and raw verifier artifacts. The
remote validators are stdlib-only and consume a separately caller-hash-pinned
packet; they do not execute TLAPS or require local corpus paths.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
MANIFEST_SHA256 = '23d15fba5fcb08e8d8436d02deb727a34976bc220e8d66ec7bc333728949627e'
MANIFEST = ROOT/'results/runs/proof-breadth-controls-20260905-v1/manifest.json'
TOKENIZER = ROOT/'results/runs/proof-cuda-tokenizer-20260905-v2'
TOKENIZER_HASHES = {
 'config.json':'29e4c210b0d6ac178b16b2a255a568bdb23b581e50ca1ef6a6d071dd85704e6e',
 'generation_config.json':'189fb0c0d7fd8a527db217c0a60a0e013f0394cd8800f9697a666a9e75e5f7fd',
 'model.safetensors.index.json':'146776fce3f6db1103aa6f249e65ee5544c5923ce6f971b092eee79aa6e5d37b',
 'special_tokens_map.json':'6f38c73729248f6c127296386e3cdde96e254636cc58b4169d3fd32328d9a8ec',
 'tokenizer.json':'79e3e522635f3171300913bb421464a87de6222182a0570b9b2ccba2a964b2b4',
 'tokenizer_config.json':'177c7b61e616fecb84c17ce0591acb92c6c4d60e9ac5ababfb940ff23bbcd424',
}
TRAIN_IDS = ['breadth-Lock-MutualExclusion','breadth-Barriers-LockExclusion'] + [
    'breadth-ReachabilityProofs-Reachable'+str(i) for i in range(4)]
DEV_IDS = ['crdt-type-step','crdt-safety-step','crdt-sum-type-proof','crdt-sum-zero-proof']
ALGORITHM = 'response-only causal cross-entropy SFT; fresh float32 AdamW; no RL'
KIND = 'frozen6_whole_target_proofs'
CONTRACT = 'full-proof-fragment-v1'
SHAPE = dict(train_spans=6,leaf_spans=1,hierarchical_spans=5,source_families=3,
             whole_target_count=6,independent_theorem_count_claimed=False,
             whole_target_generation=True)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def digest(value):
    return sha((json.dumps(value,sort_keys=True,separators=(',',':'))).encode())


def dump(path, value):
    path.write_text(json.dumps(value,indent=2)+'\n')


def checked(path, expected):
    raw=Path(path).read_bytes()
    if sha(raw)!=expected:
        raise ValueError('Pinned artifact changed: '+str(path))
    return raw


def whole_prompt(task):
    from tools.proof_repair_pilot import with_dependency_context
    task=with_dependency_context(task)
    dependencies=''.join('\n===BEGIN DEPENDENCY '+d['module']+'===\n'+d['text']+
        '\n===END DEPENDENCY '+d['module']+'===\n' for d in task['dependency_context'])
    return ('Complete the entire missing TLA+ proof marked <PROOF_HOLE>. '
        'The theorem statement, module definitions, assumptions, dependencies and preceding proofs are immutable. '
        'Return only the proof, preferably in a tla code fence, using valid TLAPS syntax. '
        'Hierarchical proof steps and balanced ordinary comments are allowed. '
        'A hierarchical DEFINE step may introduce one fresh proof-local operator; '
        'do not shadow existing names or change module definitions. '
        'Do not introduce axioms, omit proofs, inject declarations, use proof pragmas or repeat the module.\n\n'+
        (dependencies+'\n' if dependencies else '')+task['prefix']+'<PROOF_HOLE>'+task['suffix'])


def task_prompt(task):
    if task['split']=='train':
        return whole_prompt(task)
    if task['split']!='development':
        raise ValueError('Only frozen TRAIN/development tasks supported')
    from tools.proof_repair_pilot import prompt_for, with_dependency_context
    return prompt_for(with_dependency_context(task))


def load_manifest(path):
    data=json.loads(checked(path,MANIFEST_SHA256))
    if (data.get('kind')!='controlled_breadth_whole_target_train' or
            data.get('training_authorized') is not True or data.get('admitted_train')!=6 or
            data.get('fragment_contract')!=CONTRACT):
        raise ValueError('Exact admitted whole-proof manifest required')
    return data


def export_tasks(manifest):
    data=load_manifest(manifest); rows=[]
    for task in data['tasks']:
        checked(task['source_path'],task['source_sha256'])
        if sha((task['prefix']+task['reference_fragment']+task['suffix']).encode())!=task['assembled_sha256']:
            raise ValueError('Immutable task scaffold changed')
        if set(task['dependencies'])!=set(task['dependency_sha256']):
            raise ValueError('Incomplete dependency inventory')
        prompt=task_prompt(task)
        rows.append(dict(id=task['id'],split=task['split'],prompt=prompt,prompt_sha256=sha(prompt.encode())))
    packet=dict(schema=1,manifest_sha256=MANIFEST_SHA256,tasks=rows,requested_tasks=10,
                reference_fragments_exported=False,candidates_exported=False)
    validate_export(packet)
    return packet,data['tasks']


def validate_export(data):
    if (set(data)!={'schema','manifest_sha256','tasks','requested_tasks','reference_fragments_exported','candidates_exported'} or
            data['schema']!=1 or data['manifest_sha256']!=MANIFEST_SHA256 or data['requested_tasks']!=10 or
            data['reference_fragments_exported'] is not False or data['candidates_exported'] is not False):
        raise ValueError('Whole-proof prompt export contract mismatch')
    rows=data['tasks']
    if [r['id'] for r in rows]!=TRAIN_IDS+DEV_IDS:
        raise ValueError('Exact ordered six TRAIN and four DEV tasks required')
    for row in rows:
        if (set(row)!={'id','split','prompt','prompt_sha256'} or not isinstance(row['prompt'],str) or
                not row['prompt'] or sha(row['prompt'].encode())!=row['prompt_sha256'] or
                row['split']!=('train' if row['id'] in TRAIN_IDS else 'development')):
            raise ValueError('Prompt-only row fields, split or hash mismatch')
    return rows


def control_binding(task, row, label, identity):
    """Reclassify exact raw logs, candidate/input bytes and copied dependencies."""
    from harness.proof_fragment_check import classify_result
    from harness.proof_full_fragment_check import validate_fragment
    from tools.proof_breadth_manifest import wrong_conclusion
    prefix=task['prefix'] if label=='reference' else wrong_conclusion(task)
    fragment=task['reference_fragment']; suffix=task['suffix']
    validate_fragment(prefix,fragment,suffix,task['theorem_name'])
    assembled=(prefix+fragment+suffix).encode(); expected=sha(assembled)
    deps={Path(p).name:h for p,h in task['dependency_sha256'].items()}
    if (row['id']!=task['id'] or row['control']!=label or row.get('contract_version')!=CONTRACT or
            row.get('timed_out') is not False or row.get('sha256')!=expected or
            row.get('dependency_sha256')!=deps or not {'--strict','--nofp'}.issubset(row.get('command',[])) or
            Path(row['command'][0]).resolve()!=Path(identity['tlapm_path']).resolve()):
        raise ValueError('Strict attested whole-proof control required')
    candidate=Path(row['candidate_path']); work=Path(row['workdir'])
    if (candidate.resolve().parent!=work.resolve() or candidate.name!=row['command'][-1] or
            checked(candidate,expected)!=assembled or (work/'tlapm.log').read_text()!=row['output']):
        raise ValueError('Raw control module/log/command mismatch')
    inp=json.loads((work/'input.json').read_text())
    if inp!=dict(prefix=prefix,fragment=fragment,suffix=suffix,theorem_name=task['theorem_name'],contract_version=CONTRACT):
        raise ValueError('Raw control input mismatch')
    for name,value in deps.items():
        checked(work/name,value)
    status,proved,total=classify_result(row['returncode'],row['output'],False)
    if (status,proved,total)!=(row['status'],row['proved'],row['total']):
        raise ValueError('Raw control classification mismatch')
    if label=='reference':
        if not (row['certified'] is True and row['returncode']==0 and status=='pass' and proved==total>0):
            raise ValueError('All positive obligations must be proved')
    elif not (row['certified'] is False and row['returncode']==10 and status=='verifier_reject' and
            re.search(r'\bPROVE\s+FALSE\b',row['output']) and
            re.findall(r'\b(\d+)/\d+ obligations failed\.',row['output'])==['1'] and
            re.search(r'(?i)(obligation|proof).*fail|fail.*(obligation|proof)',row['output']) and
            not re.search(r'(?i)parse|syntax|unknown operator|not found|exception|cannot find',row['output'])):
        raise ValueError('Wrong conclusion must fail proof obligations, not infrastructure or parsing')
    return dict(id=task['id'],control=label,proved=proved,total=total,status=status,returncode=row['returncode'],
        certified=row['certified'],candidate_sha256=expected,input_sha256=sha((work/'input.json').read_bytes()),
        log_sha256=sha((work/'tlapm.log').read_bytes()),dependency_sha256=deps,command=row['command'])


def token_feasibility(rows, prompts, tokenizer_path=TOKENIZER):
    from transformers import AutoTokenizer
    from tools.proof_candidate_rank import encode_candidate
    from tools.proof_cuda_eval import encode_prompt
    for name,value in TOKENIZER_HASHES.items():
        checked(tokenizer_path/name,value)
    tokenizer=AutoTokenizer.from_pretrained(tokenizer_path,local_files_only=True)
    counts=[]; by_id={r['id']:r for r in rows}
    for prompt in prompts['tasks']:
        actual=encode_prompt(tokenizer,prompt)
        if actual['input_tokens']+3072>8192:
            raise ValueError('Frozen full output budget does not fit: '+prompt['id'])
        row=dict(id=prompt['id'],prompt_tokens=actual['input_tokens'],
                 input_token_ids_sha256=digest(actual['input_token_ids']))
        if prompt['id'] in by_id:
            encoded=encode_candidate(tokenizer,prompt['prompt'],by_id[prompt['id']]['response'],8192)
            if (encoded['rendered_prompt']!=actual['rendered_prompt'] or
                    encoded['input_ids'][:encoded['prompt_tokens']]!=actual['input_token_ids'] or
                    encoded['response_tokens']>3072):
                raise ValueError('Training/inference prefix differs or response exceeds generation budget')
            row.update(response_tokens=encoded['response_tokens'],total_tokens=len(encoded['input_ids']),
                       training_inference_prefix_equal=True)
        counts.append(row)
    return dict(max_tokens=8192,max_new_tokens=3072,tokenizer_files=TOKENIZER_HASHES,rows=counts)


def validate_training_packet(packet):
    """Validate the explicit six-target contract remotely, without corpus imports."""
    if (packet.get('schema_version')!=1 or packet.get('packet_kind')!=KIND or packet.get('algorithm')!=ALGORITHM or
            packet.get('split')!='train' or packet.get('training_ready') is not True or
            packet.get('evaluation_responses_exported') is not False or packet.get('manifest_sha256')!=MANIFEST_SHA256 or
            packet.get('task_shape')!=SHAPE or packet.get('train_ids')!=TRAIN_IDS):
        raise ValueError('Exact frozen six-target TRAIN packet required')
    rows=packet['rows']
    if [r['id'] for r in rows]!=TRAIN_IDS or len({r['source_family'] for r in rows})!=3:
        raise ValueError('Exact ordered TRAIN population and three families required')
    fields={'id','split','source_family','source_sha256','assembled_sha256','prompt','prompt_sha256','response','response_sha256'}
    for row in rows:
        if set(row)!=fields or row['split']!='train':
            raise ValueError('Unexpected training row fields or split')
        for name in ('prompt','response'):
            if not isinstance(row[name],str) or not row[name] or sha(row[name].encode())!=row[name+'_sha256']:
                raise ValueError('Training text hash mismatch')
        for name in ('source_sha256','assembled_sha256'):
            if not re.fullmatch('[0-9a-f]{64}',row[name]):
                raise ValueError('Training provenance hash missing')
    if sum(bool(re.search(r'(?m)^\s*<1>',r['response'])) for r in rows)!=5:
        raise ValueError('Five hierarchical and one leaf whole proof required')
    evidence=packet['evidence']
    if (evidence.get('manifest_sha256')!=MANIFEST_SHA256 or evidence.get('strict_controls_verified') is not True or
            evidence.get('original18_reference_text_exported') is not False or evidence.get('threshold')!=.65 or
            evidence.get('canonical_matches')!=0 or not math.isfinite(evidence['max_jaccard']) or
            not 0<=evidence['max_jaccard']<.65 or
            set(evidence['populations'])!={'original18','official119','official30','development'}):
        raise ValueError('Full local lexical exclusion evidence required')
    for name,count in [('original18',18),('official119',119),('official30',30),('development',4)]:
        members=evidence['populations'][name]
        if len(members)!=count or len(set(members))!=count:
            raise ValueError('Full unique exclusion population required')
    if evidence['populations']['development']!=DEV_IDS:
        raise ValueError('Four unchanged DEV exclusions required')
    identity=evidence['verifier_identity']
    if (not identity.get('before') or identity['before']!=identity.get('after') or
            identity['before']!=identity.get('controlled') or digest(identity)!=evidence['verifier_identity_sha256'] or
            identity['before'].get('breadth_fragment_contract')!=CONTRACT):
        raise ValueError('Unchanged full controlled/current verifier identity required')
    controls=evidence['controls']
    if [(c['id'],c['control']) for c in controls]!=[(i,label) for i in TRAIN_IDS for label in ('reference','wrong_conclusion')]:
        raise ValueError('Exact twelve control bindings required')
    for control in controls:
        if not {'--strict','--nofp'}.issubset(control['command']):
            raise ValueError('Strict uncached controls required')
        for field in ('candidate_sha256','input_sha256','log_sha256'):
            if not re.fullmatch('[0-9a-f]{64}',control[field]):
                raise ValueError('Raw control artifact binding required')
        if control['control']=='reference':
            row=rows[TRAIN_IDS.index(control['id'])]
            if not (control['candidate_sha256']==row['assembled_sha256'] and control['proved']==control['total']>0 and
                    control['status']=='pass' and control['returncode']==0 and control['certified'] is True):
                raise ValueError('All exact target obligations must pass')
        elif not (control['status']=='verifier_reject' and control['returncode']==10 and control['certified'] is False):
            raise ValueError('Wrong-conclusion control must fail')
    for field in ('controls_sha256','selection_sha256','exclusion_audit_sha256','verifier_identity_sha256'):
        if not re.fullmatch('[0-9a-f]{64}',evidence[field]):
            raise ValueError('Missing preparation evidence hash')
    feasibility=packet['token_feasibility']
    if (feasibility['max_tokens']!=8192 or feasibility['max_new_tokens']!=3072 or
            feasibility['tokenizer_files']!=TOKENIZER_HASHES or
            [r['id'] for r in feasibility['rows']]!=TRAIN_IDS+DEV_IDS):
        raise ValueError('Pinned complete token feasibility evidence required')
    for row in feasibility['rows']:
        if not 0<row['prompt_tokens']<=8192-3072:
            raise ValueError('Generation context overflow')
        if row['id'] in TRAIN_IDS and not (row['training_inference_prefix_equal'] is True and
                2<=row['response_tokens']<=3072 and row['total_tokens']==row['prompt_tokens']+row['response_tokens']):
            raise ValueError('Exact training/inference prefix and response budget required')
    return rows


def prepare(manifest_path, output, tokenizer_path=TOKENIZER):
    from tools.proof_breadth_manifest import construct, control_identity
    from tools.proof_original18 import MODULES
    manifest=load_manifest(manifest_path)
    before=control_identity()
    if before!=manifest['verifier_identity']:
        raise ValueError('Current verifier identity differs from admitted controls')
    selection=construct()
    expected=dict(selection,kind='controlled_breadth_whole_target_train',training_authorized=True,admitted_train=6,
                  controls_sha256=manifest['controls_sha256'],verifier_identity=before)
    if expected!=manifest:
        raise ValueError('Reconstructed selection/source/exclusion audit differs from admitted manifest')
    controls_path=manifest_path.parent/'controls.json'
    controls=json.loads(checked(controls_path,manifest['controls_sha256']))
    if [(r['id'],r['control']) for r in controls]!=[(i,label) for i in TRAIN_IDS for label in ('reference','wrong_conclusion')]:
        raise ValueError('Exact twelve ordered raw controls required')
    prompts,tasks=export_tasks(manifest_path); train=tasks[:6]; bindings=[]; rows=[]
    for index,task in enumerate(train):
        bindings.extend(control_binding(task,controls[2*index+j],label,before)
                        for j,label in enumerate(('reference','wrong_conclusion')))
        prompt=prompts['tasks'][index]['prompt']; response=task['reference_fragment']
        rows.append({k:task[k] for k in ('id','split','source_family','source_sha256','assembled_sha256')} |
                    dict(prompt=prompt,prompt_sha256=sha(prompt.encode()),response=response,response_sha256=sha(response.encode())))
    feasibility=token_feasibility(rows,prompts,tokenizer_path)
    after=control_identity()
    identity=dict(before=before,after=after,controlled=manifest['verifier_identity'])
    if before!=after:
        raise ValueError('Verifier identity changed during packet preparation')
    comparisons=[r for task in train for r in task['decontamination'].values()]
    evidence=dict(manifest_sha256=MANIFEST_SHA256,strict_controls_verified=True,controls=bindings,
        controls_sha256=manifest['controls_sha256'],selection_sha256=digest(selection),
        exclusion_audit_sha256=digest(dict(provenance=selection['exclusion_sha256'],comparisons=comparisons)),
        verifier_identity=identity,verifier_identity_sha256=digest(identity),
        threshold=.65,max_jaccard=max(r['max_jaccard'] for r in comparisons),
        canonical_matches=sum(len(r['exact_normalized']) for r in comparisons),
        original18_reference_text_exported=False,populations=dict(original18=list(MODULES),development=DEV_IDS,
            official119=[r['id'] for r in selection['official_sources'] if r['id'].startswith('official119:')],
            official30=[r['id'] for r in selection['official_sources'] if r['id'].startswith('official30:')]),
        scope='Local lexical exclusions only; preceding helper proofs remain, generic helper goal templates overlap. Unknown pretraining absence not certified.')
    packet=dict(schema_version=1,packet_kind=KIND,algorithm=ALGORITHM,split='train',training_ready=True,
        manifest_sha256=MANIFEST_SHA256,task_shape=SHAPE,evaluation_responses_exported=False,
        train_ids=TRAIN_IDS,rows=rows,evidence=evidence,token_feasibility=feasibility)
    validate_training_packet(packet)
    output.mkdir(parents=True,exist_ok=False)
    dump(output/'train.json',packet);dump(output/'prompts.json',prompts)
    dump(output/'summary.json',dict(train_packet_sha256=sha((output/'train.json').read_bytes()),
        prompts_sha256=sha((output/'prompts.json').read_bytes()),training_ready=True,task_shape=SHAPE,
        token_feasibility=feasibility,training_executed=False,checker_executed=False))
    return packet


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest',type=Path,default=MANIFEST)
    parser.add_argument('--tokenizer-path',type=Path,default=TOKENIZER)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    packet=prepare(args.manifest,args.output,args.tokenizer_path)
    print(json.dumps(dict(train_tasks=len(packet['rows']),training_ready=True,training_executed=False)))


if __name__=='__main__':
    main()
