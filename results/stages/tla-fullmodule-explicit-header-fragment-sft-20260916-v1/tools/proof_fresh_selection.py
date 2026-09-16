#!/usr/bin/env python3
"""Pinned fresh14 evaluation selection and reference-free prompts; never TRAIN."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools import proof_breadth_manifest as legacy
from tools.proof_breadth26_manifest import wrong_conclusion, selection_digest
from tools.proof_whole_packet import sha,digest,dump,whole_prompt,TOKENIZER,TOKENIZER_HASHES
from tools.proof_cuda_train import file_sha
from tools.proof_cuda_eval import encode_prompt
from tools.proof_hierarchical_packet import runtime_identity

COMMIT=legacy.COMMIT
EXAMPLES=ROOT/'tools/tlaplus-examples'
SOURCE_ROOT=EXAMPLES/'specifications'
BUDGET=dict(seconds=1000,timeout=30,requested_controls=28)
SELECTION=[["DieHard/DieHard_proof.tla","MinNat",9,12,12],["Paxos/Consensus.tla","LivenessTheorem",59,60,68],["byzpaxos/Consensus.tla","EnabledDef",185,186,186],["byzpaxos/Consensus.tla","LiveSpecEquals",205,207,207],["ewd840/EWD840_proof.tla","Safety",55,56,59],["ewd840/EWD840_proof.tla","EnabledSystem",95,100,109],["ewd840/SyncTerminationDetection_proof.tla","CorrectDetection",16,17,22],["ewd840/SyncTerminationDetection_proof.tla","Quiescent",24,25,28],["ewd840/SyncTerminationDetection_proof.tla","Enabled_ST",37,40,40],["ewd998/AsyncTerminationDetection_proof.tla","Safety",19,20,26],["ewd998/AsyncTerminationDetection_proof.tla","Stability",28,29,31],["ewd998/AsyncTerminationDetection_proof.tla","EnabledDT",41,44,44],["spanning/spanning_proof.tla","SntMsgStep",30,31,147],["spanning/spanning_proof.tla","SntMsgInv",149,150,156]]
HASHES={"DieHard/DieHard_proof.tla":"581a7773656302ec59ec3dc6eae78e4c9d39ee9e70894b6fba364f185b123033","DieHard/DieHard.tla":"295495de6509d86a82b88757835b95e3f91fad8691d764ece4d98886dcf42b66","Paxos/Consensus.tla":"c5c181338db9d7489da158daaead6e8ed47b91ca5802f64ecab02dfd379f8e21","byzpaxos/Consensus.tla":"5b877e93b31c982e80b1443127bc2c50c090d7f8d729d468f3b42849315205bf","ewd840/EWD840_proof.tla":"2b00ab2de84711226037c464f6d39213169d695a1f049f57058c55e115c0586e","ewd840/EWD840.tla":"4a42e8a67c7ecb8425c6e370a5d3b180ad697751128d7b331e778afbcd29b747","ewd840/SyncTerminationDetection.tla":"3626ab87e7431a7c07cf0f92b442fdf38363e6d7a9928f2391476c54a1e4fb2e","ewd840/SyncTerminationDetection_proof.tla":"77cb25e68e54084a4ac07327bb60f0ad171d3aa969cdf278cb4836a504d4983b","ewd998/AsyncTerminationDetection_proof.tla":"87cc4e25be553691b1819b1be20b0addec2f724cec9ffe081014b23f99722ec7","ewd998/AsyncTerminationDetection.tla":"c1b15be68a73c6e5f69c5c09f2736870182a9b0765ad9860452240119911b030","spanning/spanning_proof.tla":"2c96247c40d77a391d56f0cc744d0c0fa7818ffbb0d99d10e411bf82afedf59a","spanning/spanning.tla":"878e917b075f6cd2bfa2a2d0083c1c66e9eb47fe2baaed41dd9a0a28fbcb2c36"}
EXPECTED_PROMPT_COUNTS=[1645,578,2060,2254,2818,3385,799,908,1040,1390,1497,1642,1123,2711]
MANIFESTS={
 'earlier6':('proof-training-cycle-20260905-v1/training/manifest.json','23811bcbae1967a56b1a7e7421c32569662040dbae7d9503e1ab0c790aeae19f'),
 'leaf50':('proof-leaf-manifest-20260905-v1/defs-complete/manifest.json','fa42ce3fa8db5b928ffa69d3da338bf32f0720c60d22f78a2776e9ba9000daca'),
 'hier17':('proof-multistep-manifest-20260905-v2/manifest.json','c186ddf0007c5b5adfdc345a06feb777a89746160cf9041b875a8655ed1eb344'),
 'whole6':('proof-breadth-controls-20260905-v1/manifest.json','23d15fba5fcb08e8d8436d02deb727a34976bc220e8d66ec7bc333728949627e'),
 'new26':('proof-breadth26-controls-20260905-v1/manifest.json','fa9891e67e8c099e2956d5d9f78a29780f186c132a6446d0ed02e5dc89487526')}
CUDA_INPUTS=(
 ('proof-cuda-cycle-20260905-v2','leaf50','e5c52dec0561cf8468e4abb77371fe006c034a095830efb2217feb09f8f79f41','64c27f262f9eba2694ba05a428aaba66ddf3af12dd0e92cc6537cd10a41263f9'),
 ('proof-cuda-hierarchical-cycle-20260905-v2','hier17','90f3709973c3c65c27d4427237d83468f12d589fa1558390091d7e2f51410ac7','b105e352f5cfdda5fe878ea5d9760a5bc220d17c0c7f511a875577acbff00e06'),
 ('proof-cuda-whole-cycle-20260905-v2','whole6','dc1284f501de735fcbf2d0523132b8e13420034d0a92750e275d337491b408e1','78c3dd57247edde10c50dc12e6e8a3ca2f720f0a98f6d0eca901c359c13cfeff'),
 ('proof-cuda-broader-cycle-20260905-v1','broader32','a282ce32acfe48d3b1d1c3ca66dbcce34b301cd63f45cf347d061e66d7eb4d61','5adb8315e8d9563fbf42a40fa5055d4e4b3b7f3e3c6e4ec7fe889b05ca030860'),
 ('proof-cuda-exposure-cycle-20260905-v1','broader32','4e830b736c95aa18fcc627934d17fe91b9229f1c4ab755f92ed4779e5c11886b','5adb8315e8d9563fbf42a40fa5055d4e4b3b7f3e3c6e4ec7fe889b05ca030860'))
EXTRA_INPUTS={
 'proof-family-manifest-20260905-v3/manifest.json':'58196ff75d174ff97ec6b70306c01ab709b814688422629f9424fee4801e4ce7',
 'proof-training-cycle-20260905-v1/training/config.json':'fa3c8be1c619eddf6495ea64c1b4910f10b72db172c7b2e8aa8966502be0acaa',
 'proof-multistep-cycle-20260905-v1/training/config.json':'57b543a0fcb1f22b0555a17918425561cf0b918ab7195db8962fde28b3fc79a6',
 'proof-candidate-rl-20260905-v1/config.json':'8e506e4b5441f0ab6a10aa3216f020aa56be5f1152fbe23d7de9e534777bdc5b',
 'proof-candidate-rl-20260905-v1/frozen.json':'0c5a9d23e74afa55a6b03e4ebb865b93858bef3efa10f9b81436663fc9167e63'}
IMPLEMENTATION=('tools/proof_fresh_selection.py','tools/proof_fresh_controls.py','tools/proof_breadth_manifest.py',
 'tools/proof_breadth26_manifest.py','tools/proof_whole_packet.py','tools/proof_hierarchical_packet.py',
 'tools/proof_original18.py','tools/proof_source_scope.py','tools/proof_family_manifest.py',
 'tools/proof_cuda_train.py','tools/proof_cuda_eval.py','tools/proof_sequence_train.py',
 'tools/proof_candidate_rank.py','tools/proof_repair_pilot.py','harness/proof_fragment_check.py',
 'harness/proof_full_fragment_check.py','harness/runner.py','harness/corpora.py')

EVAL_IDS=['fresh-'+Path(p).parent.name+'-'+Path(p).stem+'-'+name for p,name,*_ in SELECTION]


def checked(path,expected):
    raw=Path(path).read_bytes()
    if sha(raw)!=expected:raise ValueError('Pinned input changed: '+str(path))
    return raw


def source(relative):
    if relative not in HASHES:raise ValueError('Unfrozen custom source: '+relative)
    path=SOURCE_ROOT/relative;raw=checked(path,HASHES[relative])
    blob=subprocess.check_output(['git','-C',str(EXAMPLES),'show',COMMIT+':specifications/'+relative],timeout=30)
    if raw!=blob:raise ValueError('Source differs from pinned Git commit')
    return path,raw.decode()


def closure(path,text):
    deps={};standard={};visiting=set()
    def visit(current,raw):
        for name in legacy.imports(raw):
            local=current.parent/(name+'.tla')
            if local.is_file():
                p,body=source(str(local.relative_to(SOURCE_ROOT)))
                assumptions=legacy.check_dependency(body)
                if str(p) in visiting:raise ValueError('Cyclic custom dependency')
                if str(p) not in deps:
                    visiting.add(str(p));visit(p,body);visiting.remove(str(p))
                    deps[str(p)]=dict(sha256=sha(body.encode()),assumptions=assumptions)
            else:
                p=next((Path(r)/(name+'.tla') for r in legacy.TLA_LIBRARY.split(':') if (Path(r)/(name+'.tla')).is_file()),None)
                if p is None:
                    if name not in {'Naturals','Integers','Reals','Sequences'}:raise ValueError('Unresolved installed module: '+name)
                    standard['tlapm-builtin:'+name]=file_sha(legacy.TLAPM)
                else:standard[str(p.resolve())]=file_sha(p)
    visit(path,text)
    return deps,standard


def training_inputs():
    provenance={};manifests={};extras={}
    def read(name,expected):
        path=ROOT/'results/runs'/name;raw=checked(path,expected);provenance[str(path)]=expected
        return json.loads(raw)
    for key,(name,h) in MANIFESTS.items():manifests[key]=read(name,h)
    ids={key:[t['id'] for t in d['tasks'] if t['split']=='train'] for key,d in manifests.items()}
    ids['broader32']=ids['whole6']+ids['new26']
    for key,n in [('earlier6',6),('leaf50',50),('hier17',17),('whole6',6),('new26',26)]:
        if len(ids[key])!=n or len(set(ids[key]))!=n:raise ValueError('Training population mismatch')
    for run,key,config_sha,packet_sha in CUDA_INPUTS:
        config=read(run+'/training/config.json',config_sha);packet=read(run+'/training/train.json',packet_sha)
        expected_manifest=(digest([MANIFESTS['whole6'][1],MANIFESTS['new26'][1]]) if key=='broader32' else MANIFESTS[key][1])
        if (config.get('input_sha256')!=packet_sha or config.get('train_ids')!=ids[key]
                or packet.get('train_ids')!=ids[key] or packet.get('manifest_sha256')!=expected_manifest
                or [r['id'] for r in packet['rows']]!=ids[key]):
            raise ValueError('Actual training config/packet provenance mismatch')
    for name,h in EXTRA_INPUTS.items():extras[name]=read(name,h)
    for path,key in [('proof-training-cycle-20260905-v1/training/config.json','earlier6'),
                     ('proof-multistep-cycle-20260905-v1/training/config.json','hier17'),
                     ('proof-candidate-rl-20260905-v1/config.json','hier17')]:
        if extras[path]['manifest_sha256']!=MANIFESTS[key][1] or extras[path]['train_ids']!=ids[key]:
            raise ValueError('Historical SFT/RL population mismatch')
    old={t['id']:t for t in manifests['earlier6']['tasks']}
    for t in extras['proof-family-manifest-20260905-v3/manifest.json']['tasks']:
        if t['split']=='train' and any(t[k]!=old[t['id']][k] for k in ('prefix','reference_fragment','suffix','source_sha256')):
            raise ValueError('Corrected earlier6 changed actual training content')
    rl=extras['proof-candidate-rl-20260905-v1/frozen.json']
    if [t['id'] for t in rl]!=ids['hier17'] or extras['proof-candidate-rl-20260905-v1/config.json']['frozen_sha256']!=EXTRA_INPUTS['proof-candidate-rl-20260905-v1/frozen.json']:
        raise ValueError('RL frozen input mismatch')
    return manifests,rl,provenance


def exclusions():
    manifests,rl,provenance=training_inputs()
    sources,goals,original,_=legacy.exclusions(manifests['hier17']);provenance.update(original)
    rawpaths={};trainrows=[]
    # Preserve historical repeats so the research316/901 audit is reproducible.
    for key in ('leaf50','hier17','whole6','new26','earlier6'):
        for t in manifests[key]['tasks']:
            if t['split']!='train':continue
            trainrows.append(t)
            for p in [t['source_path']]+t.get('dependencies',[]):
                expected=t['source_sha256'] if p==t['source_path'] else t.get('dependency_sha256',{}).get(p)
                if expected is None:raise ValueError('Training dependency lacks exact hash')
                rawpaths[p]=checked(p,expected).decode();provenance[p]=expected
            assembled=t['prefix']+t['reference_fragment']+t['suffix']
            if t.get('assembled_sha256') and sha(assembled.encode())!=t['assembled_sha256']:raise ValueError('Training assembly changed')
            sources.append(('TRAIN-assembled:'+t['id'],assembled))
            goals.extend(('TRAIN-assembled:'+t['id']+':'+n,b) for n,b in legacy.goal_bodies(assembled))
            if t.get('target_goal'):goals.append(('TRAIN-target:'+t['id'],t['target_goal']))
    for p,raw in sorted(rawpaths.items()):
        sources.append(('TRAIN-source:'+p,raw));goals.extend(('TRAIN-source:'+p+':'+n,b) for n,b in legacy.goal_bodies(raw))
    libraries={}
    for t in rl:
        goals.append(('RL-target:'+t['id'],t['target_goal']))
        for field in ('visible_facts','imported_facts'):
            goals.extend(('RL-context:'+t['id']+':'+f['name'],f['statement']) for f in t['context'].get(field,[]))
        for p,h in t['context']['library_sha256'].items():
            if p in libraries and libraries[p]!=h:raise ValueError('Inconsistent RL library hashes')
            libraries[p]=h
    for p,h in sorted(libraries.items()):
        sources.append(('RL-library:'+p,checked(p,h).decode()));provenance[p]=h
    counts=dict(source_entries=len(sources),goal_entries=len(goals),distinct_train_ids=len({t['id'] for t in trainrows}),
                training_rows_with_historical_repeats=len(trainrows),train_raw_paths=len(rawpaths))
    if counts!=dict(source_entries=316,goal_entries=901,distinct_train_ids=99,training_rows_with_historical_repeats=105,train_raw_paths=17):
        raise ValueError('Research exclusion count discrepancy: '+repr(counts))
    return sources,goals,provenance,counts


def construct():
    sources,goals,provenance,counts=exclusions();tasks=[]
    for ident,(relative,name,begin,proof,end) in zip(EVAL_IDS,SELECTION):
        path,text=source(relative);deps,standard=closure(path,text)
        task=legacy.extract(text,name,begin,proof,end)
        task.update(id=ident,split='fresh_evaluation',theorem_name=name,module_name=path.stem,
            source_family='tlaplus/Examples:'+relative.split('/')[0],source_path=str(path),source_sha256=sha(text.encode()),
            source_commit=COMMIT,source_repository='https://github.com/tlaplus/Examples',dependencies=list(deps),
            dependency_sha256={p:d['sha256'] for p,d in deps.items()},dependency_audit=deps,
            standard_library_sha256=standard,training_authorized=False)
        audit={'source':legacy.compare(text,sources),
               'assembled':legacy.compare(task['prefix']+task['reference_fragment']+task['suffix'],sources),
               'goal_body':legacy.compare(task['target_goal'],goals)}
        audit.update({'dependency:'+p:legacy.compare(Path(p).read_text(),sources) for p in deps})
        task['decontamination']=audit
        task['context_goal_audit']={n:legacy.compare(b,goals) for n,b in legacy.goal_bodies(task['prefix']) if n!=name}
        task['rejection_reasons']=[task['contract_rejection']] if task['contract_rejection'] else []
        if any(v['max_jaccard']>=.65 or v['exact_normalized'] for v in audit.values()):
            task['rejection_reasons'].append('source/assembled/goal/dependency overlap')
        wrong_conclusion(task)
        tasks.append(task)
    for i,t in enumerate(tasks):
        t['within_selection_goal_audit']=legacy.compare(t['target_goal'],[(other['id'],other['target_goal']) for j,other in enumerate(tasks) if i!=j])
        v=t['within_selection_goal_audit']
        if v['max_jaccard']>=.65 or v['exact_normalized']:t['rejection_reasons'].append('within-selection goal overlap')
    return dict(schema_version=1,kind='fresh14_evaluation_selection_only',source_commit=COMMIT,
        requested_evaluation=14,requested_train=0,training_authorized=False,evaluation_authorized=False,
        fragment_contract=legacy.CONTRACT_VERSION,control_budget=BUDGET,tasks=tasks,
        exclusion_sha256=provenance,exclusion_counts=counts,
        reference_scope='Isolated local evaluation controls only; never inference or training',
        decontamination_threshold=.65,context_overlap_disclosure='Preceding human proofs remain; lexical novelty is not semantic/pretraining novelty')


def identity(selection=None):
    current=construct()
    if selection is not None and selection_digest(selection)!=selection_digest(current):raise ValueError('Selection changed')
    result=runtime_identity()
    paths={ROOT/p for p in IMPLEMENTATION}|{SOURCE_ROOT/p for p in HASHES}
    for name,h in TOKENIZER_HASHES.items():checked(TOKENIZER/name,h)
    paths.update(TOKENIZER/name for name in TOKENIZER_HASHES)
    paths.update(Path(p) for p in current['exclusion_sha256'] if Path(p).is_file())
    result.update(fresh_selection_sha256=selection_digest(current),
        fresh_inputs_sha256={str(p):file_sha(p) for p in sorted(paths)},
        fresh_exclusion_sha256=current['exclusion_sha256'])
    return result


def export_prompts(selection,tokenizer_path=TOKENIZER):
    import transformers
    for name,h in TOKENIZER_HASHES.items():checked(tokenizer_path/name,h)
    tokenizer=transformers.AutoTokenizer.from_pretrained(tokenizer_path,local_files_only=True)
    rows=[];evidence=[]
    for task,expected in zip(selection['tasks'],EXPECTED_PROMPT_COUNTS):
        prompt=whole_prompt(task);row=dict(id=task['id'],split='fresh_evaluation',prompt=prompt,prompt_sha256=sha(prompt.encode()))
        encoded=encode_prompt(tokenizer,row)
        if encoded['input_tokens']!=expected or encoded['input_tokens']+3072>8192:raise ValueError('Fresh prompt token feasibility changed')
        evidence.append({k:encoded[k] for k in ('id','input_tokens','input_token_ids_sha256','rendered_prompt_sha256')})
        rows.append(row)
    if [r['id'] for r in rows]!=EVAL_IDS:raise ValueError('Exact14 prompt population required')
    return dict(schema=1,requested_evaluation=14,training_authorized=False,reference_fragments_exported=False,
        selection_sha256=selection_digest(selection),tasks=rows,token_feasibility=dict(max_tokens=8192,max_new_tokens=3072,
            tokenizer_files=TOKENIZER_HASHES,rows=evidence))


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
    p.add_argument('--controls',action='store_true');a=p.parse_args()
    selection=construct();prompts=export_prompts(selection)
    a.output.mkdir(parents=True,exist_ok=False)
    dump(a.output/'selection.json',selection);dump(a.output/'prompts.json',prompts)
    dump(a.output/'config.json',dict(hypothesis='All14 prospective evaluation tasks admit exact positive and conclusion-only FALSE controls',
        measurement='Strict uncached TLAPS; all positive obligations and intended single FALSE failure',
        budget=BUDGET,training_authorized=False,model_sampling_authorized=False,
        stop='All28 controls or1000seconds total; keep all14 outcomes and diagnose failed controls without shrinking population'))
    for name in IMPLEMENTATION:
        path=a.output/'code'/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes((ROOT/name).read_bytes())
    if a.controls:
        from tools.proof_fresh_controls import controls
        result=controls(selection,a.output,seconds=1000,timeout=30,identity=lambda:identity(selection))
        if not result['evaluation_authorized']:raise SystemExit(1)


if __name__=='__main__':main()
