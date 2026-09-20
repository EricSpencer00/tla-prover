"""Frozen TRAIN4 proof packet: portable exact prompts, separately audited references.

Local export rechecks all raw controls and protected-data evidence. Portable
validation accepts only the pinned complete packet, without requiring verifier
installations or reference proofs on the generation host.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
NAMES=('FrontDef','Lemma2','Lemma2a','Lemma3')
TRAIN_IDS=tuple('sumsequence-'+name for name in NAMES)
KIND='checked_sumsequence_train4'
MANIFEST_SHA256='57cbaa474074249210bd64ff801fe45fe6df6ca17aff365dcd438949d645ff01'
POPULATION_SHA256='67c6e7dd95a95883de85c4482c106678e9322918b474e6bbf2bcdb37215b53b9'
PACKET_SHA256='4b5a95633c5fd5ab01562c946229262678f3606eb7bf9aaf7a6e593ae977c318'
RUNS={
 'proof-sumsequence-controls-20260906-v2':{
 'config':'ef32f2c68fc75544a0e4ba6f9331d8d0143c68b7b156b6dd594ce6f9516703cf',
 'summary':'4a87ebd426ad13adedc7465b604da6485b43056aec9faaa64350de3cbf50d7ab',
 'row-1':'900bbc29885d3a1391166f76a7940a167a1f309b1d68121e66720e451db9e6f5',
 'row-2':'0ac746ef4d8736d033052bcc53afba0d0264fad90527946448ec19f47c057be4',
 'row-3':'dcde505ac17ff2df1a2f1ceeecef446e902f378f8293f0f10cd11763fc260b23',
 'row-4':'b72117ee8b7e0900f92bc24a94ba4d6de40062603644e4c42f90c163331cb603'},
 'proof-sumsequence-lemma2a-20260906-v1':{
 'config':'6a9c266dd1596a5dc918436ef413398852d9720cc3a46d118a6e9a298b4bf6ff',
 'summary':'389cd69d71cc3674b4ef6e74e31eb2ab36a75579d134e6477e6832093d1f0c76',
 'row-1':'edaf28a00b7370944be8df6b30a1f648f626aa8de11ffca2f17783fa1ae065b5',
 'row-2':'89dce00813766248c856aaec8560f595863de79808b2177e499ff9bcf053f39f'},
 'proof-sumsequence-lemma3-20260906-v1':{
 'config':'3f32fbdb659fa897a4e0509d52b24e2c00cadf75cfbbd127b49d9143bf394b60',
 'summary':'bb71b16c28de4aa6d5e6539f7be68b8b3de897995f9fae3c3e0aa75aae0a4e02',
 'row-1':'c9f24d4b8c85c817d8623b8945bef0aff5798a2cd970fd4e1a662e993c32aa4b',
 'row-2':'e807d3258095f5535f132db7c5ad1f0b4b49a2fc3874918505538c6dabbaeb02'}}
REPORTS={
 'proof-sumsequence-exclusions-20260906-main-v1':'2556d60b952f69eaf4d4ebe72bbcfb44f1c1059df5a5044156eb9ebf224f3146',
 'proof-sumsequence-extended-exclusions-20260906-v1':'16a3570eaf6fb7d8ef9aceb720cf7d06b80c0fbd8a395a5370689fbafedbe4f3'}
PROCESSES={
 'proof-sumsequence-controls-20260906-v2/row-1':'789c73cea45be247960d461be0753b9e13769836e1fd7c5a40009e8a32d25c1c',
 'proof-sumsequence-controls-20260906-v2/row-2':'a4575c7c48a483a85e3013ba56ed08eb3909958c2acf3b3cdb5487d6b1c87b02',
 'proof-sumsequence-controls-20260906-v2/row-3':'2123b5c4fb9c3ddcc2d5133bdf99c831af76e0095f01113515306c27eb56f33d',
 'proof-sumsequence-controls-20260906-v2/row-4':'85d1d6e311bd4b025ce2cd9bac14023f73ff389a4d56be02c01aacf353ad9589',
 'proof-sumsequence-lemma2a-20260906-v1/row-1':'25f964ae2ee7097502cca802ded7e3c636daaf872d82e97ba41ee3ab81802d1c',
 'proof-sumsequence-lemma2a-20260906-v1/row-2':'23bf13f101d6ee9564709d91969f94bc3ba91d5d8092f5043a8a46d7a2d8f6dd',
 'proof-sumsequence-lemma3-20260906-v1/row-1':'b5dfb2d0cd11f2c4d187a39d81332d87be20500902b559651555c2260c2b635e',
 'proof-sumsequence-lemma3-20260906-v1/row-2':'2a88a35ffe6693ddfd7f3148cdfe592b537df3ff0e8b78164e1fab924b458c85'}


def sha(raw):return hashlib.sha256(raw).hexdigest()
def digest(value):return sha(json.dumps(value,sort_keys=True,separators=(',',':')).encode())


def checked(path,expected):
    raw=Path(path).read_bytes()
    if sha(raw)!=expected:raise ValueError('Frozen evidence hash mismatch: '+str(path))
    return raw


def static_tasks():
    from tools import proof_sumsequence_controls as base
    from tools import proof_sumsequence_lemma2a as second
    from tools import proof_sumsequence_lemma3 as third
    originals=base.discover()['tasks']
    a=second.task();a['reference_fragment']='OBVIOUS\n'
    tasks=[]
    for name,source in zip(NAMES,[originals[0],originals[1],a,third.task()]):
        task={k:source[k] for k in ('prefix','negative_prefix','reference_fragment','suffix','statement','theorem_name')}
        if task['theorem_name']!=name:raise ValueError('Static task inventory changed')
        task.update(id='sumsequence-'+name,split='train',source_path=str(base.SOURCE),
            source_sha256=base.SOURCE_SHA,source_commit=base.COMMIT,
            source_family='tlaplus/Examples:LoopInvariance',dependencies=[],dependency_sha256={},
            assembled_sha256=sha((task['prefix']+task['reference_fragment']+task['suffix']).encode()))
        tasks.append(task)
    return tasks


def _static_manifest():
    return dict(schema=1,kind=KIND,tasks=static_tasks(),discovered=5,
        inventory=[dict(id='sumsequence-'+name,status='checked_train' if name in NAMES else 'pending_prerequisite_closure')
                   for name in (*NAMES,'Lemma4')],
        admitted_train=4,development_tasks=0,control_evidence=RUNS,exclusion_evidence=REPORTS,
        owned_process_evidence=PROCESSES,
        model_training_performed=False,
        scope='Four human-proved TRAIN tasks, not independent families, model success, generalization, or optimizer admission')


def _packet(manifest):
    from tools.proof_whole_packet import task_prompt
    rows=[]
    for task in manifest['tasks']:
        prompt=task_prompt(task)
        rows.append(dict(id=task['id'],split='train',prompt=prompt,prompt_sha256=sha(prompt.encode())))
    return dict(schema=1,kind=KIND,manifest_sha256=digest(manifest),population_sha256=digest(rows),
        tasks=rows,requested_tasks=4,reference_fragments_exported=False,candidates_exported=False)


def validate_export(packet):
    """Portable; reject any altered task, prompt, provenance, or reference field."""
    keys={'schema','kind','manifest_sha256','population_sha256','tasks','requested_tasks',
          'reference_fragments_exported','candidates_exported'}
    if (not isinstance(packet,dict) or set(packet)!=keys or type(packet['schema']) is not int
        or packet['schema']!=1 or packet['kind']!=KIND or type(packet['requested_tasks']) is not int
        or packet['requested_tasks']!=4 or packet['reference_fragments_exported'] is not False
        or packet['candidates_exported'] is not False or packet['manifest_sha256']!=MANIFEST_SHA256
        or packet['population_sha256']!=POPULATION_SHA256):
        raise ValueError('Frozen reference-free packet contract mismatch')
    rows=packet['tasks']
    if not isinstance(rows,list) or len(rows)!=4:raise ValueError('Exact TRAIN4 required')
    for expected,row in zip(TRAIN_IDS,rows):
        if (not isinstance(row,dict) or set(row)!={'id','split','prompt','prompt_sha256'}
            or row['id']!=expected or row['split']!='train' or not isinstance(row['prompt'],str)
            or sha(row['prompt'].encode())!=row['prompt_sha256']):
            raise ValueError('Exact ordered TRAIN prompt fields required')
    if digest(rows)!=POPULATION_SHA256 or digest(packet)!=PACKET_SHA256:
        raise ValueError('Immutable prompt/provenance content changed')
    return rows


def audit_row(task,row,*,wrapped):
    from harness.proof_ladder_check import _audit_tlaps
    from harness.proof_owned_process import as_runner_tuple
    from tools.proof_sumsequence_controls import intended_false_failure
    label=row.get('control')
    if label not in ('reference','false_conclusion'):raise ValueError('Unknown control label')
    prefix=task['prefix' if label=='reference' else 'negative_prefix'];result=row['result']
    _audit_tlaps(result,prefix,task['reference_fragment'],task['suffix'],task['theorem_name'],{})
    work=Path(result['workdir'])
    saved=json.loads((work/'process.json').read_bytes())
    if wrapped:
        if saved['command']!=result['command'] or saved['cwd']!=str(work) or saved['timeout']!=30:
            raise ValueError('Wrapped owned process identity mismatch')
        process=saved['process']
    else:process=saved
    if (process['command']!=result['command'] or process['cwd']!=str(work)
        or as_runner_tuple(process)!=tuple(result[k] for k in ('returncode','output','seconds','timed_out'))
        or not all(process.get(k) is True for k in ('execution_complete','cleanup_complete','output_complete'))
        or process.get('timed_out') is not False):
        raise ValueError('Incomplete or mismatched owned process')
    accepted=result['certified'] is True if label=='reference' else intended_false_failure(result)
    if not accepted or row.get('accepted') is not True:
        raise ValueError('Control does not establish intended outcome')


def audit_controls(tasks,runtime):
    from tools import proof_sumsequence_controls as base
    from tools import proof_sumsequence_lemma2a as second
    from tools import proof_sumsequence_lemma3 as third
    groups=((tasks[:2],base.file_identity()),(tasks[2:3],second.identity()),(tasks[3:],third.identity()))
    for index,((run,pins),(group,current)) in enumerate(zip(RUNS.items(),groups)):
        root=ROOT/'results/runs'/run
        values={key:json.loads(checked(root/(key+'.json'),value)) for key,value in pins.items()}
        config=values['config'];summary=values['summary']
        before=config['files' if index==0 else 'identity']
        after=summary['files_after' if index==0 else 'identity_after']
        if (before!=current or after!=current or config['runtime']!=runtime or summary['runtime_after']!=runtime
            or summary['identity_stable'] is not True or summary['within_budget'] is not True
            or summary['controls_admitted'] is not True or summary['attempted_controls']!=len(group)*2
            or summary['accepted_controls']!=len(group)*2):
            raise ValueError('Current control runtime/source/budget mismatch')
        if index==0:
            if config['manifest']!=base.discover():raise ValueError('Frozen discovery config changed')
        else:
            expected=second.task() if index==1 else third.task()
            if config['task']!=expected:raise ValueError('Frozen exact control task mismatch')
        for n,task in enumerate(group):
            for offset,label in enumerate(('reference','false_conclusion')):
                row=values[f'row-{2*n+offset+1}']
                if row['control']!=label or (index==0 and row['id']!=task['theorem_name']):
                    raise ValueError('Ordered control population changed')
                if index==1 and row.get('candidate')!='obvious':raise ValueError('Lemma2a proof changed')
                checked(Path(row['result']['workdir'])/'process.json',PROCESSES[run+f'/row-{2*n+offset+1}'])
                audit_row(task,row,wrapped=index==0)


def audit_exclusions():
    from tools import proof_sumsequence_exclusions as prior
    from tools import proof_sumsequence_extended_exclusions as extended
    sources,goals,paths,provenance=prior.population()
    for index,(run,pin) in enumerate(REPORTS.items()):
        report=json.loads(checked(ROOT/'results/runs'/run/'report.json',pin))
        for path,value in report['input_sha256'].items():checked(path,value)
        for path,value in report['sources_before'].items():checked(ROOT/path,value)
        if (report['sources_before']!=report['sources_after'] or report['protected_provenance']!=provenance
            or any(report['input_sha256'].get(path)!=value for path,value in paths.items())
            or report['source_entries']!=len(sources) or report['goal_entries']!=len(goals)
            or report['threshold']!=prior.THRESHOLD or report['overlap_keys']
            or report['lexical_exclusion_clear'] is not True):
            raise ValueError('Protected population evidence changed')
        checks={}
        def compare(label,text,pool,kind):
            value=prior.breadth.compare(text,pool)
            checks[label]=dict(value,queried_sha256=sha(text.encode()),protected_pool=kind,
                               overlap_exclusion=prior.overlap(value))
        if index==0:
            candidate=prior.discovery.discover()
            compare('original_source',prior.discovery.SOURCE.read_text(),sources,'sources')
            compare('Front_definition_source',prior.discovery.FRONT_SOURCE.read_text(),sources,'sources')
            compare('Front_definition',prior.discovery.FRONT,sources,'sources')
            for task in candidate['tasks']:
                bodies=prior.breadth.goal_bodies(task['statement'])
                if len(bodies)!=1 or bodies[0][0]!=task['id']:raise ValueError('Target inventory mismatch')
                compare(task['id']+':target_goal',bodies[0][1],goals,'goals')
                if task['control_eligible']:
                    compare(task['id']+':sanitized_assembly',task['prefix']+task['reference_fragment']+task['suffix'],sources,'sources')
                    compare(task['id']+':reference_fragment',task['reference_fragment'],sources,'sources')
                    for name,body in prior.breadth.goal_bodies(task['prefix']):
                        compare(task['id']+':context_goal:'+name,body,goals,'goals')
            front=candidate['tasks'][0]
            compare('Lemma2:prerequisite_FrontDef_statement_and_proof',front['statement']+front['reference_fragment'],sources,'sources')
        else:
            candidates=extended.candidates()
            if report['task_sha256']!=sha(json.dumps(candidates,sort_keys=True).encode()):
                raise ValueError('Extended assembly identity changed')
            checks=extended.compare_candidates(candidates,sources,goals)
            for name,text in (('original_source',prior.discovery.SOURCE.read_text()),
                ('Front_source',prior.discovery.FRONT_SOURCE.read_text()),('Front_definition',prior.discovery.FRONT)):
                compare(name,text,sources,'sources')
        if checks!=report['checks'] or any(row['overlap_exclusion'] for row in checks.values()):
            raise ValueError('Recomputed exact protected comparisons differ')


def manifest():
    from tools.proof_hierarchical_packet import runtime_identity
    value=_static_manifest()
    if digest(value)!=MANIFEST_SHA256:raise ValueError('Static manifest reconstruction changed')
    before=runtime_identity()
    audit_controls(value['tasks'],before)
    audit_exclusions()
    if runtime_identity()!=before:raise ValueError('Verifier runtime drift during admission')
    # Re-audit raw controls after exclusion work, including source identities.
    audit_controls(value['tasks'],before)
    return value


def export_tasks():
    value=manifest();packet=_packet(value);validate_export(packet)
    return packet,value['tasks']


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    output=parser.parse_args().output;output.mkdir(parents=True,exist_ok=False)
    try:
        value=manifest();packet=_packet(value);validate_export(packet)
    except BaseException as exc:
        with (output/'failure.json').open('x') as stream:
            json.dump(dict(error=type(exc).__name__+': '+str(exc),admitted_train=0),stream,indent=2)
        raise
    for name,data in (('manifest',value),('prompts',packet)):
        with (output/(name+'.json')).open('x') as stream:json.dump(data,stream,indent=2);stream.write('\n')
    with (output/'summary.json').open('x') as stream:
        json.dump(dict(admitted_train=4,discovered=5,pending=['Lemma4'],model_training_performed=False,
            manifest_sha256=MANIFEST_SHA256,population_sha256=POPULATION_SHA256,packet_sha256=PACKET_SHA256,
            manifest_file_sha256=sha((output/'manifest.json').read_bytes()),
            prompts_file_sha256=sha((output/'prompts.json').read_bytes())),stream,indent=2);stream.write('\n')


if __name__=='__main__':main()
