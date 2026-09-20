"""No verifier/optimizer execution: broader packet structure and artifact audits."""
import copy
import json
from pathlib import Path
import subprocess
import sys

import pytest

from tools import proof_broader_packet as broader


@pytest.fixture
def prompts():
    rows=[dict(id=i,split='train' if i in broader.TRAIN_IDS else 'development',
        prompt='prompt '+i,prompt_sha256=broader.sha(('prompt '+i).encode())) for i in broader.TRAIN_IDS+broader.DEV_IDS]
    return dict(schema=1,manifest_sha256=broader.MANIFEST_SHA256,
        source_manifest_sha256=broader.SOURCE_MANIFEST_SHA256.copy(),tasks=rows,requested_tasks=36,
        reference_fragments_exported=False,candidates_exported=False)


@pytest.fixture
def packet(prompts):
    families=[name for name,count in broader.FAMILY_COUNTS.items() for _ in range(count)]
    rows=[];controls=[];tokens=[]
    for index,prompt in enumerate(prompts['tasks']):
        token=dict(id=prompt['id'],prompt_tokens=100,input_token_ids_sha256='a'*64)
        tokens.append(token)
        if index>=32:continue
        response='<1>1. TRUE\n<1> QED BY <1>1' if index<15 else 'BY previous'
        rows.append(dict(prompt,source_family=families[index],source_sha256='b'*64,assembled_sha256='c'*64,
                         response=response,response_sha256=broader.sha(response.encode())))
        token.update(response_tokens=20,total_tokens=120,training_inference_prefix_equal=True,
            actual_eos_verified=True,terminal_eos_token_id=128009,response_token_ids_sha256='d'*64,training_token_ids_sha256='e'*64)
        for label in ('reference','wrong_conclusion'):
            good=label=='reference'
            control=dict(id=prompt['id'],control=label,proved=1 if good else 0,total=1 if good else 0,
                status='pass' if good else 'verifier_reject',returncode=0 if good else 10,certified=good,
                candidate_sha256='c'*64 if good else 'd'*64,input_sha256='e'*64,log_sha256='f'*64,
                dependency_sha256={},command=['/tlapm','--strict','--nofp','Proof.tla'])
            if prompt['id'] in broader.NEW_IDS:control['negative_contract']='preserve-assumptions-conclusion-only-FALSE-v1'
            controls.append(control)
    current=dict(original6={'runtime':'same'},broader26={'negative_contract':'preserve-assumptions-conclusion-only-FALSE-v1'})
    identity={key:copy.deepcopy(current) for key in ('before','after','controlled')}
    evidence=dict(manifest_sha256=broader.MANIFEST_SHA256,source_manifest_sha256=broader.SOURCE_MANIFEST_SHA256.copy(),
        controls_sha256=broader.CONTROLS_SHA256.copy(),strict_controls_verified=True,controls=controls,
        original18_reference_text_exported=False,threshold=.65,canonical_matches=0,max_jaccard=.4,
        verifier_identity=identity,verifier_identity_sha256=broader.digest(identity),
        populations=dict(original18=list(map(str,range(18))),official119=list(map(str,range(119))),
            official30=list(map(str,range(30))),development=broader.DEV_IDS[:]),
        selection_sha256={'original6':'a'*64,'broader26':'b'*64},raw_source_sha256={'source':'c'*64},
        implementation_sha256={path:'d'*64 for path in broader.IMPLEMENTATION},exclusion_audit_sha256={'both':'e'*64})
    return dict(schema_version=1,packet_kind=broader.KIND,algorithm=broader.ALGORITHM,split='train',training_ready=True,
        evaluation_responses_exported=False,manifest_sha256=broader.MANIFEST_SHA256,
        source_manifest_sha256=broader.SOURCE_MANIFEST_SHA256.copy(),train_ids=broader.TRAIN_IDS[:],
        task_shape=broader.SHAPE.copy(),rows=rows,evidence=evidence,
        token_feasibility=dict(max_tokens=8192,max_new_tokens=3072,tokenizer_files=broader.TOKENIZER_HASHES.copy(),
                              terminal_eos_token_id=128009,rows=tokens))


def test_remote_stdlib_import():
    result=subprocess.run([sys.executable,'-S','-c','from tools.proof_broader_packet import validate_training_packet'],
                          cwd=broader.ROOT,capture_output=True,text=True)
    assert result.returncode==0,result.stderr


def test_complete_contract(prompts,packet):
    assert len(broader.validate_export(prompts))==36
    assert len(broader.validate_training_packet(packet))==32


@pytest.mark.parametrize('mutation',[
    lambda p:p['tasks'].pop(),lambda p:p['tasks'].reverse(),
    lambda p:p['tasks'][0].update(response='leak'),lambda p:p['tasks'][32].update(split='train'),
    lambda p:p.update(reference_fragments_exported=True),lambda p:p['tasks'][0].update(prompt='changed'),
    lambda p:p['source_manifest_sha256'].update(broader26='a'*64),
])
def test_export_rejects_drift(prompts,mutation):
    mutation(prompts)
    with pytest.raises(ValueError):broader.validate_export(prompts)


@pytest.mark.parametrize('mutation',[
    lambda p:p.update(packet_kind='frozen6_whole_target_proofs'),
    lambda p:p['rows'].pop(),lambda p:p['rows'].reverse(),
    lambda p:p['rows'][0].update(split='development'),lambda p:p['rows'][0].update(extra='leak'),
    lambda p:p['rows'][0].update(response='changed'),lambda p:p['rows'][0].update(source_family='unknown'),
    lambda p:p['task_shape'].update(hierarchical_spans=14),lambda p:p.update(training_ready=False),
    lambda p:p.update(evaluation_responses_exported=True),
    lambda p:p['source_manifest_sha256'].update(original6='b'*64),
    lambda p:p['evidence'].update(max_jaccard=.65),lambda p:p['evidence'].update(max_jaccard=float('nan')),
    lambda p:p['evidence']['populations']['original18'].pop(),lambda p:p['evidence']['populations']['development'].reverse(),
    lambda p:p['evidence']['controls'].pop(),lambda p:p['evidence']['controls'][0].update(total=2),
    lambda p:p['evidence']['controls'][1].update(returncode=3),
    lambda p:p['evidence']['controls'][13].update(negative_contract='discard-bindings'),
    lambda p:p['evidence']['controls'][0].update(candidate_sha256='f'*64),
    lambda p:p['evidence']['controls'][0].update(command=['tlapm','Proof.tla']),
    lambda p:p['evidence']['verifier_identity']['after']['original6'].update(changed=True),
    lambda p:p['evidence']['implementation_sha256'].pop('tools/proof_broader_packet.py'),
    lambda p:p['token_feasibility']['rows'][0].update(actual_eos_verified=False),
    lambda p:p['token_feasibility']['rows'][0].update(terminal_eos_token_id=128001),
    lambda p:p['token_feasibility']['rows'][0].update(training_inference_prefix_equal=False),
    lambda p:p['token_feasibility']['rows'][0].update(response_tokens=3073),
    lambda p:p['token_feasibility']['rows'][35].update(prompt_tokens=5121),
    lambda p:p['token_feasibility']['tokenizer_files'].update(**{'tokenizer.json':'f'*64}),
])
def test_training_rejects_drift(packet,mutation):
    mutation(packet)
    with pytest.raises(ValueError):broader.validate_training_packet(packet)


def test_real_source_population_and_unchanged_dev():
    from tools.proof_whole_packet import export_tasks as original_export
    packet,tasks=broader.export_tasks()
    original,_=original_export(broader.MANIFEST6)
    assert packet['tasks'][:6]==original['tasks'][:6]
    assert packet['tasks'][32:]==original['tasks'][6:]
    assert len(tasks)==36
    assert len({t['source_family'] for t in tasks[:32]})==7
    assert sum(bool(__import__('re').search(r'(?m)^\s*<1>',t['reference_fragment'])) for t in tasks[:32])==15


def test_all52_new_raw_artifacts_without_checker():
    manifests=broader.load_manifests();data=manifests['broader26']
    controls=json.loads((broader.MANIFEST26.parent/'controls.json').read_text())
    bindings=[broader.broader_control_binding(task,controls[2*i+j],label,data['verifier_identity'])
        for i,task in enumerate(data['tasks'][:26]) for j,label in enumerate(('reference','wrong_conclusion'))]
    assert len(bindings)==52
    assert sum(r['certified'] for r in bindings)==26


def test_assumptions_not_dropped(tmp_path):
    from tools.proof_breadth26_manifest import wrong_conclusion
    manifest=broader.load_manifests()['broader26'];task=manifest['tasks'][0]
    assert 'ASSUME' in wrong_conclusion(task) and 'PROVE FALSE' in wrong_conclusion(task)
    row=json.loads((broader.MANIFEST26.parent/'controls.json').read_text())[1]
    original=Path(row['workdir']);candidate=Path(row['candidate_path'])
    for name in (candidate.name,'input.json'):(tmp_path/name).write_bytes((original/name).read_bytes())
    (tmp_path/'tlapm.log').write_text(row['output'])
    inp=json.loads((tmp_path/'input.json').read_text())
    start,end=task['goal_offsets']
    inp['prefix']=task['prefix'][:start]+' FALSE\n'+task['prefix'][end:]
    (tmp_path/'input.json').write_text(json.dumps(inp))
    row.update(workdir=str(tmp_path),candidate_path=str(tmp_path/candidate.name))
    with pytest.raises(ValueError,match='immutable input'):
        broader.broader_control_binding(task,row,'wrong_conclusion',manifest['verifier_identity'])
