"""Whole-target packet contract tests; never run a verifier or optimizer."""
import copy
import json
from pathlib import Path
import subprocess
import sys

import pytest

from tools import proof_whole_packet as whole


@pytest.fixture
def export():
    rows=[dict(id=i,split='train' if i in whole.TRAIN_IDS else 'development',
               prompt='immutable prompt '+i,prompt_sha256=whole.sha(('immutable prompt '+i).encode()))
          for i in whole.TRAIN_IDS+whole.DEV_IDS]
    return dict(schema=1,manifest_sha256=whole.MANIFEST_SHA256,tasks=rows,requested_tasks=10,
                reference_fragments_exported=False,candidates_exported=False)


@pytest.fixture
def packet(export):
    rows=[]; controls=[]; counts=[]
    for index,item in enumerate(export['tasks']):
        counts.append(dict(id=item['id'],prompt_tokens=100,input_token_ids_sha256='b'*64))
        if index>=6:
            continue
        response='<1>1. TRUE\n<1> QED BY <1>1' if index<5 else 'BY previous'
        rows.append(dict(item,source_family=['lock','barriers','reachability'][min(index,2)],
                         source_sha256='a'*64,assembled_sha256='c'*64,
                         response=response,response_sha256=whole.sha(response.encode())))
        counts[-1].update(response_tokens=20,total_tokens=120,training_inference_prefix_equal=True)
        for label in ('reference','wrong_conclusion'):
            good=label=='reference'
            controls.append(dict(id=item['id'],control=label,proved=1 if good else 0,total=1,
                status='pass' if good else 'verifier_reject',returncode=0 if good else 10,certified=good,
                candidate_sha256='c'*64 if good else 'd'*64,input_sha256='e'*64,log_sha256='f'*64,
                dependency_sha256={},command=['/tlapm','--strict','--nofp','Proof.tla']))
    identity={key:dict(breadth_fragment_contract=whole.CONTRACT) for key in ('before','after','controlled')}
    evidence=dict(manifest_sha256=whole.MANIFEST_SHA256,strict_controls_verified=True,
        original18_reference_text_exported=False,threshold=.65,canonical_matches=0,max_jaccard=.1,
        populations=dict(original18=list(map(str,range(18))),official119=list(map(str,range(119))),
                         official30=list(map(str,range(30))),development=whole.DEV_IDS[:]),
        verifier_identity=identity,verifier_identity_sha256=whole.digest(identity),controls=controls,
        controls_sha256='a'*64,selection_sha256='b'*64,exclusion_audit_sha256='c'*64)
    return dict(schema_version=1,packet_kind=whole.KIND,algorithm=whole.ALGORITHM,split='train',training_ready=True,
        evaluation_responses_exported=False,manifest_sha256=whole.MANIFEST_SHA256,task_shape=whole.SHAPE.copy(),
        train_ids=whole.TRAIN_IDS[:],rows=rows,evidence=evidence,
        token_feasibility=dict(max_tokens=8192,max_new_tokens=3072,tokenizer_files=whole.TOKENIZER_HASHES.copy(),rows=counts))


def test_remote_import_is_stdlib_only(tmp_path):
    isolated=tmp_path/'packet.py'
    isolated.write_bytes(Path(whole.__file__).read_bytes())
    code='import runpy;runpy.run_path('+repr(str(isolated))+',run_name="remote_import")'
    result=subprocess.run([sys.executable,'-I','-S','-c',code],capture_output=True,text=True)
    assert result.returncode==0,result.stderr


def test_export_and_packet_valid(export,packet):
    assert len(whole.validate_export(export))==10
    assert len(whole.validate_training_packet(packet))==6


@pytest.mark.parametrize('mutation',[
    lambda x:x['tasks'].pop(),
    lambda x:x['tasks'].reverse(),
    lambda x:x['tasks'][0].update(response='LEAK'),
    lambda x:x['tasks'][0].update(split='development'),
    lambda x:x['tasks'][0].update(prompt='changed'),
    lambda x:x.update(reference_fragments_exported=True),
    lambda x:x.update(manifest_sha256='a'*64),
])
def test_export_fail_closed(export,mutation):
    mutation(export)
    with pytest.raises(ValueError):
        whole.validate_export(export)


@pytest.mark.parametrize('mutation',[
    lambda x:x.update(packet_kind='frozen17_hierarchical_repair_spans'),
    lambda x:x.update(training_ready=False),
    lambda x:x.update(evaluation_responses_exported=True),
    lambda x:x['task_shape'].update(whole_target_count=5),
    lambda x:x['rows'].pop(),
    lambda x:x['rows'][0].update(response='OBVIOUS'),
    lambda x:x['rows'][0].update(extra='leak'),
    lambda x:x['evidence'].update(max_jaccard=.65),
    lambda x:x['evidence'].update(max_jaccard=float('nan')),
    lambda x:x['evidence']['populations']['original18'].pop(),
    lambda x:x['evidence']['populations']['development'].reverse(),
    lambda x:x['evidence']['verifier_identity']['after'].update(changed=True),
    lambda x:x['evidence']['controls'].pop(),
    lambda x:x['evidence']['controls'][0].update(total=2),
    lambda x:x['evidence']['controls'][0].update(candidate_sha256='f'*64),
    lambda x:x['evidence']['controls'][1].update(returncode=3),
    lambda x:x['evidence']['controls'][1].update(certified=True),
    lambda x:x['evidence']['controls'][0].update(command=['tlapm','Proof.tla']),
    lambda x:x['token_feasibility']['rows'][0].update(training_inference_prefix_equal=False),
    lambda x:x['token_feasibility']['rows'][0].update(response_tokens=3073),
    lambda x:x['token_feasibility']['rows'][9].update(prompt_tokens=5121),
    lambda x:x['token_feasibility']['tokenizer_files'].update(**{'tokenizer.json':'f'*64}),
])
def test_training_fail_closed(packet,mutation):
    mutation(packet)
    with pytest.raises(ValueError):
        whole.validate_training_packet(packet)


def test_prompt_contract_and_unchanged_development():
    from tools.proof_repair_pilot import prompt_for,with_dependency_context
    task=dict(prefix='---- MODULE X ----\nTHEOREM T == TRUE\n',suffix='\n====\n',dependencies=[],split='train')
    prompt=whole.task_prompt(task)
    assert 'entire missing TLA+ proof' in prompt
    assert 'DEFINE' in prompt and 'immutable' in prompt
    assert task['prefix']+'<PROOF_HOLE>'+task['suffix'] in prompt
    task['split']='development'
    assert whole.task_prompt(task)==prompt_for(with_dependency_context(task))


def test_real_controls_reclassified_without_checker():
    if not whole.MANIFEST.exists():
        pytest.skip('local append-only control artifacts unavailable')
    manifest=whole.load_manifest(whole.MANIFEST)
    controls=json.loads((whole.MANIFEST.parent/'controls.json').read_text())
    bindings=[]
    for index,task in enumerate(manifest['tasks'][:6]):
        for offset,label in enumerate(('reference','wrong_conclusion')):
            bindings.append(whole.control_binding(task,controls[2*index+offset],label,manifest['verifier_identity']))
    assert len(bindings)==12
    assert sum(x['certified'] for x in bindings)==6
    altered=copy.deepcopy(controls[1]);altered['output']='Parse error'
    with pytest.raises(ValueError):
        whole.control_binding(manifest['tasks'][0],altered,'wrong_conclusion',manifest['verifier_identity'])


@pytest.mark.parametrize('output',[
    'PROVE TRUE\n[ERROR]: 1/29 obligations failed.\n',
    'PROVE FALSE\n[ERROR]: 2/29 obligations failed.\n',
    'PROVE FALSE\n[ERROR]: 1/29 obligations failed.\nParse error\n',
    'PROVE FALSE\n[ERROR]: proof failed.\n',
])
def test_wrong_conclusion_must_be_single_false_obligation(tmp_path,output):
    if not whole.MANIFEST.exists():
        pytest.skip('local append-only control artifacts unavailable')
    manifest=whole.load_manifest(whole.MANIFEST)
    bad=json.loads((whole.MANIFEST.parent/'controls.json').read_text())[1]
    original=Path(bad['workdir'])
    for name in ('Lock.tla','input.json'):
        (tmp_path/name).write_bytes((original/name).read_bytes())
    (tmp_path/'tlapm.log').write_text(output)
    bad.update(workdir=str(tmp_path),candidate_path=str(tmp_path/'Lock.tla'),output=output)
    with pytest.raises(ValueError,match='Wrong conclusion'):
        whole.control_binding(manifest['tasks'][0],bad,'wrong_conclusion',manifest['verifier_identity'])


def test_prepared_packet_remote_validation():
    path=whole.ROOT/'results/runs/proof-whole-train-prepared-20260905-v1/train.json'
    if not path.exists():
        pytest.skip('prepared local packet unavailable')
    assert len(whole.validate_training_packet(json.loads(path.read_text())))==6
