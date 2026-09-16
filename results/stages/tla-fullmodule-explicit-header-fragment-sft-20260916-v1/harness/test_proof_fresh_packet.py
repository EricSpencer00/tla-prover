"""Fresh evaluation export tests use fake control artifacts, never a checker."""
import copy
import json
from pathlib import Path
import subprocess
import sys

import pytest

from tools import proof_fresh_packet as fresh


@pytest.fixture
def packet():
    return dict(schema=1,manifest_sha256='a'*64,selection_sha256='b'*64,requested_tasks=14,
        reference_fragments_exported=False,candidates_exported=False,training_authorized=False,evaluation_authorized=True,
        tasks=[dict(id=i,split='fresh_evaluation',prompt='prompt '+i,prompt_sha256=fresh.sha(('prompt '+i).encode())) for i in fresh.EVAL_IDS])


def test_stdlib_import_only():
    result=subprocess.run([sys.executable,'-S','-c','from tools.proof_fresh_packet import validate_export'],
                          cwd=fresh.ROOT,capture_output=True,text=True)
    assert result.returncode==0,result.stderr


def test_valid_export(packet):assert len(fresh.validate_export(packet))==14


@pytest.mark.parametrize('mutate',[
    lambda p:p['tasks'].pop(),lambda p:p['tasks'].reverse(),
    lambda p:p['tasks'][0].update(split='train'),lambda p:p['tasks'][0].update(response='LEAK'),
    lambda p:p['tasks'][0].update(reference_fragment='LEAK'),lambda p:p.update(training_authorized=True),
    lambda p:p.update(reference_fragments_exported=True),lambda p:p.update(candidates_exported=True),
    lambda p:p.update(manifest_sha256='invalid'),lambda p:p['tasks'][0].update(prompt='changed'),
])
def test_export_rejects_leaks_or_drift(packet,mutate):
    mutate(packet)
    with pytest.raises(ValueError):fresh.validate_export(packet)


@pytest.fixture
def controlled(tmp_path):
    from tools.proof_fresh_controls import controls
    prefix='---- MODULE M ----\nTHEOREM T == ASSUME NEW x, x = 1 PROVE x = 1\n'
    fragment='BY SMT';suffix='\n====\n';source=tmp_path/'source.tla';source.write_text(prefix+fragment+suffix)
    tasks=[dict(id=i,split='fresh_evaluation',prefix=prefix,reference_fragment=fragment,suffix=suffix,
        theorem_name='T',source_path=str(source),source_sha256=fresh.sha(source.read_bytes()),
        assembled_sha256=fresh.sha(source.read_bytes()),dependencies=[],dependency_sha256={},
        goal_offsets=[prefix.index(' ASSUME'),len(prefix)],rejection_reasons=[]) for i in fresh.EVAL_IDS]
    selection=dict(tasks=tasks,requested_evaluation=14,training_authorized=False,evaluation_authorized=False)
    def construct():return copy.deepcopy(selection)
    def identity():return dict(tlapm_path='/fake/tlapm',runtime='same',fresh_selection_sha256=fresh.digest(selection))
    def fake_checker(pre,proof,post,**kwargs):
        work=kwargs['work_root'];work.mkdir(parents=True)
        candidate=work/'M.tla';candidate.write_text(pre+proof+post)
        bad='PROVE FALSE' in pre
        output='PROVE FALSE\n[ERROR]: 1/1 obligations failed.\n' if bad else '[INFO]: All 1 obligations proved.\n'
        (work/'tlapm.log').write_text(output)
        (work/'input.json').write_text(json.dumps(dict(prefix=pre,fragment=proof,suffix=post,
            theorem_name='T',contract_version='full-proof-fragment-v1')))
        return dict(contract_version='full-proof-fragment-v1',certified=not bad,status='verifier_reject' if bad else 'pass',
            returncode=10 if bad else 0,timed_out=False,proved=0 if bad else 1,total=0 if bad else 1,output=output,
            sha256=fresh.sha(candidate.read_bytes()),dependency_sha256={},command=['/fake/tlapm','--strict','--nofp','M.tla'],
            workdir=str(work),candidate_path=str(candidate))
    run=tmp_path/'controlled';controls(selection,run,checker=fake_checker,identity=identity)
    manifest=run/'manifest.json'
    return manifest,fresh.sha(manifest.read_bytes()),construct,identity


def test_full_raw_control_audit_and_referencefree_export(controlled):
    manifest,sha,construct,identity=controlled
    packet,tasks,evidence=fresh.audit_manifest(manifest,sha,construct=construct,identity=identity)
    assert len(packet['tasks'])==14 and len(evidence['controls'])==28
    assert all(t['split']=='fresh_evaluation' for t in tasks)
    assert all('response' not in row and 'reference_fragment' not in row for row in packet['tasks'])
    assert all('entire missing TLA+ proof' in row['prompt'] for row in packet['tasks'])
    assert all('BY SMT' not in row['prompt'] for row in packet['tasks'])


@pytest.mark.parametrize('filename', ['M.tla','tlapm.log','input.json'])
def test_control_artifact_tampering_rejected(controlled,filename):
    manifest,sha,construct,identity=controlled
    rows=json.loads((manifest.parent/'controls.json').read_text())
    (Path(rows[0]['workdir'])/filename).write_text('tampered')
    with pytest.raises((ValueError,json.JSONDecodeError)):
        fresh.export_tasks(manifest,sha,construct=construct,identity=identity)


def test_drifted_identity(controlled):
    manifest,sha,construct,identity=controlled
    def changed():return dict(identity(),runtime='changed')
    with pytest.raises(ValueError,match='identity differs'):
        fresh.export_tasks(manifest,sha,construct=construct,identity=changed)


def test_source_change(controlled):
    manifest,sha,construct,identity=controlled
    Path(construct()['tasks'][0]['source_path']).write_text('changed source')
    with pytest.raises(ValueError,match='Pinned artifact'):
        fresh.export_tasks(manifest,sha,construct=construct,identity=identity)


def test_wrong_manifest_pin(controlled):
    manifest,_,construct,identity=controlled
    with pytest.raises(ValueError):fresh.export_tasks(manifest,'b'*64,construct=construct,identity=identity)


def test_prepare_evaluation_only(controlled,tmp_path,monkeypatch):
    manifest,sha,construct,identity=controlled
    monkeypatch.setattr(fresh,'token_feasibility',lambda p,t:dict(rows=[dict(id=r['id'],input_tokens=100) for r in p['tasks']],
        max_tokens=8192,max_new_tokens=3072,tokenizer_files=fresh.TOKENIZER_HASHES))
    output=tmp_path/'prepared'
    packet=fresh.prepare(manifest,sha,output,construct=construct,identity=identity)
    assert set(p.name for p in output.iterdir())=={'prompts.json','evidence.json','summary.json'}
    summary=json.loads((output/'summary.json').read_text())
    assert summary['evaluation_ready'] and not summary['training_authorized']
    assert not summary['checker_executed'] and not summary['training_executed']
    rebuilt,_=fresh.export_tasks(manifest,sha,construct=construct,identity=identity)
    assert packet==rebuilt
    assert 'BY SMT' not in (output/'evidence.json').read_text()
