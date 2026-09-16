import copy
import json
from pathlib import Path
import subprocess
import sys
import pytest
from tools import proof_sumsequence_packet as module


@pytest.fixture
def packet():return module._packet(module._static_manifest())


def test_exact_reconstruction(packet):
    assert module.validate_export(packet)==packet['tasks']
    manifest=module._static_manifest()
    assert module.digest(manifest)==module.MANIFEST_SHA256
    assert manifest['discovered']==5 and manifest['inventory'][-1]['status']=='pending_prerequisite_closure'
    assert [row['id'] for row in packet['tasks']]==list(module.TRAIN_IDS)
    for task,row in zip(manifest['tasks'],packet['tasks']):
        assert task['prefix']+'<PROOF_HOLE>'+task['suffix'] in row['prompt']
        assert set(row)=={'id','split','prompt','prompt_sha256'}
    assert 'OBVIOUS\n' in manifest['tasks'][3]['prefix']


@pytest.mark.parametrize('change',[
    lambda p:p['tasks'].reverse(),
    lambda p:p['tasks'].pop(),
    lambda p:p['tasks'][0].update(split='development'),
    lambda p:p['tasks'][0].update(id='foreign'),
    lambda p:p['tasks'][0].update(reference_fragment='OBVIOUS'),
    lambda p:p.update(schema=True),
    lambda p:p.update(reference_fragments_exported=True),
    lambda p:p.update(manifest_sha256='0'*64),
    lambda p:p.update(other='hidden answer'),
])
def test_packet_mutation_rejected(packet,change):
    change(packet)
    with pytest.raises(ValueError):module.validate_export(packet)


def test_rehashing_changed_prompt_cannot_admit(packet):
    packet['tasks'][0]['prompt']+='\nOBVIOUS'
    packet['tasks'][0]['prompt_sha256']=module.sha(packet['tasks'][0]['prompt'].encode())
    with pytest.raises(ValueError):module.validate_export(packet)


def test_portable_validator_needs_only_own_source(tmp_path,packet):
    (tmp_path/'validator.py').write_bytes(Path(module.__file__).read_bytes())
    (tmp_path/'packet.json').write_text(json.dumps(packet))
    result=subprocess.run([sys.executable,'-I','-c',
        'import runpy,json; v=runpy.run_path("validator.py"); '
        'assert len(v["validate_export"](json.load(open("packet.json"))))==4'],
        cwd=tmp_path,capture_output=True,text=True,timeout=10)
    assert result.returncode==0,result.stderr


def test_changed_frozen_evidence_rejected(tmp_path):
    path=tmp_path/'evidence';path.write_bytes(b'changed')
    with pytest.raises(ValueError,match='evidence hash'):module.checked(path,module.sha(b'original'))


def test_real_saved_raw_controls_audit_without_success_flag_shortcut():
    tasks=module.static_tasks()
    for (run,pins),group in zip(module.RUNS.items(),(tasks[:2],tasks[2:3],tasks[3:])):
        for n,task in enumerate(group):
            for offset in (0,1):
                row=json.loads(module.checked(module.ROOT/'results/runs'/run/f'row-{2*n+offset+1}.json',
                                             pins[f'row-{2*n+offset+1}']))
                module.audit_row(task,row,wrapped=len(group)==2)
                bad=copy.deepcopy(row);bad['result']['output']+='tampered'
                with pytest.raises(ValueError):module.audit_row(task,bad,wrapped=len(group)==2)


def test_static_manifest_drift_blocks_before_runtime(monkeypatch):
    monkeypatch.setattr(module,'_static_manifest',lambda:{'foreign':True})
    with pytest.raises(ValueError,match='Static manifest'):module.manifest()


def test_export_requires_full_local_admission(monkeypatch):
    def reject():raise ValueError('Raw admission failed')
    monkeypatch.setattr(module,'manifest',reject)
    with pytest.raises(ValueError,match='Raw admission'):module.export_tasks()


def test_incomplete_process_cannot_admit(tmp_path,monkeypatch):
    from tools import proof_sumsequence_lemma3 as controls
    from harness.test_proof_sumsequence_lemma2a import execute
    controls.controls(tmp_path/'run',execute=execute,identify=lambda:{})
    row=json.loads((tmp_path/'run/row-1.json').read_text())
    process_path=Path(row['result']['workdir'])/'process.json'
    process=json.loads(process_path.read_text());process['cleanup_complete']=False
    process_path.write_text(json.dumps(process))
    with pytest.raises(ValueError,match='Incomplete'):
        module.audit_row(module.static_tasks()[3],row,wrapped=False)


def test_exclusion_report_flags_cannot_replace_recomputed_checks(monkeypatch):
    # Pinned reports still get independently recomputed against current sources.
    from tools import proof_sumsequence_exclusions as prior
    original=prior.breadth.compare
    def altered(*args):
        value=original(*args);value['max_jaccard']=1;return value
    monkeypatch.setattr(prior.breadth,'compare',altered)
    with pytest.raises(ValueError,match='Recomputed'):
        module.audit_exclusions()
