import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
from unittest.mock import patch

import pytest
from tools import proof_fullmodule_learning_packet as p


@pytest.fixture(scope='module')
def packet():
    # In-memory composition only: no fresh checks, admission, output or optimizer.
    with patch.object(p.controls,'audit',side_effect=AssertionError('no controls run')):
        return p.payload()


def test_actual169_preserves_exact42_and128_dispositions(packet):
    rows=p.validate_training_packet(packet)
    old=json.loads(packet['old_packet_bytes'])
    assert rows[:42]==old['rows'] and packet['encodings'][:42]==old['encodings']
    assert len(rows)==169 and len(packet['eligibility'])==128
    assert sum(e['included'] for e in packet['eligibility'])==127
    assert [e['id'] for e in packet['eligibility'] if not e['included']]==[p.BLOCKED]
    assert 'w4-fullmodule:'+p.BLOCKED not in {r['id'] for r in rows}
    assert packet['max_full_tokens']==7461
    assert not packet['training_authorized'] and not packet['new_data_semantic_admission']


def test_exact_module_targets_and_prompt_provenance(packet):
    candidates=json.loads(packet['audit_rows_bytes'])
    included=[r for r in candidates if r['exclusions']['status']=='lexically_clear']
    for row,source in zip(packet['rows'][42:],included):
        assert row['response']==source['raw']['spec_text']
        assert row['prompt']==source['encoded']['prompt']
        assert row['source_sha256']==source['encoded']['response_sha256']
        assert row['split']=='train'
    assert p.identity()['files']==p.expected_files()
    assert all(not Path(k).is_absolute() for k in p.expected_files())


@pytest.mark.parametrize('defect',[
    'parent','count','old_bytes','audit_bytes','controls_bytes','summary_bytes','receipt_bytes',
    'old_row','old_encoding','new_target','labels','eos','blocked','source_map','identity_sources',
    'identity_files','identity_extra','exclusion_pin','control_pin','max_tokens'])
def test_tampering_fails_closed(packet,defect):
    value=copy.deepcopy(packet)
    if defect=='parent':value['parent_checkpoint_sha256']='0'*64
    elif defect=='count':value['requested_rows']=168
    elif defect in ('old_bytes','audit_bytes','controls_bytes','summary_bytes','receipt_bytes'):
        key={'old_bytes':'old_packet_bytes','audit_bytes':'audit_rows_bytes','controls_bytes':'control_rows_bytes',
             'summary_bytes':'controls_summary_bytes','receipt_bytes':'controls_receipt_bytes'}[defect]
        value[key]+=' '
    elif defect=='old_row':value['rows'][0]['response']+=' '
    elif defect=='old_encoding':value['encodings'][0]['input_ids'][0]+=1
    elif defect=='new_target':value['rows'][42]['response']+='\nPROPERTY invented'
    elif defect=='labels':value['encodings'][42]['labels'][0]=1
    elif defect=='eos':value['eos_token_id']+=1
    elif defect=='blocked':next(e for e in value['eligibility'] if not e['included'])['included']=True
    elif defect=='source_map':value['source_sha256'][next(iter(value['source_sha256']))]='0'*64
    elif defect=='identity_sources':value['identity']['sources'][next(iter(value['identity']['sources']))]='0'*64
    elif defect=='identity_files':value['identity']['files'][next(iter(value['identity']['files']))]='0'*64
    elif defect=='identity_extra':value['identity']['files']['unexpected']='0'*64
    elif defect=='exclusion_pin':value['protected_evidence_sha256']='0'*64
    elif defect=='control_pin':value['control_pins']['rows.json']='0'*64
    else:value['max_full_tokens']=9217
    with pytest.raises(ValueError):p.validate_training_packet(value)


def test_current_source_drift_rejected(packet):
    changed=dict(p.sources());changed[next(iter(changed))]='0'*64
    with patch.object(p,'sources',return_value=changed),pytest.raises(ValueError,match='source'):
        p.validate_training_packet(packet)


def test_all169_actual_tokenizer_reconstruction(packet):
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(p.audit.framing.TOKENIZER,local_files_only=True)
    for row,encoding in zip(packet['rows'],packet['encodings']):
        actual=p.retained.encode_candidate(tokenizer,row['prompt'],row['response'],9216)
        assert dict(actual,id=row['id'],prompt_sha256=row['prompt_sha256'],response_sha256=row['response_sha256'])==encoding


def test_admit_walks_all_actual_pins_and_replays_controls():
    with patch.object(p.controls,'audit') as raw_audit:
        value=p.admit()
    raw_audit.assert_called_once()
    assert len(p.validate_training_packet(value))==169


def test_isolated_source_only_import_and_portable_validation(packet,tmp_path):
    stage=tmp_path/'isolated';stage.mkdir()
    for name in p.SOURCES:
        target=stage/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(p.ROOT/name,target)
    fixture=tmp_path/'fixture.json';fixture.write_text(json.dumps(packet))
    script='''import json,sys
from pathlib import Path
from tools import proof_fullmodule_learning_packet as p
value=json.loads(Path(sys.argv[1]).read_text())
assert not (p.ROOT/'results').exists()
original_open=Path.open
def guarded(self,*args,**kwargs):
    assert '/Users/eric/GitHub/prove-TLA' not in str(self), 'original local artifact access'
    return original_open(self,*args,**kwargs)
Path.open=guarded
assert len(p.validate_training_packet(value))==169
print('portable169')
'''
    env=dict(os.environ,PYTHONPATH=str(stage),OMP_NUM_THREADS='4',OPENBLAS_NUM_THREADS='4',MKL_NUM_THREADS='4',NUMEXPR_NUM_THREADS='4')
    result=subprocess.run([str(p.ROOT/'tools/smoke/e2e/.venv/bin/python'),'-c',script,str(fixture)],
        cwd=stage,env=env,capture_output=True,text=True,timeout=60)
    assert result.returncode==0,result.stdout+result.stderr
    assert 'portable169' in result.stdout
