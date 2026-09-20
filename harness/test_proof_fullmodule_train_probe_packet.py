import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
from unittest.mock import patch
import pytest
from tools import proof_fullmodule_train_probe_packet as p


@pytest.fixture(scope='module')
def packet():
    # Actual CPU token reconstruction, in memory only. No output packet written.
    with (patch.object(p.training.controls,'audit',side_effect=AssertionError('No new controls')),
          patch.object(p.training.audit,'protected',side_effect=AssertionError('No protected corpus'))):
        return p.prepare()


def test_exact_deterministic20_train_membership_and_prefix(packet):
    value=p.load(p.INPUT);rows=value['rows'][42:];encoded=value['encodings'][42:]
    tasks=p.validate_export(packet)
    assert p.INDICES==tuple(i*126//19 for i in range(20))
    assert len(tasks)==20 and p.INDICES[0]==0 and p.INDICES[-1]==126
    for t,i in zip(tasks,p.INDICES):
        r=rows[i];e=encoded[i]
        assert t['id']==r['id'] and t['prompt']==r['prompt']
        assert t['original_training_row_sha256']==p.digest(r)
        assert t['response_sha256']==r['response_sha256']
        assert t['input_token_ids']==e['input_ids'][:e['prompt_tokens']]
        assert t['control_task_id']==r['id'].removeprefix('w4-fullmodule:')
        assert r['response'] not in t['prompt']
        assert not {'response','spec_text','labels','target'}&t.keys()
    assert packet['minimum_required_context']==17113
    assert packet['max_new_tokens']==16384 and packet['requested_samples']==40
    assert not packet['launch_authorized'] and not packet['generalization_claim']


def test_actual_worker_encoder_matches_saved_training_prefix(packet):
    from tools import proof_fullmodule_retention_eval as evaluator
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(p.TOKENIZER,local_files_only=True)
    for task in packet['tasks']:
        actual=evaluator.common.encode_prompt(tokenizer,task)
        assert actual['input_token_ids']==task['input_token_ids']
        assert actual['rendered_prompt']==task['rendered_prompt']


@pytest.mark.parametrize('defect',['membership','order','prompt','tokens','response_hash','module','control_id',
    'parent','child','output_budget','time','seed','training','source','tokenizer','input','environment','extra'])
def test_every_contract_mutation_rejected(packet,defect):
    value=copy.deepcopy(packet)
    if defect=='membership':value['selected_indices'][0]=1
    elif defect=='order':value['tasks'].reverse()
    elif defect in ('prompt','response_hash','module','control_id'):
        key=dict(prompt='prompt',response_hash='response_sha256',module='module_name',control_id='control_task_id')[defect]
        value['tasks'][0][key]+=' changed'
    elif defect=='tokens':value['tasks'][0]['input_token_ids'][0]+=1
    elif defect in ('parent','child'):value['policies'][defect]='0'*64
    elif defect=='output_budget':value['max_new_tokens']=3072
    elif defect=='time':value['seconds_per_item']=46
    elif defect=='seed':value['seed']+=1
    elif defect=='training':value['training_authorized']=True
    elif defect=='source':value['source_sha256'][next(iter(value['source_sha256']))]='0'*64
    elif defect=='tokenizer':value['tokenizer_files'][next(iter(value['tokenizer_files']))]='0'*64
    elif defect=='input':value['training_input_sha256']='0'*64
    elif defect=='environment':value['prompt_environment']['TLA_PROMPT_ARITY']='1'
    else:value['answer']='leaked'
    with pytest.raises(ValueError):p.validate_export(value)


def test_input_byte_drift_rejected_before_loader():
    with patch.object(p.training,'validate_training_packet',side_effect=AssertionError('must fail first')):
        with pytest.raises(ValueError):p.select(p.INPUT.read_bytes()+b' ')


def test_source_drift_rejected(packet):
    with patch.object(p,'sources',return_value={}):
        with pytest.raises(ValueError):p.validate_export(packet)


def test_isolated_portable_validation_without_any_corpus(packet,tmp_path):
    stage=tmp_path/'stage';stage.mkdir()
    for name in p.SOURCES:
        target=stage/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p.ROOT/name,target)
    fixture=tmp_path/'fixture.json';fixture.write_text(json.dumps(packet))
    script='''import json,sys
from pathlib import Path
from tools import proof_fullmodule_train_probe_packet as p
v=json.loads(Path(sys.argv[1]).read_text())
assert not (p.ROOT/'results').exists() and not (p.ROOT/'corpus').exists()
original=Path.open
def guarded(self,*args,**kw):
    assert '/Users/eric/GitHub/prove-TLA' not in str(self)
    return original(self,*args,**kw)
Path.open=guarded
assert len(p.validate_export(v))==20
'''
    result=subprocess.run([str(p.ROOT/'tools/smoke/e2e/.venv/bin/python'),'-c',script,str(fixture)],
        cwd=stage,env=dict(os.environ,PYTHONPATH=str(stage)),capture_output=True,text=True,timeout=60)
    assert result.returncode==0,result.stdout+result.stderr
