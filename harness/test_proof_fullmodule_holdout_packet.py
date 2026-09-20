import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from unittest.mock import patch
import pytest
from tools import proof_fullmodule_holdout_packet as p


@pytest.fixture(scope='module')
def actual():return p.build()


def test_actual_all30_portable_and_full_ceiling(actual):
    rows=p.validate_packet(actual)
    assert len(rows)==30 and [r['id'] for r in rows]==list(p.IDS)
    assert {k:sum(r['population']==k for r in rows) for k in p.COUNTS}==p.COUNTS
    assert min(r['input_tokens'] for r in rows)==480
    assert max(r['input_tokens'] for r in rows)==1309
    assert actual['minimum_required_context']==17693
    assert all(r['required_context']-r['input_tokens']==16384 for r in rows)
    assert actual['oracle_controls_performed'] is False and actual['launch_authorized'] is False
    assert actual['g1_denominator']==206 and actual['g1_missing_source_ids']==['120']


def test_no_reference_modules_in_prompts_or_packet(actual):
    for row in actual['tasks']:
        body=Path(row['source']['path']).read_text()
        assert body not in row['prompt']
        assert 'reference_fragment' not in row and 'source_text' not in row
        assert set(row['source'])=={'path','sha256'}
        assert row['prompt']==p.framing.build_generation_prompt(json.loads(row['description']['bytes']),
            row['config']['bytes'],row['module_name'],None)
        if row['wrapper']:
            assert Path(row['wrapper']['path']).read_text() not in row['prompt']
        assert all(p.runner.module_name(Path(path).read_text())!=row['module_name'] for path in row['wrapper_dependencies'])


def test_exact_wrapper_and_dependency_provenance(actual):
    assert [r['id'] for r in actual['tasks'] if r['wrapper']]==['128','141','148','158','168']
    for row in actual['tasks']:
        for record in [row['source'],row['description'],row['config']]+([row['wrapper']] if row['wrapper'] else []):
            assert p.file_sha(record['path'])==record['sha256']
        for path,h in (row['dependencies']|row['wrapper_dependencies']).items():assert p.file_sha(path)==h
    assert p.digest(p.inventories())==p.INPUTS_SHA


@pytest.mark.parametrize('field,value',[('max_new_tokens',3072),('requested_tasks',29),('temperature',1.),
    ('split','train'),('training_authorized',True),('protected_failures_must_not_feed_training',False),
    ('oracle_controls_performed',True),('launch_authorized',True),('generalization_claim',True),
    ('g1_denominator',205),('requested_samples',60.0)])
def test_contract_drift(actual,field,value):
    changed=copy.deepcopy(actual);changed[field]=value
    with pytest.raises(ValueError):p.validate_packet(changed)


@pytest.mark.parametrize('field',['prompt','prompt_sha256','input_token_ids','rendered_prompt','config','source','dependencies','module_name','population'])
def test_exact_row_mutations_rejected(actual,field):
    changed=copy.deepcopy(actual);changed['tasks'][0][field]='mutated'
    with pytest.raises(ValueError):p.validate_packet(changed)


def test_wrong_order_and_missing_key(actual):
    changed=copy.deepcopy(actual);changed['tasks'].reverse()
    with pytest.raises(ValueError):p.validate_packet(changed)
    changed=copy.deepcopy(actual);changed['tasks'].pop()
    with pytest.raises(ValueError):p.validate_packet(changed)


@pytest.mark.parametrize('name',list(p.PROMPT_ENV))
def test_inherited_prompt_flags_not_silently_overridden(monkeypatch,name):
    monkeypatch.setenv(name,'2' if name=='GEN_EVAL_CONCURRENCY' else '1')
    with pytest.raises(ValueError):p.environment()


def test_source_drift_and_extra_reference_rejected(actual):
    with patch.object(p,'sources',return_value={}):
        with pytest.raises(ValueError):p.validate_packet(actual)
    changed=copy.deepcopy(actual);changed['reference_answers']=['forbidden']
    with pytest.raises(ValueError):p.validate_packet(changed)


def test_full_actual_token_reconstruction(actual):
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(p.TOKENIZER,local_files_only=True)
    assert p.make_rows(tokenizer)==actual['tasks']


def test_sources_only_isolated_portable_validation(actual,tmp_path):
    for name in p.SOURCES:
        target=tmp_path/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p.ROOT/name,target)
    # Test-only portable fixture, no host corpus/tokenizer fallback is available.
    fixture=tmp_path/'packet.json';fixture.write_text(json.dumps(actual))
    env=dict(os.environ);env.pop('PYTHONPATH',None)
    command=[sys.executable,'-c',"import json;from tools import proof_fullmodule_holdout_packet as p;assert len(p.validate_packet(json.load(open('packet.json'))))==30"]
    result=subprocess.run(command,cwd=tmp_path,env=env,capture_output=True,text=True,timeout=30)
    assert result.returncode==0,result.stdout+result.stderr
