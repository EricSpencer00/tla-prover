import copy
import json
from pathlib import Path
from unittest.mock import patch
import pytest
from tools import proof_sany_repair_learning_packet as p


@pytest.fixture
def packet():
    old=p.ORIGINAL.read_text();repair=p.REPAIR.read_text();rows=p.compose(old,repair)
    encodings=[dict(id=r['id'],prompt_sha256=r['prompt_sha256'],response_sha256=r['response_sha256'],
        input_ids=[1,2,3],labels=[-100,2,3],prompt_tokens=1,response_tokens=2,rendered_prompt='mock') for r in rows]
    controls=[dict(id=r['id'],label=label,response_sha256=r['response_sha256'],accepted=True)
        for r in rows[-2:] for label in ('positive','false_conclusion')]
    return dict(p.CONTRACT,original_packet_bytes=old,repair_packet_bytes=repair,rows=rows,rows_sha256=p.digest(rows),
        encodings=encodings,eos_token_id=3,target_controls=dict(complete=True,requested_controls=4,accepted_controls=4,rows=controls),
        exclusions=dict(protected_populations=['official119','official30','original18','development']))


def test_real_portable_composition(packet):
    rows=p.validate_training_packet(packet)
    assert rows[:40]==p.load(p.ORIGINAL)['rows']
    assert len(rows)==42 and len({r['id'] for r in rows})==42
    assert rows[-2]['response']==rows[3]['response']
    assert rows[-1]['response']=='BY DEF Front, Tail'
    assert [r['prompt'] for r in rows[-2:]]==[r['prompt'] for r in p.load(p.REPAIR)['tasks']]
    assert rows[-1]['assembled_sha256']!=rows[35]['assembled_sha256']
    assert all(r['split']=='train' and set(r)==p.original.ROW_FIELDS for r in rows)


@pytest.mark.parametrize('field,value',[('parent_checkpoint_sha256','0'*64),('requested_rows',40),
    ('requested_rows',42.0),('training_authorized',True),('on_policy_rewards',True),('max_tokens',8192),
    ('truncation',True),('original_evaluation_denominator',42)])
def test_contract_drift(packet,field,value):
    packet[field]=value
    with pytest.raises(ValueError):p.validate_training_packet(packet)


@pytest.mark.parametrize('mutation',['oldbytes','repairbytes','response','prompt','goal','order','count','eos','mask','length','control','excluded'])
def test_fail_closed(packet,mutation):
    if mutation=='oldbytes':packet['original_packet_bytes']+=' '
    elif mutation=='repairbytes':packet['repair_packet_bytes']+=' '
    elif mutation in ('response','prompt'):packet['rows'][-1][mutation]+=' '
    elif mutation=='goal':packet['rows'][-1]['assembled_sha256']='0'*64
    elif mutation=='order':packet['rows'].reverse()
    elif mutation=='count':packet['rows'].pop()
    elif mutation=='eos':packet['encodings'][-1]['input_ids'][-1]=4
    elif mutation=='mask':packet['encodings'][0]['labels'][0]=1
    elif mutation=='length':packet['encodings'][0]['input_ids']*=4000
    elif mutation=='control':packet['target_controls']['rows'][1]['accepted']=False
    elif mutation=='excluded':packet['exclusions']['protected_populations'].pop()
    with pytest.raises(ValueError):p.validate_training_packet(packet)


def test_actual_tokenizer_full42():
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(p.repair.TOKENIZER,local_files_only=True)
    rows=p.compose(p.ORIGINAL.read_text(),p.REPAIR.read_text());enc=p.encode_rows(tokenizer,rows)
    assert len(enc)==42 and all(len(e['input_ids'])<=9216 for e in enc)
    assert enc[-2]['prompt_tokens']==5290
    assert enc[-2]['response_tokens']==2171 and len(enc[-2]['input_ids'])==7461
    assert enc[-1]['prompt_tokens']==921
    assert all(e['input_ids'][-1]==tokenizer.eos_token_id for e in enc)


def test_incomplete_controls_keep_four(packet,tmp_path):
    rows=packet['rows'];chosen=[dict(id='a'),dict(id='b')]
    with patch.object(p.checks,'negative_task',side_effect=lambda t:t),patch.object(p.checks,'audit_check'),patch.object(p.checks,'intended_negative',return_value=False):
        result=p.target_controls([],chosen,rows,{},tmp_path,checker=lambda *a:dict(sany=None,proof=None,status='unmeasured'),clock=iter([0,0,250,250]).__next__)
    assert not result['complete'] and result['requested_controls']==4 and result['accepted_controls']==0
    assert len(p.load(tmp_path/'control_rows.json'))==4
    assert sum(r['status']=='unattempted' for r in result['rows'])==3


def test_source_inventory_exists():
    assert 'tools/proof_sany_repair_learning_packet.py' in p.SOURCES
    assert all((p.ROOT/name).is_file() for name in p.SOURCES)


def test_reference_metadata_exception_escapes(packet,tmp_path):
    with patch.object(p.checks,'negative_task',side_effect=KeyError('goal_offsets')):
        with patch.object(p.checks,'audit_check'):
            with pytest.raises(KeyError):
                p.target_controls([], [dict(id='a'),dict(id='b')],packet['rows'],{},tmp_path,
                    checker=lambda *a:dict(sany=1,proof=1,status='certified'))
