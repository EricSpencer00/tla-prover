import copy
import json

import pytest
from tools import proof_sumsequence_sany_repair_packet as p


@pytest.fixture(scope='module')
def original():
    from transformers import AutoTokenizer
    broader=p.policy.greedy.broader;extra=p.policy.greedy.extra
    tasks=broader.combined_tasks(broader.load_manifests())+extra.static_tasks()
    portable=p.policy.greedy.validate_export(p.load(p.PROMPTS))
    raw=p.load(p.GENERATIONS/'accounting.json');records=p.load(p.VERIFIED/'rows.json')[40:]
    tokenizer=AutoTokenizer.from_pretrained(p.TOKENIZER,local_files_only=True)
    return tasks,portable,raw,records,tokenizer,{'test_provenance':True}


@pytest.fixture
def values(original):
    return [copy.deepcopy(v) if i!=4 else v for i,v in enumerate(original)]


def test_actual_two_misses_full_token_feasibility_and_no_truncation(values):
    packet=p.build(*values);p.validate_packet(packet,*values)
    assert packet['original_denominator']==40 and len(packet['original_requested_ids'])==40
    assert [r['id'] for r in packet['tasks']]==list(p.IDS)
    assert packet['diagnostic_tasks']==2 and packet['budget']['optimizer_updates']==0
    assert not packet['gate_claim'] and not packet['pass_at1_claim'] and not packet['generalization_claim']
    for row in packet['tasks']:
        assert row['original_prompt'] in row['prompt'] and row['raw_failed_reply'] in row['prompt']
        assert row['context']['prefix'] in row['prompt'] and row['context']['suffix'] in row['prompt']
        assert row['encoding']['input_token_ids']==values[4](row['encoding']['rendered_prompt'],add_special_tokens=False,truncation=False)['input_ids']
        assert row['total_context_tokens']==row['input_tokens']+3072
        assert row['context_overage_tokens']==max(0,row['input_tokens']-5120)
        assert row['executable_full_context']==(row['input_tokens']<=5120)
    cap,reject=packet['tasks']
    assert cap['failure']['sany_diagnostic'] is None and not cap['failure']['sany_attempted']
    assert reject['failure']['sany_attempted'] and 'Encountered "SUFFICES"' in reject['failure']['sany_diagnostic']
    assert not cap['executable_full_context'] and reject['executable_full_context']


def test_reference_answers_never_supply_exported_text(values):
    for task in values[0]:task['reference_fragment']='ORACLE_ANSWER_MUST_NEVER_APPEAR'
    packet=p.build(*values)
    assert 'ORACLE_ANSWER_MUST_NEVER_APPEAR' not in json.dumps(packet)
    assert not packet['reference_answers_exported']
    assert all(not row['reference_answer_exported'] for row in packet['tasks'])


@pytest.mark.parametrize('defect',['order','count','dev','goal','source','dependency','reply','fake_sany_cap','lost_sany','different_miss'])
def test_immutable_population_context_and_actual_feedback(values,defect):
    tasks,portable,raw,records,tokenizer,provenance=values
    index=next(i for i,r in enumerate(raw) if r['id']==p.IDS[0]);last=39
    if defect=='order':raw[0],raw[1]=raw[1],raw[0]
    elif defect=='count':records.pop()
    elif defect=='dev':tasks[index]['split']='development'
    elif defect=='goal':tasks[index]['prefix']+='ALTERED_GOAL'
    elif defect=='source':tasks[index]['source_sha256']='bad'
    elif defect=='dependency':tasks[index]['dependencies']=[]
    elif defect=='reply':raw[index]['raw_reply']+='corrupt'
    elif defect=='fake_sany_cap':records[index]['evidence']={'error':'invented'}
    elif defect=='lost_sany':records[last]['evidence']['evidence']['sany_evidence']['output']=''
    else:records[0]['sany']=None
    with pytest.raises(ValueError):p.build(*values)


@pytest.mark.parametrize('defect',['prompt','tokens','overage','denominator','diagnostic','reference_flag'])
def test_export_validator_rejects_tampered_packet(values,defect):
    packet=p.build(*values)
    if defect=='prompt':packet['tasks'][0]['prompt']='shortened'
    elif defect=='tokens':packet['tasks'][0]['encoding']['input_token_ids'].pop()
    elif defect=='overage':packet['tasks'][0]['context_overage_tokens']=0
    elif defect=='denominator':packet['original_denominator']=2
    elif defect=='diagnostic':packet['tasks'][0]['failure']['sany_diagnostic']='fictional'
    else:packet['reference_answers_exported']=True
    with pytest.raises(ValueError):p.validate_packet(packet,*values)


def test_creation_failure_preserves_original_denominator(tmp_path,monkeypatch):
    def fail():raise ValueError('instrument failure')
    monkeypatch.setattr(p,'admit',fail)
    output=tmp_path/'packet'
    with pytest.raises(ValueError):p.create(output)
    assert p.load(output/'summary.json')==dict(complete=False,original_denominator=40,diagnostic_tasks=2,generation_performed=False)
    assert not (output/'packet.json').exists()
