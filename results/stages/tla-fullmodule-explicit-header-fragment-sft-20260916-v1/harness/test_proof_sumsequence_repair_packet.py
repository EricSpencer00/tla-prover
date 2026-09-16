import json
from pathlib import Path
import subprocess
import sys
import pytest
from tools import proof_sumsequence_repair_packet as module


@pytest.fixture
def packet():return module._build()


def test_exact_population_and_unchanged_retention(packet):
    assert module.validate_training_packet(packet)==packet['rows']
    original=json.loads(module.checked(module.OLD,module.OLD_SHA))
    assert packet['rows'][:32]==original['rows']
    assert [r['mode'] for r in packet['inventory']]==['retention_whole']*32+['whole_generation']*4+['actual_reply_repair']*4
    assert packet['discovery']['pending']==['sumsequence-Lemma4']
    assert packet['parent_checkpoint_sha256']==module.PARENT_SHA


def test_exact_actual_replies_including_successes_and_caps(packet):
    replies=[json.loads(line) for line in (module.GENERATIONS/'child/generations.jsonl').read_bytes().splitlines()]
    assert [r['finish_reason'] for r in replies]==['eos','token_limit','eos','token_limit']
    for whole,repair,reply in zip(packet['rows'][32:36],packet['rows'][36:],replies):
        assert repair['response']==whole['response']
        assert repair['prompt']==module.repair_prompt(whole['prompt'],reply)
        assert '===BEGIN EXACT PRIOR ATTEMPT===\n'+reply['raw_reply']+'\n===END EXACT PRIOR ATTEMPT===' in repair['prompt']
        if reply['finish_reason']=='token_limit':
            assert 'incomplete prefix' in repair['prompt'] and 'It was not checked by TLAPS' in repair['prompt']
        else:assert 'It may already be correct' in repair['prompt']


@pytest.mark.parametrize('change',[
    lambda p:p['rows'].reverse(),lambda p:p['rows'].pop(),
    lambda p:p['rows'][0].update(split='development'),
    lambda p:p['rows'][36].update(id='foreign-repair'),
    lambda p:p['rows'][0].update(other='answer'),
    lambda p:p['inventory'][37].update(prior_finish_reason='eos'),
    lambda p:p.update(on_policy_rewards=True),lambda p:p.update(parent_checkpoint_sha256='0'*64),
    lambda p:p.update(requested_rows=39),lambda p:p.update(schema=True),
    lambda p:p['evidence'].update(baseline_directory='proof-sumsequence-baseline-verified-20260906-v1'),
])
def test_all_mutations_rejected(packet,change):
    change(packet)
    with pytest.raises(ValueError):module.validate_training_packet(packet)


def test_rehashed_reference_cannot_replace_target(packet):
    row=packet['rows'][33];row['response']='OBVIOUS\n';row['response_sha256']=module.sha(row['response'].encode())
    with pytest.raises(ValueError):module.validate_training_packet(packet)


def test_rehashed_truncated_prior_reply_rejected(packet):
    row=packet['rows'][37];row['prompt']=row['prompt'][:100];row['prompt_sha256']=module.sha(row['prompt'].encode())
    with pytest.raises(ValueError):module.validate_training_packet(packet)


def test_portable_only_source_and_packet(tmp_path,packet):
    (tmp_path/'validator.py').write_bytes(Path(module.__file__).read_bytes())
    (tmp_path/'packet.json').write_text(json.dumps(packet))
    result=subprocess.run([sys.executable,'-I','-c',
        'import runpy,json; p=runpy.run_path("validator.py"); assert len(p["validate_export"](json.load(open("packet.json"))))==40'],
        cwd=tmp_path,capture_output=True,text=True,timeout=10)
    assert result.returncode==0,result.stderr


def test_full_export_requires_raw_baseline_admission(monkeypatch):
    def reject(*args):raise ValueError('Raw baseline invalid')
    monkeypatch.setattr(module,'audit_baseline',reject)
    with pytest.raises(ValueError,match='Raw baseline'):module.export_packet()


def test_bad_prior_hash_or_finish_rejected(packet):
    attempt=dict(raw_reply='BY DEF Front',raw_reply_sha256='0'*64,finish_reason='eos')
    with pytest.raises(ValueError,match='prior reply'):module.repair_prompt('prompt',attempt)
    attempt['finish_reason']='fabricated_failure'
    with pytest.raises(ValueError,match='finish'):module.repair_prompt('prompt',attempt)
