import json
from pathlib import Path
import pytest
from tools import proof_cuda_feedback_cycle as cycle


def test_unfrozen_or_partial_population_cannot_execute(monkeypatch,tmp_path):
    monkeypatch.setattr(cycle,'PACKET_HASHES',{'base':'a'*64})
    with pytest.raises(ValueError,match='three'):
        cycle.freeze(tmp_path,tmp_path,tmp_path/'parent',tmp_path/'child')


def test_full_freeze_calls_actual_admission_for_all_policies(monkeypatch,tmp_path):
    hashes={a:str(i)*64 for i,a in enumerate(cycle.ARMS)}
    monkeypatch.setattr(cycle,'PACKET_HASHES',hashes)
    calls=[]
    def admit(*args):calls.append(args); return {'arm':args[0].parent.name}
    monkeypatch.setattr(cycle.probe,'admit',admit)
    result=cycle.freeze(tmp_path,tmp_path/'model',tmp_path/'p',tmp_path/'c')
    assert [call[0].parent.name for call in calls]==list(cycle.ARMS)
    assert [call[1] for call in calls]==list(hashes.values())
    assert [call[3] for call in calls]==[None,tmp_path/'p',tmp_path/'c']
    assert set(result['admissions'])==set(cycle.ARMS)
    assert set(cycle.probe.IMPLEMENTATION)<=set(result['implementation_sha256'])


@pytest.mark.parametrize('fault',[None,'partial','time_limit','identity'])
def test_arm_completion_requires_four_measured_identity_bound_outputs(monkeypatch,tmp_path,fault):
    expected=dict(model_files={'x':'y'},prompts_sha256='p',checkpoint_sha256=None,
                  experiment_arm='base',implementation_sha256={'source':'h'})
    config=dict(expected); rows=[dict(id=str(i),status='generated') for i in range(4)]
    summary=dict(returncode=0,termination='complete')
    if fault=='partial':rows.pop()
    if fault=='time_limit':rows[0]['status']='generation_time_limit'
    if fault=='identity':config['prompts_sha256']='changed'
    cycle.dump(tmp_path/'config.json',config); cycle.dump(tmp_path/'summary.json',summary)
    (tmp_path/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    monkeypatch.setattr(cycle.probe,'validate_run',lambda *args:[dict(id=str(i)) for i in range(4)])
    seen=[]
    monkeypatch.setattr(cycle,'validate_tokenization',lambda tokenizer,task,row:seen.append(row['id']))
    if fault:
        with pytest.raises(ValueError):cycle.check_arm(tmp_path,'base',b'{}',{'admissions':{'base':expected}},None)
    else:
        result=cycle.check_arm(tmp_path,'base',b'{}',{'admissions':{'base':expected}},None)
        assert result['generated_tasks']==4 and seen==['0','1','2','3']
        assert result['verified_proof_claim'] is False


def test_feedback_job_has_no_training_command_and_nested_deadlines():
    source=(cycle.ROOT/'tools/proof_cuda_feedback_cycle.pbs').read_text()
    assert '00:20:00' in source and '900s' in source
    assert 'proof_cuda_train.py' not in source
