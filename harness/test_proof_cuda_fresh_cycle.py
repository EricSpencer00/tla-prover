"""Read-only admission/paired orchestration tests; no model or process launches."""
import json
from pathlib import Path
from types import SimpleNamespace
import sys

import pytest

from tools import proof_cuda_fresh_cycle as cycle


@pytest.fixture
def admitted(tmp_path,monkeypatch):
    model=tmp_path/'model';model.mkdir();monkeypatch.setattr(cycle,'MODEL',model)
    prompts=tmp_path/'prompts.json';prompts.write_text('{}')
    checkpoint=tmp_path/'checkpoint.pt';checkpoint.write_bytes(b'fake')
    calls=[]
    def admit(args):
        calls.append(args)
        return dict(input_evidence=[dict(id=str(i),input_tokens=100) for i in range(14)],
            checkpoint_sha256=cycle.probe.CHECKPOINT_SHA if args.checkpoint else None,
            prompts_sha256=args.expected_input_sha256,restore_exact=False)
    monkeypatch.setattr(cycle.probe,'admit',admit)
    monkeypatch.setattr(cycle,'file_sha',lambda p:'a'*64)
    frozen=cycle.freeze(prompts,'b'*64,model,checkpoint)
    return prompts,model,checkpoint,frozen,calls


def test_full_production_admission_for_both_arms(admitted):
    prompts,model,checkpoint,frozen,calls=admitted
    assert len(calls)==2
    assert calls[0].checkpoint is None and calls[0].expected_checkpoint_sha256 is None
    assert calls[1].checkpoint==checkpoint and calls[1].expected_checkpoint_sha256==cycle.probe.CHECKPOINT_SHA
    assert all(a.prompts==prompts and a.model_path==model and a.expected_input_sha256=='b'*64 for a in calls)
    assert set(frozen['implementation_sha256'])==set(cycle.SOURCES)


def test_wrong_model_path_rejected(admitted,tmp_path):
    prompts,_,checkpoint,_,calls=admitted
    with pytest.raises(ValueError,match='snapshot'):
        cycle.freeze(prompts,'b'*64,tmp_path/'different',checkpoint)
    assert len(calls)==2


def test_alias_model_path_resolves_equally(admitted,tmp_path):
    prompts,model,checkpoint,frozen,_=admitted
    alias=tmp_path/'alias';alias.symlink_to(model,target_is_directory=True)
    assert cycle.freeze(prompts,'b'*64,alias,checkpoint)==frozen


def test_mismatched_parent_inputs_block(admitted,monkeypatch):
    prompts,model,checkpoint,_,_=admitted
    monkeypatch.setattr(cycle.probe,'admit',lambda a:dict(input_evidence=['child' if a.checkpoint else 'base']))
    with pytest.raises(ValueError,match='Matched exact input'):
        cycle.freeze(prompts,'b'*64,model,checkpoint)


def test_admission_failure_propagates(admitted,monkeypatch):
    prompts,model,checkpoint,_,_=admitted
    def broken(a):raise ValueError('invalid manifest or checkpoint')
    monkeypatch.setattr(cycle.probe,'admit',broken)
    with pytest.raises(ValueError,match='invalid manifest'):
        cycle.freeze(prompts,'b'*64,model,checkpoint)


def test_exact_paired_commands_and_post_guard(admitted,tmp_path,monkeypatch):
    prompts,model,checkpoint,frozen,_=admitted
    output=tmp_path/'run';calls=[];checked=[]
    monkeypatch.setattr(cycle,'run_processes',lambda commands,logs,seconds:calls.append((commands,logs,seconds)))
    monkeypatch.setattr(cycle,'check_arm',lambda p,r,f,a:checked.append((p,r,f,a)) or dict(arm=a))
    assert cycle.execute(output,prompts,model,checkpoint,frozen)==[{'arm':'base'},{'arm':'child'}]
    commands,logs,seconds=calls[0]
    assert len(commands)==2 and seconds==1260
    assert logs==[output/'base.log',output/'child.log']
    for arm,command in zip(('base','child'),commands):
        assert command[:3]==[sys.executable,str(cycle.ROOT/'tools/proof_cuda_fresh_eval.py'),'generate']
        assert command[command.index('--prompts')+1]==str(prompts)
        assert command[command.index('--expected-input-sha256')+1]==frozen['prompts_sha256']
        assert command[command.index('--output')+1]==str(output/arm)
        assert not any(flag in command for flag in ('--train','--response','--reference','--manifest'))
    assert '--checkpoint' not in commands[0]
    assert commands[1][commands[1].index('--checkpoint')+1]==str(checkpoint)
    assert commands[1][commands[1].index('--expected-checkpoint-sha256')+1]==cycle.probe.CHECKPOINT_SHA
    assert [r[3] for r in checked]==['base','child']


def test_identity_drift_stops_before_arm_acceptance(admitted,tmp_path,monkeypatch):
    prompts,model,checkpoint,frozen,_=admitted
    monkeypatch.setattr(cycle,'run_processes',lambda *args:None)
    monkeypatch.setattr(cycle,'freeze',lambda *args:dict(frozen,checkpoint_sha256='changed'))
    def unexpected(*args):raise AssertionError('arm accepted despite drift')
    monkeypatch.setattr(cycle,'check_arm',unexpected)
    with pytest.raises(ValueError,match='changed during'):
        cycle.execute(tmp_path/'run',prompts,model,checkpoint,frozen)


def test_phase_failure_propagates(admitted,tmp_path,monkeypatch):
    prompts,model,checkpoint,frozen,_=admitted
    def failed(*args):raise RuntimeError('phase timeout')
    monkeypatch.setattr(cycle,'run_processes',failed)
    with pytest.raises(RuntimeError,match='phase timeout'):
        cycle.execute(tmp_path/'run',prompts,model,checkpoint,frozen)


@pytest.fixture
def arm(admitted,tmp_path,monkeypatch):
    from tools import proof_cuda_eval
    _,_,_,frozen,_=admitted
    path=tmp_path/'base';path.mkdir()
    config=dict(frozen['admissions']['base'],restore_exact=True)
    rows=[dict(id=str(i),status='generated',token_ids=[i],raw_reply='reply') for i in range(14)]
    tasks=[dict(id=str(i)) for i in range(14)]
    summary=dict(termination='complete')
    def write():
        (path/'config.json').write_text(json.dumps(config))
        (path/'summary.json').write_text(json.dumps(summary))
        (path/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    write();checks=[]
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *a,**kw:object())))
    monkeypatch.setattr(cycle.probe,'validate_run',lambda *a:tasks)
    monkeypatch.setattr(proof_cuda_eval,'validate_tokenization',lambda tok,t,r:checks.append(t['id']))
    monkeypatch.setattr(proof_cuda_eval,'decode_reply',lambda tok,ids:'reply')
    return path,frozen,config,rows,summary,write,checks


def test_checks_all14_raw_reconstructions(arm):
    path,frozen,_,_,_,_,checks=arm
    result=cycle.check_arm(path,b'{}',frozen,'base')
    assert checks==list(map(str,range(14)))
    assert result['completed_rows']==14 and result['generated_tasks']==14 and result['verification_pending']


def test_time_limited_rows_reported_not_success(arm):
    path,frozen,_,rows,_,write,_=arm
    rows[0]['status']='generation_time_limit';write()
    result=cycle.check_arm(path,b'{}',frozen,'base')
    assert result['generated_tasks']==13 and result['unmeasured_time_limits']==1


def test_partial_denominator_rejected(arm):
    path,frozen,_,rows,summary,write,_=arm
    rows.pop();summary['termination']='phase_timeout';write()
    with pytest.raises(ValueError,match='Incomplete generation'):
        cycle.check_arm(path,b'{}',frozen,'base')


def test_raw_reply_drift_rejected(arm):
    path,frozen,_,rows,_,write,_=arm
    rows[0]['raw_reply']='changed';write()
    with pytest.raises(ValueError,match='reply reconstruction'):
        cycle.check_arm(path,b'{}',frozen,'base')


def test_run_config_drift_rejected(arm):
    path,frozen,config,_,_,write,_=arm
    config['prompts_sha256']='changed';write()
    with pytest.raises(ValueError,match='frozen production admission'):
        cycle.check_arm(path,b'{}',frozen,'base')


def test_pbs_bounded_account_and_no_training():
    pbs=(cycle.ROOT/'tools/proof_cuda_fresh_cycle.pbs').read_text()
    for expected in ('#PBS -A EVITA','#PBS -q debug','#PBS -l select=1:system=polaris',
                     '#PBS -l walltime=01:00:00','3420s','--kill-after=20s','set -euo pipefail'):
        assert expected in pbs
    assert 'proof_cuda_fresh_cycle.py' in pbs and 'proof_cuda_train.py' not in pbs
