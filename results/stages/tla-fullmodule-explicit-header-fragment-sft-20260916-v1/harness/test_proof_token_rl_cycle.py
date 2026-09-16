"""Cycle tests never launch models, checkers, queues, or subprocesses."""
import json
import sys
from types import SimpleNamespace

import pytest

from tools import proof_token_rl_cycle as c


@pytest.fixture
def setup(tmp_path, monkeypatch):
    model=tmp_path/'model';model.mkdir()
    req=tmp_path/'requests';req.write_bytes(b'requests')
    prompts=tmp_path/'prompts';prompts.write_bytes(b'prompts')
    parent=tmp_path/'parent';parent.write_bytes(b'parent')
    out=tmp_path/'output'
    monkeypatch.setattr(c,'MODEL',model)
    monkeypatch.setattr(c,'file_sha',lambda p:c.POLICY_SHA)
    calls=[]
    packet={'requests':list(range(32))}
    def load(raw, sha, **kwargs):
        calls.append((raw,sha,kwargs));return packet
    monkeypatch.setattr(c,'load_requests',load)
    admission=dict(checkpoint_sha256=c.POLICY_SHA,requested_task_ids=list(range(36)),
                   model_files={'x':'y'},input_evidence=list(range(36)))
    monkeypatch.setattr(c.probe,'admit',lambda *a:admission)
    worker=SimpleNamespace(SOURCES=('tools/proof_token_rl_worker.py',),admit=lambda a:{'worker':'admitted'},
                           validate_training=lambda *a:dict(actual_updates=0,eligible_groups=0,checkpoint_sha256=None))
    monkeypatch.setattr(c,'worker_module',lambda:worker)
    frozen=c.freeze(req,prompts,model,parent,out)
    return SimpleNamespace(req=req,prompts=prompts,model=model,parent=parent,out=out,
                           frozen=frozen,calls=calls,worker=worker,packet=packet)


def test_freeze_full_packet_model_worker_and_sources(setup):
    s=setup
    assert s.calls==[(b'requests',c.REQUESTS_SHA,{'broader_raw':b'prompts'})]
    assert s.frozen['requested_rollouts']==32 and s.frozen['requested_retention_tasks']==36
    assert set(s.frozen['implementation_sha256'])==set(c.SOURCES)|set(c.probe.IMPLEMENTATION)|set(s.worker.SOURCES)


def test_mount_alias_both_sides_resolved(setup,tmp_path):
    s=setup;alias=tmp_path/'alias';alias.symlink_to(s.model)
    assert c.freeze(s.req,s.prompts,alias,s.parent,s.out)==s.frozen


def test_wrong_parent_rejected(setup,monkeypatch):
    monkeypatch.setattr(c,'file_sha',lambda p:'wrong')
    with pytest.raises(ValueError,match='parent'):c.freeze(setup.req,setup.prompts,setup.model,setup.parent,setup.out)


@pytest.mark.parametrize('updates',[0,1])
def test_update_and_zero_update_select_exact_policy(setup,monkeypatch,updates):
    s=setup;calls=[]
    s.out.mkdir()
    monkeypatch.setattr(c,'run_processes',lambda commands,logs,seconds:calls.append((commands,logs,seconds)))
    monkeypatch.setattr(c,'check_training',lambda *a:{'summary':{'actual_updates':updates,'checkpoint_sha256':c.POLICY_SHA}})
    checked=[]
    monkeypatch.setattr(c,'check_retention',lambda *a:checked.append(a) or {'accounted_tasks':36})
    result=c.execute(s.out,s.req,s.prompts,s.model,s.parent,s.frozen,clock=lambda:0)
    assert [x[2] for x in calls]==[1700,1220]
    selected=s.out/'training'/'policy_optimizer.pt' if updates else s.parent
    command=calls[1][0][0]
    assert command[command.index('--checkpoint')+1]==str(selected)
    assert checked[0][-1]==selected
    assert result['proof_success_claim'] is False and result['learning_improvement_claim'] is False
    assert result['retention']['accounted_tasks']==36


def test_worker_failure_runs_parent_diagnostic_but_fails(setup,monkeypatch):
    s=setup;calls=[]
    s.out.mkdir()
    def run(commands,logs,seconds):
        calls.append(commands)
        if len(calls)==1:raise RuntimeError('worker died')
    monkeypatch.setattr(c,'run_processes',run)
    monkeypatch.setattr(c,'check_retention',lambda *a:{'accounted_tasks':36})
    with pytest.raises(RuntimeError,match='parent retention preserved'):
        c.execute(s.out,s.req,s.prompts,s.model,s.parent,s.frozen,clock=lambda:0)
    assert str(s.parent) in calls[1][0]
    result=json.loads((s.out/'summary.json').read_text())
    assert result['training'] is None and result['status']=='worker_failed_parent_retention_complete'
    assert json.loads((s.out/'training_failure.json').read_text())['zero_eligibility_claim'] is False


def test_drift_blocks_retention(setup,monkeypatch):
    s=setup;calls=[]
    s.out.mkdir()
    monkeypatch.setattr(c,'run_processes',lambda *a:calls.append(a))
    monkeypatch.setattr(c,'freeze',lambda *a:{'changed':True})
    with pytest.raises(ValueError,match='Frozen'):
        c.execute(s.out,s.req,s.prompts,s.model,s.parent,s.frozen,clock=lambda:0)
    assert len(calls)==1


def test_total_deadline_bounds_retention(setup,monkeypatch):
    s=setup;now=[0];budgets=[]
    s.out.mkdir()
    def run(commands,logs,seconds):budgets.append(seconds);now[0]+=2500
    monkeypatch.setattr(c,'run_processes',run)
    monkeypatch.setattr(c,'check_training',lambda *a:{'summary':{'actual_updates':0}})
    monkeypatch.setattr(c,'check_retention',lambda *a:{})
    with pytest.raises(TimeoutError):
        c.execute(s.out,s.req,s.prompts,s.model,s.parent,s.frozen,clock=lambda:now[0])
    assert budgets==[1700,800]


@pytest.mark.parametrize('updates,eligible,sha,valid',[(0,0,None,True),(0,1,None,False),(0,0,'child',False),(2,1,'child',False),(True,0,None,False),(1,1,c.POLICY_SHA,True),(1,1,'wrong',False)])
def test_training_count_and_checkpoint_guards(setup,monkeypatch,updates,eligible,sha,valid):
    s=setup;s.out.mkdir();(s.out/'rollouts.jsonl').write_text('{}\n')
    s.worker.validate_training=lambda *a:dict(actual_updates=updates,eligible_groups=eligible,checkpoint_sha256=sha)
    monkeypatch.setattr(c,'validate_rollouts',lambda *a,**k:{'accounted_samples':32})
    if valid:assert c.check_training(s.out,s.frozen,s.packet)['rollout_accounting']['accounted_samples']==32
    else:
        with pytest.raises(ValueError):c.check_training(s.out,s.frozen,s.packet)


def test_missing_rollout_accounting_rejected(setup,monkeypatch):
    s=setup;s.out.mkdir();(s.out/'rollouts.jsonl').write_text('{}\n')
    monkeypatch.setattr(c,'validate_rollouts',lambda *a,**k:{'accounted_samples':31})
    with pytest.raises(ValueError,match='All32'):c.check_training(s.out,s.frozen,s.packet)


def test_admit_only_does_not_create_output(setup,monkeypatch,capsys):
    s=setup
    monkeypatch.setattr(sys,'argv',['cycle','--requests',str(s.req),'--broader-prompts',str(s.prompts),
        '--model-path',str(s.model),'--checkpoint',str(s.parent),'--output',str(s.out),'--admit-only'])
    c.main()
    assert not s.out.exists()
    assert json.loads(capsys.readouterr().out)['requested_retention_tasks']==36


def test_pbs_bounded_debug_profile():
    script=(c.ROOT/'tools/proof_token_rl_cycle.pbs').read_text()
    for value in ('#PBS -A EVITA','#PBS -q debug','select=1:system=polaris','walltime=01:00:00','3300s','--kill-after=20s'):
        assert value in script


@pytest.mark.parametrize('count,changed,reply_ok',[(36,False,True),(35,False,True),(36,True,True),(36,False,False)])
def test_retention_full_accounting_and_exact_bytes(setup,monkeypatch,count,changed,reply_ok):
    from tools import proof_cuda_eval as base
    s=setup;s.out.mkdir()
    config=dict(s.frozen['retention_admission'],restore_exact=True)
    if changed:config['checkpoint_sha256']='wrong'
    (s.out/'config.json').write_text(json.dumps(config))
    (s.out/'summary.json').write_text(json.dumps(dict(returncode=0,termination='complete')))
    rows=[dict(status='generated',token_ids=[1],raw_reply='literal') for _ in range(count)]
    (s.out/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *a,**k:object())))
    monkeypatch.setattr(c.probe,'validate_run',lambda *a:list(range(count)))
    checked=[]
    monkeypatch.setattr(base,'validate_tokenization',lambda *a:checked.append(a))
    monkeypatch.setattr(base,'decode_reply',lambda *a:'literal' if reply_ok else 'changed')
    if count==36 and not changed and reply_ok:
        result=c.check_retention(s.out,s.prompts,s.frozen,s.parent)
        assert len(checked)==36 and result['generated_tasks']==36 and result['verification_pending']
    else:
        with pytest.raises(ValueError):c.check_retention(s.out,s.prompts,s.frozen,s.parent)
