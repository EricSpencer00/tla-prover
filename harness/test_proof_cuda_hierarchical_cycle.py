import json
from pathlib import Path
import sys
from types import SimpleNamespace
import pytest
from tools import proof_cuda_hierarchical_cycle as cycle


def test_pinned_snapshot_filesystem_alias_resolves_on_both_sides(tmp_path,monkeypatch):
    actual=tmp_path/'canonical';actual.mkdir()
    alias=tmp_path/'grand';alias.symlink_to(actual,target_is_directory=True)
    monkeypatch.setattr(cycle,'MODEL_PATH',alias)
    cycle.validate_model_path(alias)
    cycle.validate_model_path(actual)
    other=tmp_path/'other';other.mkdir()
    with pytest.raises(ValueError,match='Exact original'):
        cycle.validate_model_path(other)
    with pytest.raises(FileNotFoundError):
        cycle.validate_model_path(tmp_path/'absent')


def training_fixture(tmp_path):
    frozen=dict(model_files={'weights':'hash'},train_input_sha256='input',
        train_ids=[str(i) for i in range(17)],train_evidence={'controlled':True},
        implementation_sha256={name:'sha' for name in cycle.TRAIN_SOURCES})
    config=dict(model_files=frozen['model_files'],input_sha256='input',train_ids=frozen['train_ids'],
        evidence=frozen['train_evidence'],dtype_profile=cycle.PROFILE,requested_updates=100,seconds=600,
        seed=20260925,lr=1e-5,max_tokens=8192,implementation_sha256=frozen['implementation_sha256'])
    (tmp_path/'config.json').write_text(json.dumps(config))
    (tmp_path/'policy_optimizer.pt').write_bytes(b'test-child')
    steps=[dict(step=i+1,task=str(i),loss=1.,gradient_norm=1.) for i in range(17)]
    (tmp_path/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in steps))
    summary=dict(reload_tensors_exact=True,reload_logits_exact=True,evaluation_responses_forwarded=0,
        train_tasks=17,attempted_train_tasks=17,updates=17,requested_updates=100,
        parameter_delta_l2=.1,cuda_peak_allocated=20*1024**3,cuda_peak_reserved=21*1024**3,
        checkpoint_sha256=cycle.file_sha(tmp_path/'policy_optimizer.pt'))
    (tmp_path/'summary.json').write_text(json.dumps(summary))
    return frozen,summary


def test_full17_gate_not_leaf50_gate(tmp_path):
    frozen,summary=training_fixture(tmp_path)
    assert cycle.check_training(tmp_path,frozen)['updates']==17


@pytest.mark.parametrize('field,value',[('updates',16),('attempted_train_tasks',16),('train_tasks',50),
    ('reload_logits_exact',False),('reload_tensors_exact',False),('parameter_delta_l2',0),
    ('parameter_delta_l2',float('nan')),('cuda_peak_reserved',37*1024**3),('evaluation_responses_forwarded',1)])
def test_bad_training_cannot_advance(tmp_path,field,value):
    frozen,summary=training_fixture(tmp_path);summary[field]=value
    (tmp_path/'summary.json').write_text(json.dumps(summary))
    with pytest.raises(ValueError):cycle.check_training(tmp_path,frozen)


def test_optimizer_ledger_must_really_cover_every_task(tmp_path):
    frozen,summary=training_fixture(tmp_path)
    steps=[dict(step=i+1,task='0',loss=1.,gradient_norm=1.) for i in range(17)]
    (tmp_path/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in steps))
    with pytest.raises(ValueError,match='all17'):cycle.check_training(tmp_path,frozen)


def test_probe_checks_exact_checkpoint_and_all_tokens(tmp_path,monkeypatch):
    frozen=dict(model_files={'weights':'sha'},prompts_sha256='prompts',
        implementation_sha256={name:'source' for name in cycle.IMPLEMENTATION})
    config=dict(**frozen,checkpoint_sha256=cycle.LEAF_SHA,arm='checkpoint',torch_version='x',transformers_version='y')
    (tmp_path/'config.json').write_text(json.dumps(config))
    summary=dict(returncode=0,termination='complete')
    (tmp_path/'summary.json').write_text(json.dumps(summary))
    rows=[dict(id=str(i),status='generated') for i in range(21)]
    (tmp_path/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    monkeypatch.setattr(cycle,'validate_run',lambda *args:rows)
    seen=[];monkeypatch.setattr(cycle,'validate_tokenization',lambda tok,task,row:seen.append(row['id']))
    assert cycle.check_probe(tmp_path,b'',frozen,cycle.LEAF_SHA,object())['generated']==21
    assert seen==[str(i) for i in range(21)]
    with pytest.raises(ValueError,match='checkpoint_sha256'):cycle.check_probe(tmp_path,b'',frozen,'wrong',object())
    summary['termination']='phase_timeout';(tmp_path/'summary.json').write_text(json.dumps(summary))
    with pytest.raises(ValueError,match='Complete21'):cycle.check_probe(tmp_path,b'',frozen,cycle.LEAF_SHA,object())


@pytest.mark.parametrize('bad_parent',[False,True])
def test_cli_parallel_parents_before_fresh_training(tmp_path,monkeypatch,bad_parent):
    train=tmp_path/'train.json';train.write_text('{}')
    prompts=tmp_path/'prompts.json';prompts.write_text('{}')
    leaf=tmp_path/'leaf.pt';leaf.write_bytes(b'old')
    out=tmp_path/'new'
    monkeypatch.setattr(sys,'argv',['cycle','--train-input',str(train),'--prompts',str(prompts),
        '--leaf-checkpoint',str(leaf),'--output',str(out)])
    frozen=dict(train_input_sha256='train');monkeypatch.setattr(cycle,'freeze',lambda *a:frozen)
    monkeypatch.setattr(cycle,'unchanged',lambda *a:None)
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(
        AutoTokenizer=SimpleNamespace(from_pretrained=lambda *a,**kw:object())))
    events=[]
    monkeypatch.setattr(cycle,'run_processes',lambda commands,logs,seconds:events.append(commands))
    def probe(path,*args):
        if bad_parent and path.name=='leaf':raise ValueError('Incomplete parent')
        return dict(model_files={},prompts_sha256='prompts',torch_version='test',transformers_version='test')
    monkeypatch.setattr(cycle,'check_probe',probe)
    monkeypatch.setattr(cycle,'check_training',lambda *a:dict(checkpoint_sha256='new-child'))
    if bad_parent:
        with pytest.raises(ValueError):cycle.main()
        assert len(events)==1
        assert json.loads((out/'failure.json').read_text())['completed_phases']==[]
    else:
        cycle.main();assert len(events)==3
        traincmd=events[1][0]
        assert traincmd[2]=='train' and '--checkpoint' not in traincmd and '--resume' not in traincmd
        assert traincmd[traincmd.index('--steps')+1]=='100'
        assert events[2][0][-1]==str(out/'training/policy_optimizer.pt')
        assert json.loads((out/'summary.json').read_text())['official_evaluation_tasks']==0
    assert len(events[0])==2 and '--checkpoint' not in events[0][0]
    assert events[0][1][-1]==str(leaf)
    assert leaf.read_bytes()==b'old'
