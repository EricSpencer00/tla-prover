import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import pytest
from tools import proof_sany_repair_learning_eval as module


@pytest.fixture
def frozen():
    root=module.ROOT/'results/runs'
    first=module.load(root/'proof-sumsequence-proof-rl-eval-20260906-v1/admission.json')
    second=module.load(root/'proof-sany-repair-eval-20260906-v1/admission.json')
    return dict(checkpoint_sha256='a'*64,phases={
        'greedy40':dict(budget=module.BUDGETS['greedy40'],requested=40,encodings=first['encodings']),
        'repair2':dict(budget=module.BUDGETS['repair2'],requested=2,encodings=second['encodings'])})


@pytest.fixture
def rows():
    root=module.ROOT/'results/runs'
    return dict(greedy40=module.load(root/'proof-sumsequence-proof-rl-eval-20260906-v1/accounting.json'),
                repair2=module.load(root/'proof-sany-repair-eval-20260906-v1/accounting.json'))


def test_original_phase_budgets_and_actual_rows(frozen,rows):
    assert module.BUDGETS['greedy40']['max_context']==8192
    assert module.BUDGETS['greedy40']['seed']==20260930
    assert module.BUDGETS['repair2']['max_context']==9216
    assert module.BUDGETS['repair2']['seed']==20261005
    for phase in module.PHASES:module.validate_rows(frozen,phase,rows[phase])
    assert module.SECONDS<=3000


@pytest.mark.parametrize('phase',module.PHASES)
def test_unknown_keys_retained(frozen,phase):
    rows=[module.base.unknown(e) for e in frozen['phases'][phase]['encodings']]
    module.validate_rows(frozen,phase,rows)
    assert module.accounting(rows)['unknown']==len(rows)
    assert module.accounting(rows)['generated']==0


@pytest.mark.parametrize('change',[
    lambda r:r.reverse(),lambda r:r.pop(),lambda r:r[0].update(id='foreign'),
    lambda r:r[0].update(raw_reply='fabricated'),lambda r:r[0].update(prompt_sha256='0'*64),
    lambda r:r[0].update(token_ids=[1,2]),lambda r:r[0].update(status='pass')])
def test_changed_generation_rejected(frozen,rows,change):
    actual=rows['greedy40'];change(actual)
    with pytest.raises((ValueError,KeyError)):module.validate_rows(frozen,'greedy40',actual)


def test_mixed_phases_cannot_pool(frozen,rows):
    with pytest.raises(ValueError):module.validate_rows(frozen,'greedy40',rows['greedy40']+rows['repair2'])
    with pytest.raises(ValueError):module.validate_rows(frozen,'repair2',rows['greedy40'][:2])


def test_same_phase_different_budget_rejected(frozen,rows):
    frozen['phases']['greedy40']['budget']=dict(module.BUDGETS['greedy40'],max_context=9216)
    with pytest.raises(ValueError):module.validate_rows(frozen,'greedy40',rows['greedy40'])


def test_baseline_pin_covers_all_saved_artifacts():
    root=module.ROOT/'results/runs'
    for phase,name in [('greedy40','proof-sumsequence-proof-rl-eval-20260906-v1'),
                       ('repair2','proof-sany-repair-eval-20260906-v1')]:
        assert module.digest(module.base.inventory(root/name))==module.BASELINE_SHA[phase]


def test_changed_baseline_tree_rejected(tmp_path):
    (tmp_path/'accounting.json').write_text('[]')
    with pytest.raises(ValueError,match='baseline tree'):
        module.baseline(tmp_path,'greedy40',None,[])


def test_reserve_scales_actual_admission():
    assert module.reserve(2)==30 and module.reserve(80)==100
    assert module.phase_seconds('greedy40')==1000 and module.phase_seconds('repair2')==1200


def test_actual_training_uses_new_sft_validator(monkeypatch,tmp_path):
    args=type('Args',(),{})()
    for name in module.PATHS:setattr(args,name,tmp_path/name)
    args.expected_input_sha256='a'*64
    monkeypatch.setattr(module,'load',lambda path:{})
    def reject(a,frozen):raise ValueError('New SFT checkpoint validation invoked')
    monkeypatch.setattr(module.learning,'validate_output',reject)
    with pytest.raises(ValueError,match='New SFT checkpoint'):
        module.training_receipt(args,dict(training_admission={}))


def test_no_new_child_required_for_prospective_source():
    # Explicitly keep expensive child restoration in final admit, not prospective.
    import inspect
    text=inspect.getsource(module.prospective_admit)
    assert 'a.checkpoint' not in text and 'training_receipt' not in text
    assert 'learning.admit' in text and 'baseline(' in text


def test_isolated_declared_source_import_closure(tmp_path):
    for name in module.SOURCES:
        path=module.ROOT/name
        assert path.is_file(),name
        destination=tmp_path/name;destination.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(path,destination)
    result=subprocess.run([sys.executable,'-I','-c',
        'import sys;sys.path.insert(0,".");from tools import proof_sany_repair_learning_eval as e;'
        'assert e.PHASES==("greedy40","repair2"); assert len(e.SOURCES)>=74'],
        cwd=tmp_path,capture_output=True,text=True,timeout=30)
    assert result.returncode==0,result.stderr


@pytest.fixture
def complete_worker(tmp_path,frozen,rows):
    import torch
    rng={}
    for phase in module.PHASES:
        directory=tmp_path/phase;directory.mkdir()
        module.dump(directory/'accounting.json',rows[phase])
        (directory/'events.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows[phase]))
        rng[phase]={}
        for label in ('before','after'):
            path=directory/('rng_'+label+'.pt')
            torch.save(dict(seed=module.BUDGETS[phase]['seed'],cpu=torch.zeros(8,dtype=torch.uint8),
                            cuda=torch.zeros(8,dtype=torch.uint8)),path)
            rng[phase][label]=module.file_sha(path)
    phases=['after_model_load','after_checkpoint_restore']+[
        phase+'_sample_'+str(i) for phase in module.PHASES for i in range(len(rows[phase]))]+['after_final_admission']
    memory=dict(allocated=10,reserved=20)
    module.dump(tmp_path/'memory_events.json',[dict(phase=p,**memory) for p in phases])
    module.dump(tmp_path/'memory.json',memory)
    summary=dict(complete=True,phases={p:module.accounting(rows[p]) for p in module.PHASES},
        phase_seconds=dict(greedy40=10,repair2=10),rng_sha256=rng,elapsed_seconds=60,
        pre_admission_seconds=2,post_admission_reserve_seconds=30,memory=memory,
        weights_unchanged=True,restore_exact=True,full_admission_stable=True,
        checkpoint_sha256=frozen['checkpoint_sha256'],optimizer_updates=0,verification_pending=True,pooled_pass_at1_claim=False)
    module.dump(tmp_path/'worker_summary.json',summary)
    return tmp_path,summary


def test_complete_worker_raw_phase_validation(complete_worker,frozen,rows):
    output,_=complete_worker
    assert module.validate_worker(frozen,output)==rows


@pytest.mark.parametrize('change',[
    lambda s:s.update(checkpoint_sha256=module.PARENT_SHA),
    lambda s:s.update(optimizer_updates=1),lambda s:s.update(weights_unchanged=False),
    lambda s:s.update(pooled_pass_at1_claim=True),lambda s:s.update(elapsed_seconds=3001),
    lambda s:s['phase_seconds'].update(greedy40=1001),
    lambda s:s.update(post_admission_reserve_seconds=0),
    lambda s:s['phases']['repair2'].update(requested=40),
])
def test_worker_receipt_mutations_rejected(complete_worker,frozen,change):
    output,summary=complete_worker;change(summary);module.dump(output/'worker_summary.json',summary)
    with pytest.raises(ValueError):module.validate_worker(frozen,output)


def test_missing_memory_phase_rejected(complete_worker,frozen):
    output,_=complete_worker
    events=module.load(output/'memory_events.json');events.pop(3);module.dump(output/'memory_events.json',events)
    with pytest.raises(ValueError,match='memory'):module.validate_worker(frozen,output)


def test_rng_raw_mutation_rejected(complete_worker,frozen):
    output,_=complete_worker
    (output/'repair2/rng_before.pt').write_bytes(b'changed')
    with pytest.raises(ValueError,match='RNG'):module.validate_worker(frozen,output)


def test_exact_42_keys_persist_before_admission_failure(tmp_path,monkeypatch):
    a=type('Args',(),{})();a.output=tmp_path/'out'
    for name in (*module.PATHS,'admission','prospective'):setattr(a,name,tmp_path/(name+'.input'))
    a.expected_input_sha256='a'*64
    a.admission.write_text('{}')
    def reject(*args):raise ValueError('Preflight rejected')
    monkeypatch.setattr(module,'admit',reject)
    with pytest.raises(ValueError,match='Preflight'):module.generate(a)
    for phase in module.PHASES:
        actual=module.load(a.output/phase/'accounting.json')
        assert [r['id'] for r in actual]==module.requested_ids(phase)
        assert all(r['status']=='unattempted' for r in actual)
