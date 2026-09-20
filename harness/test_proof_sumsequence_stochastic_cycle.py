import copy
import json
from types import SimpleNamespace
import pytest
from tools import proof_sumsequence_stochastic_cycle as c


@pytest.fixture
def prepared(tmp_path,monkeypatch):
    a=SimpleNamespace(broader_prompts=c.ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json',
        model_path=tmp_path/'model',parent_checkpoint=tmp_path/'parent.pt',child_checkpoint=tmp_path/'child.pt',
        output=tmp_path/'run',freeze=tmp_path/'freeze.json')
    a.output.mkdir()
    monkeypatch.setattr(c,'sources',lambda:{})
    def admit(args):
        return dict(evaluation=c.sampling.derive_requests(args.broader_prompts.read_bytes(),args.arm),
            checkpoint_sha256=c.sampling.POLICIES[args.arm],encodings=[{'id':i} for i in range(8)],
            model_files={},model_files_sha256='model',versions={},dtype_profile='fixture',eos_token_ids=[1])
    monkeypatch.setattr(c.sampling,'admit',admit)
    frozen=c.freeze(a);c.dump(a.freeze,frozen)
    return a,frozen


def process():
    return dict(returncode=0,output='',seconds=1,execution_complete=True,
        cleanup_complete=True,output_complete=True,timed_out=False)


def generate(a):
    a.output.mkdir()
    (a.output/'rollouts.jsonl').write_text('fixture raw ledger\n')
    c.dump(a.output/'process.json',process())
    result=dict(phase_complete=True,requested_samples=32,accounted_samples=32,
        generated_samples=32,unattempted_sample_ids=[],optimizer_updates=0,
        checkpoint_sha256=c.sampling.POLICIES[a.arm],
        process_sha256=c.file_sha(a.output/'process.json'),
        rollouts_sha256=c.file_sha(a.output/'rollouts.jsonl'))
    c.dump(a.output/'summary.json',result)
    return result


def test_full_admission_compares_inputs(prepared):
    a,frozen=prepared
    c.validate_freeze(a,frozen)
    frozen['arms']['child']['encodings'][0]['id']=99
    with pytest.raises(ValueError,match='Matched'):c.validate_freeze(a,frozen)


@pytest.mark.parametrize('field,value',[('seconds',3600),('requested_samples',32),('optimizer_updates',1),
    ('phase_order',['child','parent']),('sources',{'drift':'yes'})])
def test_frozen_contract_not_weakened(prepared,field,value):
    a,frozen=prepared;frozen[field]=value
    with pytest.raises(ValueError,match='frozen'):c.validate_freeze(a,frozen)


def test_paired_order_and_complete_accounting(prepared,monkeypatch):
    a,frozen=prepared;calls=[]
    def run(args):calls.append(args.arm);return generate(args)
    monkeypatch.setattr(c.sampling,'generate',run)
    result=c.execute(a)
    assert calls==['parent','child'] and result['complete']
    assert result['requested_samples']==64 and result['optimizer_updates']==0
    assert result['unattempted_sample_ids']=={'parent':[],'child':[]}


@pytest.mark.parametrize('field,value',[('phase_complete',False),('generated_samples',31),
    ('checkpoint_sha256','wrong'),('optimizer_updates',1),('unattempted_sample_ids',['missing'])])
def test_parent_failure_never_advances(prepared,monkeypatch,field,value):
    a,frozen=prepared;calls=[]
    def run(args):
        calls.append(args.arm);result=generate(args);result[field]=value
        c.dump(args.output/'summary.json',result);return result
    monkeypatch.setattr(c.sampling,'generate',run)
    with pytest.raises(ValueError,match='raw arm'):c.execute(a)
    assert calls==['parent']
    state=json.loads((a.output/'summary.json').read_text())
    assert not state['complete'] and len(state['unattempted_sample_ids']['child'])==32


def test_returned_summary_cannot_differ_from_disk(prepared,monkeypatch):
    a,_=prepared
    def run(args):result=generate(args);result['invented']=True;return result
    monkeypatch.setattr(c.sampling,'generate',run)
    with pytest.raises(ValueError,match='raw arm'):c.execute(a)


def test_cleanup_failure_blocks_next_arm(prepared,monkeypatch):
    a,_=prepared
    def run(args):
        result=generate(args);p=process();p['cleanup_complete']=False
        c.dump(args.output/'process.json',p)
        result['process_sha256']=c.file_sha(args.output/'process.json')
        c.dump(args.output/'summary.json',result);return result
    monkeypatch.setattr(c.sampling,'generate',run)
    with pytest.raises(ValueError,match='cleanup'):c.execute(a)


def test_no_shortened_second_arm(prepared,monkeypatch):
    a,_=prepared;calls=[]
    def run(args):calls.append(args.arm);return generate(args)
    monkeypatch.setattr(c.sampling,'generate',run)
    ticks=iter([0,0,2000,2000])
    with pytest.raises(TimeoutError,match='shortened'):c.execute(a,clock=lambda:next(ticks))
    assert calls==['parent']


def test_outer_zero_exit_not_success(prepared,monkeypatch):
    a,_=prepared;a.output=a.output.parent/'outer'
    monkeypatch.setattr(c,'run_owned',lambda *a:process())
    with pytest.raises(RuntimeError,match='incomplete'):c.supervise(a)
    state=json.loads((a.output/'summary.json').read_text())
    assert sum(map(len,state['unattempted_sample_ids'].values()))==64


def test_partial_accounting_preserves_attempted_worker_error(prepared):
    a,frozen=prepared;output=a.output/'parent';output.mkdir()
    requests=frozen['arms']['parent']['evaluation']['requests']
    rows=[c.sampling.unknown(r) for r in requests]
    rows[0]=c.sampling.unknown(requests[0],'actual worker failure',status='worker_error')
    (output/'rollouts.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    state=c.initial_state(frozen);c.partial_accounting(a.output,frozen,state)
    assert len(state['unattempted_sample_ids']['parent'])==31
    assert state['partial_accounting']['parent']['worker_error_sample_ids']==[requests[0]['sample_id']]


def test_invalid_partial_ledger_is_unknown_not_unattempted(prepared):
    a,frozen=prepared;output=a.output/'parent';output.mkdir()
    (output/'rollouts.jsonl').write_text('{broken')
    state=c.initial_state(frozen);c.partial_accounting(a.output,frozen,state)
    assert state['unattempted_sample_ids']['parent'] is None
    assert len(state['partial_accounting']['parent']['unknown_sample_ids'])==32
