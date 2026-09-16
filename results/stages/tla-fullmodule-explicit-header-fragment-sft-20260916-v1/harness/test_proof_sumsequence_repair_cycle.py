import json
from types import SimpleNamespace
import pytest
from tools import proof_sumsequence_repair_cycle as module


def trained_output(output):
    output.mkdir()
    child=output/'policy_optimizer.pt';child.write_bytes(b'new checkpoint')
    summary=dict(complete=True,actual_updates=80,parent_checkpoint_sha256=module.evaluate.PARENT_SHA,
                 checkpoint_sha256=module.file_sha(child))
    module.dump(output/'summary.json',summary)
    module.dump(output/'process.json',dict(returncode=0,output='',seconds=1,
        execution_complete=True,cleanup_complete=True,output_complete=True,timed_out=False))
    module.dump(output/'admitted.json',dict(complete=True,
        summary_sha256=module.file_sha(output/'summary.json'),
        process_sha256=module.file_sha(output/'process.json')))
    return summary


@pytest.fixture
def prepared(tmp_path,monkeypatch):
    a=SimpleNamespace(input=tmp_path/'train.json',prompts=tmp_path/'prompts.json',
        model_path=tmp_path/'model',checkpoint=tmp_path/'parent.pt',
        output=tmp_path/'run',freeze=tmp_path/'freeze.json')
    a.input.write_bytes(b'train');a.prompts.write_bytes(b'prompts')
    a.train_sha=module.file_sha(a.input);a.prompts_sha=module.file_sha(a.prompts)
    a.output.mkdir()
    encodings=[];inputs=[]
    for i in range(40):
        j=i+4 if 32<=i<36 else i
        encodings.append(dict(input_ids=[j,100],prompt_tokens=1,rendered_prompt=str(j)))
        inputs.append(dict(id=str(i),input_token_ids=[i],rendered_prompt=str(i)))
    training=dict(model_files={'x':'y'},versions={'v':'x'},encodings=encodings)
    parent=dict(model_files={'x':'y'},versions={'v':'x'},input_evidence=inputs)
    monkeypatch.setattr(module,'source_identity',lambda:{})
    monkeypatch.setattr(module.train,'admit',lambda a:training)
    monkeypatch.setattr(module.evaluate,'admit',lambda a:parent)
    frozen=module.freeze(a);module.dump(a.freeze,frozen)
    return a,training,parent


def test_freeze_exact_training_inference_binding(prepared):
    a,training,_=prepared
    module.freeze(a)
    training['encodings'][32]['input_ids'][0]=999
    with pytest.raises(ValueError,match='prefix mismatch'):module.freeze(a)


def test_changed_sources_block(prepared,monkeypatch):
    a,_,_=prepared
    monkeypatch.setattr(module,'source_identity',lambda:{'changed':'hash'})
    with pytest.raises(ValueError,match='inputs/source'):
        module.validate_freeze(a,json.loads(a.freeze.read_text()))


def test_failed_parent_never_trains(prepared,monkeypatch):
    a,_,_=prepared
    monkeypatch.setattr(module.evaluate,'generate',lambda a:{'complete':False})
    monkeypatch.setattr(module.train,'supervise',lambda a:pytest.fail('Unexpected optimizer run'))
    with pytest.raises(ValueError,match='parent baseline'):
        module.execute(a)
    result=json.loads((a.output/'summary.json').read_text())
    assert not result['complete'] and len(result['unattempted_task_ids']['child'])==40


def test_validated_child_links_after_training(prepared,monkeypatch):
    a,_,_=prepared;calls=[]
    def generate(args):
        calls.append(args.role)
        return dict(complete=True,unattempted_ids=[])
    def train(args):
        calls.append('train')
        return trained_output(args.output)
    monkeypatch.setattr(module.evaluate,'generate',generate)
    monkeypatch.setattr(module.train,'supervise',train)
    module.execute(a)
    assert calls==['parent','train','child']
    result=json.loads((a.output/'summary.json').read_text())
    assert result['complete'] and result['proof_verification_pending']
    assert json.loads((a.output/'training-linkage.json').read_text())['validated']


def test_insufficient_time_never_shortens_training(prepared,monkeypatch):
    a,_,_=prepared
    monkeypatch.setattr(module.evaluate,'generate',lambda a:{'complete':True,'unattempted_ids':[]})
    monkeypatch.setattr(module.train,'supervise',lambda a:pytest.fail('Training lacks full reserve'))
    times=iter([0,0,1300,1300])
    with pytest.raises(TimeoutError,match='remaining cycle budget'):
        module.execute(a,clock=lambda:next(times))


def test_unvalidated_checkpoint_never_evaluated(prepared,monkeypatch):
    a,_,_=prepared;calls=[]
    monkeypatch.setattr(module.evaluate,'generate',lambda a:calls.append(a.role) or {'complete':True,'unattempted_ids':[]})
    def bad(args):
        summary=trained_output(args.output)
        (args.output/'policy_optimizer.pt').write_bytes(b'other')
        return summary
    monkeypatch.setattr(module.train,'supervise',bad)
    with pytest.raises(ValueError,match='Validated actual child'):
        module.execute(a)
    assert calls==['parent']


@pytest.mark.parametrize('mutation',['receipt','summary_hash','process_hash','cleanup','returned_summary'])
def test_invalid_receipt_with_matching_checkpoint_blocks_child(prepared,monkeypatch,mutation):
    a,_,_=prepared;calls=[]
    monkeypatch.setattr(module.evaluate,'generate',lambda a:calls.append(a.role) or {'complete':True,'unattempted_ids':[]})
    def bad(args):
        summary=trained_output(args.output)
        receipt=json.loads((args.output/'admitted.json').read_text())
        if mutation=='receipt':receipt['complete']=False
        elif mutation=='summary_hash':receipt['summary_sha256']='wrong'
        elif mutation=='process_hash':receipt['process_sha256']='wrong'
        elif mutation=='cleanup':
            process=json.loads((args.output/'process.json').read_text());process['cleanup_complete']=False
            module.dump(args.output/'process.json',process)
            receipt['process_sha256']=module.file_sha(args.output/'process.json')
        else:summary=dict(summary,actual_updates=79)
        module.dump(args.output/'admitted.json',receipt)
        return summary
    monkeypatch.setattr(module.train,'supervise',bad)
    with pytest.raises(ValueError,match='receipt/checkpoint'):module.execute(a)
    assert calls==['parent'] and not (a.output/'training-linkage.json').exists()


def test_incomplete_child_raises(prepared,monkeypatch):
    a,_,_=prepared
    monkeypatch.setattr(module.train,'supervise',lambda a:trained_output(a.output))
    monkeypatch.setattr(module.evaluate,'generate',lambda a:dict(complete=a.role=='parent',unattempted_ids=[]))
    with pytest.raises(ValueError,match='Complete child'):module.execute(a)
    assert not json.loads((a.output/'summary.json').read_text())['complete']


def test_zero_exit_without_complete_summary_is_not_success(prepared,monkeypatch):
    a,_,_=prepared
    a.output=a.output.parent/'outer'
    monkeypatch.setattr(module,'run_owned',lambda *args:dict(returncode=0,output='',seconds=1,
        execution_complete=True,cleanup_complete=True,output_complete=True,timed_out=False))
    with pytest.raises(RuntimeError,match='Cycle incomplete'):module.supervise(a)
    summary=json.loads((a.output/'summary.json').read_text())
    assert len(summary['unattempted_task_ids']['parent'])==40
    assert len(summary['unattempted_task_ids']['child'])==40
