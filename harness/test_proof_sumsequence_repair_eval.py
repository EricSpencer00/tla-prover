import copy
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
from tools import proof_sumsequence_repair_eval as e


@pytest.fixture
def packet():
    original=(e.ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json').read_bytes()
    new=json.dumps(e.extra._packet(e.extra._static_manifest())).encode()
    return e.compose(original,new)


def test_portable_exact40_composition(packet):
    tasks=e.validate_export(packet)
    assert len(tasks)==40 and tasks[:36]==e.broader.validate_export(json.loads(packet['original_packet_bytes']))
    assert tasks[36:]==e.extra.validate_export(json.loads(packet['new_packet_bytes']))
    assert sum(t['split']=='development' for t in tasks)==4
    assert e.sha(packet['original_packet_bytes'].encode())==packet['original_sha256']
    assert not packet['reference_answers_exported']


@pytest.mark.parametrize('mutation',['order','count','prompt','reference','newpacket','byteshash'])
def test_portable_packet_tamper(packet,mutation):
    if mutation=='order':packet['tasks'][0],packet['tasks'][-1]=packet['tasks'][-1],packet['tasks'][0]
    elif mutation=='count':packet['tasks'].pop()
    elif mutation=='prompt':packet['tasks'][0]['prompt']+=' altered'
    elif mutation=='reference':packet['reference_answers_exported']=True
    elif mutation=='newpacket':packet['new_packet_bytes']='{}'
    else:packet['original_sha256']='a'*64
    with pytest.raises((ValueError,KeyError)):e.validate_export(packet)


@pytest.mark.parametrize('role,value',[('parent','a'*64),('child',e.PARENT_SHA),('other','a'*64),('child','')])
def test_checkpoint_roles_do_not_certify_arbitrary_child(role,value):
    with pytest.raises(ValueError):e.checkpoint_role(role,value)


def frozen_inputs(packet):
    return [dict(id=t['id'],split=t['split'],prompt_sha256=t['prompt_sha256'],
        input_tokens=2,input_token_ids=[1,2],input_token_ids_sha256=e.digest([1,2]),
        rendered_prompt='prompt',rendered_prompt_sha256=e.sha(b'prompt'),status='ready') for t in packet['tasks']]


def admission(packet):
    return dict(budget=e.BUDGET,input_evidence=frozen_inputs(packet),role='parent',checkpoint_sha256=e.PARENT_SHA)


def rows(config):
    return [dict(r,**e.output_fields([128009],'')) for r in config['input_evidence']]


def test_exact40_completion_and_caps(packet):
    config=admission(packet);output=rows(config)
    e.validate_rows(config,output,complete=True)
    output[0].update(e.output_fields([7]*3072,''));output[1].update(e.output_fields([128009],'',late=True))
    e.validate_rows(config,output,complete=True)
    assert output[0]['finish_reason']=='token_limit'
    assert output[1]['finish_reason']=='time_limit' and output[1]['eos_reached']
    with pytest.raises(ValueError):e.validate_rows(config,output[:39],complete=True)


def test_raw_token_and_input_binding(packet):
    config=admission(packet);output=rows(config);output[0]['raw_reply']='changed'
    with pytest.raises(ValueError):e.validate_rows(config,output)
    output=rows(config);output[0]['input_token_ids']=[8]
    with pytest.raises(ValueError):e.validate_rows(config,output)


@pytest.mark.parametrize('a,r',[(0,e.BUDGET['memory_bytes']+1),(-1,1),(1,float('nan')),(None,1)])
def test_memory_bounds(a,r):
    with pytest.raises(ValueError):e.memory_guard(a,r)


@pytest.fixture
def runtime(packet,tmp_path,monkeypatch):
    config=admission(packet)
    args=SimpleNamespace(prompts=tmp_path/'prompts',model_path=tmp_path/'model',checkpoint=tmp_path/'checkpoint',
        admission=tmp_path/'admission',output=tmp_path/'output',role='parent',
        expected_input_sha256='a'*64,expected_checkpoint_sha256=e.PARENT_SHA)
    e.dump(args.admission,config)
    monkeypatch.setattr(e,'admit',lambda a:copy.deepcopy(config))
    return args,config


def fake_process(command,cwd):
    return dict(command=command,cwd=str(cwd),returncode=0,output='',seconds=1,
        execution_complete=True,cleanup_complete=True,output_complete=True,timed_out=False)


def test_owned_generation40_success(runtime,monkeypatch):
    args,config=runtime
    def run(command,cwd,timeout):
        assert 0<timeout<1000
        (args.output/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows(config)))
        e.dump(args.output/'runtime.json',dict(allocated=1,reserved=1,weights_unchanged=True,restore_exact=True))
        return fake_process(command,cwd)
    monkeypatch.setattr(e,'run_owned',run)
    result=e.generate(args)
    assert result['complete'] and result['accounted_tasks']==40 and result['eos_complete']==40
    assert result['training_linkage_verified'] is False


def test_owned_incomplete_keeps_remaining_denominator(runtime,monkeypatch):
    args,config=runtime
    def run(command,cwd,timeout):
        (args.output/'generations.jsonl').write_text(json.dumps(rows(config)[0])+'\n')
        result=fake_process(command,cwd);result['cleanup_complete']=False;return result
    monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises(RuntimeError,match='Incomplete'):e.generate(args)
    result=json.loads((args.output/'summary.json').read_text())
    assert result['accounted_tasks']==40 and len(result['unattempted_ids'])==39
    assert not result['complete']
    assert len(json.loads((args.output/'accounting.json').read_text()))==40


def test_full_admission_mismatch_prevents_owned_worker(runtime,monkeypatch):
    args,config=runtime;config['changed']=True
    monkeypatch.setattr(e,'run_owned',lambda *a:pytest.fail('worker started'))
    with pytest.raises(ValueError,match='pre-worker'):e.generate(args)
    assert not args.output.exists()


def test_post_admission_drift_prevents_completion(runtime,monkeypatch):
    args,config=runtime;calls=[]
    def admit(a):
        calls.append(1);return copy.deepcopy(config) if len(calls)==1 else dict(config,changed=True)
    def run(command,cwd,timeout):
        (args.output/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows(config)))
        e.dump(args.output/'runtime.json',dict(allocated=1,reserved=1,weights_unchanged=True,restore_exact=True))
        return fake_process(command,cwd)
    monkeypatch.setattr(e,'admit',admit);monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises(RuntimeError):e.generate(args)
    assert json.loads((args.output/'summary.json').read_text())['full_admission_stable'] is False


@pytest.mark.parametrize('text',['{broken','{}\n','{}\n{truncated'])
def test_malformed_ledger_preserves_all40unknown(runtime,monkeypatch,text):
    args,config=runtime
    def run(command,cwd,timeout):
        initial=json.loads((args.output/'summary.json').read_text())
        assert initial['unknown_tasks']==initial['accounted_tasks']==40
        (args.output/'generations.jsonl').write_text(text)
        return fake_process(command,cwd)
    monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises((ValueError,KeyError)):e.generate(args)
    assert (args.output/'generations.jsonl').read_text()==text
    summary=json.loads((args.output/'summary.json').read_text())
    assert summary['unknown_tasks']==summary['accounted_tasks']==40 and not summary['complete']
    assert len(json.loads((args.output/'accounting.json').read_text()))==40


def test_preexisting_output_never_overwritten(runtime):
    args,config=runtime;args.output.mkdir();(args.output/'summary.json').write_text('user evidence')
    with pytest.raises(FileExistsError):e.generate(args)
    assert (args.output/'summary.json').read_text()=='user evidence'


def test_post_admission_exception_all40unknown(runtime,monkeypatch):
    args,config=runtime;calls=[]
    def admit(a):
        calls.append(1)
        if len(calls)>1:raise ValueError('source changed')
        return copy.deepcopy(config)
    def run(command,cwd,timeout):
        (args.output/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows(config)))
        return fake_process(command,cwd)
    monkeypatch.setattr(e,'admit',admit);monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises(ValueError):e.generate(args)
    summary=json.loads((args.output/'summary.json').read_text())
    assert summary['unknown_tasks']==40 and summary['complete'] is False
