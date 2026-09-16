import copy
from contextlib import nullcontext
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
from types import SimpleNamespace

import pytest
from tools import proof_sumsequence_sany_repair_eval as e

REAL_ADMIT=e.admit


@pytest.fixture(scope='module')
def original():
    from transformers import AutoTokenizer
    path=e.ROOT/'results/runs/proof-sumsequence-sany-repair-packet-20260906-v1/packet.json'
    tokenizer=AutoTokenizer.from_pretrained(e.repair.TOKENIZER,local_files_only=True)
    value=e.packet(path)
    return path,value,tokenizer


@pytest.fixture
def runtime(tmp_path,original,monkeypatch):
    path,value,tokenizer=original
    a=SimpleNamespace(**{key:tmp_path/key for key in e.INPUTS},output=tmp_path/'output',
        admission=tmp_path/'admission.json',worker_seconds=1100.)
    a.packet.write_bytes(path.read_bytes());a.checkpoint.write_bytes(b'child')
    frozen=dict(budget=e.BUDGET,checkpoint_sha256=e.POLICY_SHA,checkpoint_config_sha256='config',model_files={},
        model_max_position_embeddings=131072,encodings=[e.encode(tokenizer,r) for r in value['tasks']])
    e.dump(a.admission,frozen);monkeypatch.setattr(e,'admit',lambda args:copy.deepcopy(frozen))
    return a,frozen


def rows(frozen):return [dict(r,**e.base.greedy.output_fields([128009],'')) for r in frozen['encodings']]


def proc(command,cwd):
    return dict(command=command,cwd=str(cwd),returncode=0,output='',seconds=.01,timed_out=False,
        execution_complete=True,cleanup_complete=True,output_complete=True,root_reaped=True,surviving_owned_processes=[])


def artifacts(output,frozen):
    import torch
    output_rows=rows(frozen);e.base.persist(output,output_rows)
    (output/'events.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in output_rows))
    memory=dict(allocated=1,reserved=2);e.dump(output/'memory.json',memory)
    phases=['after_model_load','after_checkpoint_restore','after_sample_0','after_sample_1','after_final_admission']
    e.dump(output/'memory_events.json',[dict(phase=p,**memory) for p in phases])
    rng={}
    for label in ('before','after'):
        path=output/('rng_'+label+'.pt')
        torch.save(dict(seed=e.BUDGET['seed'],cpu=torch.tensor([1],dtype=torch.uint8),cuda=torch.tensor([2],dtype=torch.uint8)),path)
        rng[label]=e.file_sha(path)
    summary=dict(complete=True,**e.accounting(output_rows),checkpoint_sha256=e.POLICY_SHA,weights_unchanged=True,
        restore_exact=True,full_admission_stable=True,elapsed_seconds=.01,pre_admission_seconds=.01,post_admission_reserve_seconds=30.,
        memory=memory,rng_sha256=rng,accounting_sha256=e.file_sha(output/'accounting.json'),optimizer_updates=0,
        verification_pending=True,original_pass_at1_unchanged=True,gate_claim=False)
    e.dump(output/'worker_summary.json',summary);return output_rows,summary


def test_actual_full_context_new_budget_preserves_old_packet(original):
    path,value,tokenizer=original;old=copy.deepcopy(value)
    encodings=[e.encode(tokenizer,row) for row in value['tasks']]
    assert [r['input_tokens'] for r in encodings]==[5290,921]
    assert all(r['status']=='ready' for r in encodings)
    assert [r['input_tokens']+3072 for r in encodings]==[8362,3993]
    assert value==old and value['tasks'][0]['encoding']['status']=='context_overflow'
    assert value['budget']['max_context']==8192 and e.BUDGET['max_context']==9216
    assert e.BUDGET['memory_bytes']==36*1024**3 and e.BUDGET['original_denominator']==40


def test_exact_packet_pin_and_no_shortening(original,tmp_path):
    path,value,tokenizer=original;changed=tmp_path/'packet.json';changed.write_bytes(path.read_bytes()+b' ')
    with pytest.raises(ValueError):e.packet(changed)
    row=copy.deepcopy(value['tasks'][0]);row['prompt']='shortened'
    with pytest.raises(ValueError):e.encode(tokenizer,row)


def test_full_admission_actual_binding(runtime,original,monkeypatch):
    import torch
    a,f=runtime;path,value,tokenizer=original;a.model_path.mkdir()
    e.dump(a.model_path/'config.json',dict(max_position_embeddings=131072))
    e.dump(a.model_path/'generation_config.json',dict(eos_token_id=e.common.EOS_IDS))
    monkeypatch.setenv('OPENBLAS_NUM_THREADS','64')
    def receipt(args):
        assert all(os.environ[k]=='4' for k in e.base.CPU_ENV)
        return dict(child_sha256=e.POLICY_SHA,parent_sha256=e.base.PARENT_SHA,optimizer_updates=1)
    monkeypatch.setattr(e.base,'training_receipt',receipt)
    original_sha=e.file_sha;monkeypatch.setattr(e,'file_sha',lambda p:e.POLICY_SHA if Path(p)==a.checkpoint else original_sha(p))
    monkeypatch.setattr(e.train,'model_files',lambda p:{})
    monkeypatch.setattr(e.common,'MODEL_FILES_SHA',e.digest({}))
    monkeypatch.setattr(e.common,'runtime_versions',lambda:e.common.FIRST_VERSIONS)
    monkeypatch.setattr(torch,'load',lambda *args,**kw:{})
    monkeypatch.setattr(e.base.stochastic,'checkpoint_state',lambda *args:'config')
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *args,**kw:tokenizer)))
    admitted=REAL_ADMIT(a)
    assert admitted['checkpoint_sha256']==e.POLICY_SHA and admitted['original_denominator']==40
    assert admitted['original_packet_executable_tasks']==1 and len(admitted['encodings'])==2
    assert admitted['original_packet_budget']['max_context']==8192 and admitted['budget']['max_context']==9216
    assert all(r['status']=='ready' for r in admitted['encodings'])
    e.dump(a.model_path/'config.json',dict(max_position_embeddings=8192))
    with pytest.raises(ValueError,match='model must support'):REAL_ADMIT(a)


def test_cap_is_not_failure_or_completion(runtime):
    a,f=runtime;output=rows(f);output[0].update(e.base.greedy.output_fields([7]*3072,''))
    output[1].update(e.base.greedy.output_fields([128009],'',late=True))
    e.validate_rows(f,output)
    assert e.accounting(output)['unknown_generations']==2 and e.accounting(output)['generated_rows']==2


@pytest.mark.parametrize('defect',['count','order','tokens','decoded','context'])
def test_raw_validator_fails_closed(runtime,monkeypatch,defect):
    a,f=runtime;r=rows(f);tokenizer=None
    if defect=='count':r.pop()
    elif defect=='order':r.reverse()
    elif defect=='tokens':r[0]['token_ids']=[7]
    elif defect=='decoded':
        tokenizer=object();monkeypatch.setattr(e.common,'decode_reply',lambda *args:'bad')
    else:r[0]['input_token_ids']=[9]
    with pytest.raises(ValueError):e.validate_rows(f,r,tokenizer)


def test_owned_supervisor_success(runtime,monkeypatch):
    a,f=runtime
    def run(command,cwd,seconds):
        assert 30<seconds<1200 and command[2]=='worker'
        artifacts(a.output,f);return proc(command,cwd)
    monkeypatch.setattr(e,'run_owned',run)
    summary=e.generate(a)
    assert summary['complete'] and summary['requested_tasks']==2 and summary['original_denominator']==40
    assert summary['original_pass_at1_unchanged'] and not summary['gate_claim']


@pytest.mark.parametrize('defect',['cleanup','malformed','partial','count','rng','memory','weights','events','checkpoint','budget'])
def test_execution_errors_preserve_both_diagnostic_keys(runtime,monkeypatch,defect):
    a,f=runtime
    def run(command,cwd,seconds):
        r,w=artifacts(a.output,f);p=proc(command,cwd)
        if defect=='cleanup':p['cleanup_complete']=False
        elif defect=='malformed':(a.output/'accounting.json').write_text('[')
        elif defect=='partial':e.dump(a.output/'accounting.json',r[:1])
        elif defect=='count':w['eos_complete']=0
        elif defect=='rng':(a.output/'rng_before.pt').write_bytes(b'bad')
        elif defect=='memory':w['memory']['reserved']=40*1024**3
        elif defect=='weights':w['weights_unchanged']=False
        elif defect=='events':(a.output/'events.jsonl').write_text('{}\n')
        elif defect=='checkpoint':w['checkpoint_sha256']='bad'
        else:w['elapsed_seconds']=1201
        e.dump(a.output/'worker_summary.json',w);return p
    monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises((ValueError,KeyError)):e.generate(a)
    summary=e.load(a.output/'summary.json')
    assert not summary['complete'] and summary['accounted_tasks']==2 and summary['original_denominator']==40
    assert summary['unknown_generations']==2 and summary['requested_ids']==list(e.IDS)


def test_full_admission_rejected_before_worker(runtime,monkeypatch):
    a,f=runtime;monkeypatch.setattr(e,'admit',lambda a:dict(f,drift=True))
    monkeypatch.setattr(e,'run_owned',lambda *args:pytest.fail('must not launch'))
    with pytest.raises(ValueError):e.generate(a)
    assert e.load(a.output/'summary.json')['original_denominator']==40


@pytest.mark.parametrize('field',['elapsed_seconds','pre_admission_seconds','post_admission_reserve_seconds'])
@pytest.mark.parametrize('value',[float('nan'),float('inf')])
def test_nonfinite_admission_and_worker_times_rejected(runtime,field,value):
    a,f=runtime;a.output.mkdir();r,w=artifacts(a.output,f);w[field]=value
    with pytest.raises(ValueError):e.validate_worker(f,r,w,a.output)


def test_actual_full_post_admission_drift(runtime,monkeypatch):
    a,f=runtime;calls=[]
    def admit(args):calls.append(1);return f if len(calls)==1 else dict(f,drift=True)
    def run(command,cwd,seconds):artifacts(a.output,f);return proc(command,cwd)
    monkeypatch.setattr(e,'admit',admit);monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises(ValueError):e.generate(a)


@pytest.mark.parametrize('drift',[None,'restore','weights','memory'])
def test_actual_worker_control_flow_with_mocked_model(runtime,original,monkeypatch,drift):
    import torch
    a,f=runtime;a.output.mkdir();path,value,tokenizer=original
    selected={'weight':torch.nn.Parameter(torch.tensor([2. if drift=='restore' else 1.]),requires_grad=False)}
    class Net:
        config=SimpleNamespace(max_position_embeddings=131072)
        generation_config=SimpleNamespace(eos_token_id=e.common.EOS_IDS)
        def parameters(self):return selected.values()
        def generate(self,**kw):
            assert kw['input_ids'].shape[1] in (5290,921) and kw['max_new_tokens']==3072 and not kw['do_sample']
            if drift=='weights':selected['weight'].add_(1.)
            return torch.cat((kw['input_ids'],torch.tensor([[128009]])),dim=1)
    monkeypatch.setattr(e.train,'load_policy',lambda *args,**kw:Net())
    monkeypatch.setattr(e.train,'restore_policy',lambda *args:selected)
    monkeypatch.setattr(e.base.stochastic,'checkpoint_state',lambda *args:'config')
    original_load=torch.load
    monkeypatch.setattr(torch,'load',lambda p,**kw:dict(trainable_state={'weight':torch.tensor([1.])}) if Path(p)==a.checkpoint else original_load(p,**kw))
    tensor=torch.tensor;monkeypatch.setattr(torch,'tensor',lambda *args,**kw:tensor(*args,**{k:v for k,v in kw.items() if k!='device'}))
    monkeypatch.setattr(e.train,'autocast',lambda *args:nullcontext())
    for name in ('manual_seed','reset_peak_memory_stats','synchronize'):monkeypatch.setattr(torch.cuda,name,lambda *args:None)
    monkeypatch.setattr(torch.cuda,'get_rng_state',lambda:torch.tensor([1,2],dtype=torch.uint8))
    peaks=[]
    def memory():peaks.append(1);return dict(allocated=1,reserved=40*1024**3 if drift=='memory' and len(peaks)>2 else 2)
    monkeypatch.setattr(e.base,'memory',memory)
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *args,**kw:tokenizer)))
    monkeypatch.setattr(e.common,'decode_reply',lambda *args:'')
    if drift:
        with pytest.raises(ValueError):e.worker(a)
        if drift=='memory':
            assert e.load(a.output/'memory.json')['reserved']==40*1024**3
            assert e.load(a.output/'accounting.json')[0]['status']=='generated'
        return
    e.worker(a);r=e.load(a.output/'accounting.json');w=e.load(a.output/'worker_summary.json')
    e.validate_worker(f,r,w,a.output)
    assert w['complete'] and w['eos_complete']==2 and torch.equal(selected['weight'],tensor([1.]))


def test_exact_archive_isolated_import_and_pbs(tmp_path):
    for relative in e.SOURCES:
        dest=tmp_path/relative;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(e.ROOT/relative,dest)
    script='import sys; sys.path.insert(0,'+repr(str(tmp_path))+'); from tools import proof_sumsequence_sany_repair_eval; print("ok")'
    env=dict(os.environ);env.pop('PYTHONPATH',None)
    result=subprocess.run([sys.executable,'-I','-c',script],cwd=tmp_path,env=env,capture_output=True,text=True,timeout=30)
    assert result.returncode==0,result.stderr
    assert result.stdout.strip()=='ok'
    result=subprocess.run(['bash','-n',str(tmp_path/'tools/proof_sumsequence_sany_repair_eval.pbs')],capture_output=True,text=True)
    assert result.returncode==0,result.stderr
