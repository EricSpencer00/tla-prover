import copy
from contextlib import nullcontext
import json
from pathlib import Path
from types import SimpleNamespace
import sys
import os
import shutil
import subprocess

import pytest
from tools import proof_sumsequence_proof_rl_eval as e
from harness.test_proof_sumsequence_repair_eval import frozen_inputs

REAL_ADMIT=e.admit


def test_isolated_stage_import_from_exact_sources_only(tmp_path):
    for relative in e.SOURCES:
        destination=tmp_path/relative;destination.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(e.ROOT/relative,destination)
    script=('import sys,pathlib; root=pathlib.Path('+repr(str(tmp_path))+'); sys.path.insert(0,str(root)); '
            'from tools import proof_sumsequence_proof_rl_eval; '
            'files=[pathlib.Path(m.__file__).resolve() for n,m in sys.modules.items() '
            'if (n=="tools" or n.startswith("tools.") or n=="harness" or n.startswith("harness.")) '
            'and getattr(m,"__file__",None)]; '
            'assert files and all(p.is_relative_to(root) for p in files); print(len(files))')
    environment=dict(os.environ);environment.pop('PYTHONPATH',None)
    result=subprocess.run([sys.executable,'-I','-c',script],cwd=tmp_path,env=environment,
        capture_output=True,text=True,timeout=30)
    assert result.returncode==0,result.stderr
    assert int(result.stdout.strip())>10


@pytest.fixture
def portable():
    return e.load(e.ROOT/'results/runs/proof-sumsequence-repair-packet-20260906-main-v2/prompts.json')


@pytest.fixture
def runtime(tmp_path,portable,monkeypatch):
    a=SimpleNamespace(**{k:tmp_path/k for k in e.INPUTS},output=tmp_path/'output',
        admission=tmp_path/'frozen.json',evaluation='greedy40',arm='child',worker_seconds=900.,
        baseline_remote_root='/canonical/old',baseline_remote_parent='/canonical/f41')
    e.dump(a.prompts,portable)
    # The original packet has canonical historical formatting, copied byte for byte.
    a.prompts.write_bytes((e.ROOT/'results/runs/proof-sumsequence-repair-packet-20260906-main-v2/prompts.json').read_bytes())
    config=dict(evaluation=e.packet(a,'a'*64),encodings=frozen_inputs(portable),checkpoint_sha256='a'*64,
        checkpoint_config_sha256='config',model_files={},historical_baseline={'original_role':'child'})
    e.dump(a.admission,config)
    monkeypatch.setattr(e,'admit',lambda args:copy.deepcopy(config))
    return a,config


def rows(config):return [dict(r,**e.greedy.output_fields([128009],'')) for r in config['encodings']]


def process(command,cwd):
    return dict(command=command,cwd=str(cwd),returncode=0,output='',seconds=1.,timed_out=False,
        execution_complete=True,cleanup_complete=True,output_complete=True,root_reaped=True,surviving_owned_processes=[])


def success_files(a,config):
    output=rows(config);e.persist(a.output,output)
    (a.output/'events.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in output))
    value=dict(complete=True,**e.accounting(output),memory=dict(allocated=1,reserved=2),
        weights_unchanged=True,restore_exact=True,full_admission_stable=True,optimizer_updates=0,
        checkpoint_sha256=config['checkpoint_sha256'],elapsed_seconds=1.,
        accounting_sha256=e.file_sha(a.output/'accounting.json'),verification_pending=True)
    e.dump(a.output/'memory.json',value['memory'])
    phases=['after_model_load','after_checkpoint_restore']+['after_sample_'+str(i) for i in range(40)]+['after_final_admission']
    e.dump(a.output/'memory_events.json',[dict(phase=phase,**value['memory']) for phase in phases])
    e.dump(a.output/'worker_summary.json',value);return value


def test_exact40_and_fresh32_contracts(runtime,portable):
    a,c=runtime
    assert c['evaluation']['tasks']==e.greedy.validate_export(portable)
    assert c['evaluation']['counts']==dict(original_train=32,original_development=4,new_train=4)
    assert e.GREEDY_BUDGET==e.greedy.BUDGET
    a.evaluation='stochastic32';a.arm='parent';p=e.packet(a,'a'*64)
    assert p['policy_sha256']==e.PARENT_SHA and len(p['requests'])==32 and len(p['tasks'])==8
    assert p['budget']['seed']==20261003 and e.stochastic.BUDGET['seed']==20261002
    assert p['selection_indices']==[0,1,2,6,13,14,16,29]
    assert all(r['policy_sha256']==e.PARENT_SHA for r in p['requests'])
    assert p['training_authorized'] is False


def test_packet_drift_rejected(runtime):
    a,c=runtime;a.prompts.write_bytes(a.prompts.read_bytes()+b' ')
    with pytest.raises(ValueError):e.packet(a,'a'*64)


def test_caps_unknown_exact_output_and_order(runtime):
    a,c=runtime;r=rows(c)
    r[0].update(e.greedy.output_fields([7]*3072,''));r[1].update(e.greedy.output_fields([128009],'',late=True))
    e.validate_rows(c,r)
    assert e.accounting(r)['unknown_tasks']==2 and e.accounting(r)['generated_rows']==40
    r[2]['token_ids']=[3]
    with pytest.raises(ValueError):e.validate_rows(c,r)
    r=rows(c);r[0],r[1]=r[1],r[0]
    with pytest.raises(ValueError):e.validate_rows(c,r)


def test_decode_must_match(runtime,monkeypatch):
    a,c=runtime;monkeypatch.setattr(e.common,'decode_reply',lambda *args:'different')
    with pytest.raises(ValueError,match='decoder'):e.validate_rows(c,rows(c),object())


def test_generate_success(runtime,monkeypatch):
    a,c=runtime
    def run(command,cwd,seconds):
        assert 30<seconds<1000 and command[2]=='worker'
        success_files(a,c);return process(command,cwd)
    monkeypatch.setattr(e,'run_owned',run)
    result=e.generate(a)
    assert result['complete'] and result['accounted_tasks']==40 and result['unknown_tasks']==0
    assert result['historical_baseline']['original_role']=='child'


@pytest.mark.parametrize('defect',['cleanup','truncated','interior','missing','weights','checkpoint','counts','optimizer','memory','late','events'])
def test_generate_raw_failure_preserves40(runtime,monkeypatch,defect):
    a,c=runtime
    def run(command,cwd,seconds):
        s=success_files(a,c);p=process(command,cwd)
        if defect=='cleanup':p['cleanup_complete']=False
        elif defect=='truncated':(a.output/'accounting.json').write_text('[')
        elif defect=='interior':e.dump(a.output/'accounting.json',[{},*rows(c)[1:]])
        elif defect=='missing':e.dump(a.output/'accounting.json',rows(c)[:1])
        elif defect=='weights':s['weights_unchanged']=False
        elif defect=='checkpoint':s['checkpoint_sha256']='wrong'
        elif defect=='counts':s['eos_complete']=39
        elif defect=='optimizer':s['optimizer_updates']=1
        elif defect=='memory':s['memory']['reserved']=40*1024**3
        elif defect=='late':s['elapsed_seconds']=1001
        else:(a.output/'events.jsonl').write_text('{}\n')
        e.dump(a.output/'worker_summary.json',s);return p
    monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises((ValueError,KeyError,RuntimeError)):e.generate(a)
    summary=e.load(a.output/'summary.json')
    assert not summary['complete'] and summary['accounted_tasks']==40 and summary['unknown_tasks']==40
    assert summary['accounting_unverified'] and len(summary['requested_ids'])==40


def test_full_admission_failure_before_worker(runtime,monkeypatch):
    a,c=runtime
    monkeypatch.setattr(e,'admit',lambda args:dict(c,drift=True))
    monkeypatch.setattr(e,'run_owned',lambda *args:pytest.fail('worker must not launch'))
    with pytest.raises(ValueError):e.generate(a)
    assert e.load(a.output/'summary.json')['unknown_tasks']==40


def test_corrupt_prompt_still_preserves40(runtime):
    a,c=runtime;a.prompts.write_bytes(b'corrupt')
    with pytest.raises(ValueError):e.generate(a)
    s=e.load(a.output/'summary.json')
    assert s['unknown_tasks']==40 and len(s['requested_ids'])==40


def test_post_admission_failure_invalidates(runtime,monkeypatch):
    a,c=runtime;calls=[]
    def admission(args):
        calls.append(1);return c if len(calls)==1 else dict(c,drift=True)
    def run(command,cwd,seconds):success_files(a,c);return process(command,cwd)
    monkeypatch.setattr(e,'admit',admission);monkeypatch.setattr(e,'run_owned',run)
    with pytest.raises(ValueError):e.generate(a)
    assert e.load(a.output/'summary.json')['unknown_tasks']==40


@pytest.mark.parametrize('field,value',[('evaluation','stochastic32'),('arm','parent')])
def test_unimplemented_sampling_and_parent_not_launched(runtime,monkeypatch,field,value):
    a,c=runtime;setattr(a,field,value)
    monkeypatch.setattr(e,'run_owned',lambda *args:pytest.fail('no worker'))
    with pytest.raises(ValueError):e.generate(a)
    assert not a.output.exists()


def test_baseline_keeps_original_child_provenance(runtime,monkeypatch):
    a,c=runtime;seen=[]
    def validate(args,role,expected,tasks,tokenizer):
        assert args.remote_model==str(a.model_path.resolve())
        seen.append((role,expected));return dict(rows=rows(c))
    monkeypatch.setattr(e.historical,'validate_arm',validate)
    value=e.baseline(a,object(),c['evaluation']['tasks'])
    assert seen==[('child',e.PARENT_SHA)] and value['current_sany_and_strict_replay_required']


def test_real_historical40_baseline_production_reconstruction():
    from transformers import AutoTokenizer
    local=e.ROOT/'results/runs/proof-cuda-tokenizer-20260905-v2'
    root='/lus/grand/projects/EVITA/eric-spencer/'
    a=SimpleNamespace(
        baseline_cycle=e.ROOT/'results/runs/proof-sumsequence-repair-cycle-20260906-v1',
        prompts=e.ROOT/'results/runs/proof-sumsequence-repair-packet-20260906-main-v2/prompts.json',
        model_path=Path(root+'hf-cache/hub/models--meta-llama--Llama-3.1-8B-Instruct/snapshots/0e9e39f249a16976918f6564b8830bc894c89659'),
        baseline_remote_root=root+'prove-tla-sumsequence-repair-20260906-v1',
        baseline_remote_parent=root+'prove-tla-token-rl-20260906-v3/results/cycle/training/policy_optimizer.pt')
    tokenizer=AutoTokenizer.from_pretrained(local,local_files_only=True)
    tasks=e.greedy.validate_export(e.load(a.prompts))
    result=e.baseline(a,tokenizer,tasks,tokenizer_path=local)
    assert result['policy_sha256']==e.PARENT_SHA and result['original_role']=='child'
    raw=[json.loads(r) for r in (a.baseline_cycle/'child/generations.jsonl').read_bytes().splitlines()]
    assert len(raw)==40 and result['rows_sha256']==e.digest(raw)
    assert sum(r['finish_reason']=='eos' for r in raw)==39
    assert result['proof_scores_reused'] is False


@pytest.mark.parametrize('drift',[None,'restore','weights','encoding'])
def test_worker_actual_execution_with_mocked_model(runtime,monkeypatch,drift):
    import torch
    a,c=runtime;a.output.mkdir()
    selected={'weight':torch.nn.Parameter(torch.tensor([2. if drift=='restore' else 1.]),requires_grad=False)}
    class Net:
        generation_config=SimpleNamespace(eos_token_id=e.common.EOS_IDS)
        def parameters(self):return selected.values()
        def generate(self,**kwargs):
            assert not kwargs['do_sample'] and kwargs['max_new_tokens']==3072
            if drift=='weights':selected['weight'].add_(1.)
            return torch.cat((kwargs['input_ids'],torch.tensor([[128009]])),dim=1)
    monkeypatch.setattr(e.train,'load_policy',lambda *args,**kw:Net())
    monkeypatch.setattr(e.train,'restore_policy',lambda *args:selected)
    monkeypatch.setattr(e.stochastic,'checkpoint_state',lambda *args:'config')
    monkeypatch.setattr(torch,'load',lambda *args,**kw:dict(trainable_state={'weight':torch.tensor([1.])}))
    tensor=torch.tensor
    monkeypatch.setattr(torch,'tensor',lambda *args,**kw:tensor(*args,**{k:v for k,v in kw.items() if k!='device'}))
    monkeypatch.setattr(e.train,'autocast',lambda *args:nullcontext())
    for name in ('reset_peak_memory_stats','synchronize'):monkeypatch.setattr(torch.cuda,name,lambda:None)
    monkeypatch.setattr(e,'memory',lambda:dict(allocated=1,reserved=2))
    tokenizer=SimpleNamespace(pad_token_id=0)
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *args,**kw:tokenizer)))
    encoded={r['id']:r for r in c['encodings']}
    if drift=='encoding':encoded={key:dict(value,rendered_prompt='drift') for key,value in encoded.items()}
    monkeypatch.setattr(e.common,'encode_prompt',lambda tokenizer,task:copy.deepcopy(encoded[task['id']]))
    monkeypatch.setattr(e.common,'decode_reply',lambda *args:'')
    if drift:
        with pytest.raises(ValueError):e.worker(a)
        return
    e.worker(a)
    r=e.load(a.output/'accounting.json');summary=e.load(a.output/'worker_summary.json')
    e.validate_worker_summary(c,r,summary,a.output)
    assert summary['complete'] and summary['eos_complete']==40
    assert torch.equal(selected['weight'],tensor([1.]))


def test_training_manifest_requires_all_paths(runtime):
    a,c=runtime;e.dump(a.training_inputs,{'checkpoint':'/made/up'})
    with pytest.raises(ValueError,match='manifest'):e.training_receipt(a)


def test_overlimit_memory_is_persisted_before_guard(tmp_path,monkeypatch):
    values=dict(allocated=1,reserved=40*1024**3)
    monkeypatch.setattr(e,'memory',lambda:values)
    with pytest.raises(ValueError):e.record_memory(tmp_path,'after_model_load')
    assert e.load(tmp_path/'memory.json')==values
    assert e.load(tmp_path/'memory_events.json')==[dict(phase='after_model_load',**values)]


@pytest.fixture
def receipt(runtime,monkeypatch):
    a,c=runtime;a.training_output.mkdir();a.model_path.mkdir()
    paths={k:str((a.training_inputs.parent/k).resolve()) for k in e.training.PATHS}
    e.dump(a.training_inputs,paths);parent=Path(paths['checkpoint']);parent.write_bytes(b'parent')
    e.dump(a.training_output/'admission.json',{'frozen':True})
    child=a.training_output/'policy_optimizer.pt';child.write_bytes(b'actualchild')
    worker=dict(complete=True,checkpoint_sha256=e.file_sha(child),optimizer_updates=1)
    monkeypatch.setattr(e.training,'admit',lambda args:{'frozen':True})
    monkeypatch.setattr(e.training,'validate_output',lambda args,frozen:worker)
    original=e.file_sha
    monkeypatch.setattr(e,'file_sha',lambda path:e.PARENT_SHA if Path(path)==parent else original(path))
    command=[sys.executable,str(e.ROOT/'tools/proof_sumsequence_proof_rl_train.py'),'worker']
    for key in (*e.training.PATHS,'output'):
        command+=['--'+key.replace('_','-'),paths[key] if key!='output' else str(a.training_output)]
    command+=['--admission',str(a.training_output/'admission.json'),'--worker-seconds','899.0']
    e.dump(a.training_output/'process.json',process(command,e.ROOT))
    e.dump(a.training_output/'summary.json',dict(worker,total_seconds=2.,process_sha256=e.file_sha(a.training_output/'process.json')))
    return a,worker


def test_actual_receipt_derives_child_never_accepts_user_hash(receipt):
    a,worker=receipt;r=e.training_receipt(a)
    assert r['child_sha256']==worker['checkpoint_sha256'] and r['parent_sha256']==e.PARENT_SHA
    assert r['optimizer_updates']==1 and 'policy_optimizer.pt' in r['training_artifacts']


@pytest.mark.parametrize('defect',['admission','process','deadline','checkpoint','summary'])
def test_receipt_rejects_drift(receipt,monkeypatch,defect):
    a,w=receipt
    if defect=='admission':monkeypatch.setattr(e.training,'admit',lambda args:{'drift':True})
    elif defect=='process':
        p=e.load(a.training_output/'process.json');p['cleanup_complete']=False;e.dump(a.training_output/'process.json',p)
    elif defect=='checkpoint':w['checkpoint_sha256']='invented'
    else:
        s=e.load(a.training_output/'summary.json')
        if defect=='deadline':s['total_seconds']=901
        else:s['optimizer_updates']=0
        e.dump(a.training_output/'summary.json',s)
    with pytest.raises(ValueError):e.training_receipt(a)


def test_full_admission_selected_checkpoint_and_cpu_policy(runtime,monkeypatch):
    import torch
    a,c=runtime;a.model_path.mkdir();e.dump(a.model_path/'generation_config.json',dict(eos_token_id=e.common.EOS_IDS))
    a.checkpoint.write_bytes(b'actualchild');child=e.file_sha(a.checkpoint)
    receipt=dict(child_sha256=child,parent_sha256=e.PARENT_SHA)
    def training(args):
        assert all(e.os.environ[k]=='4' for k in e.CPU_ENV)
        return receipt
    monkeypatch.setenv('OPENBLAS_NUM_THREADS','64')
    monkeypatch.setattr(e,'training_receipt',training)
    monkeypatch.setattr(e.train,'model_files',lambda path:{})
    monkeypatch.setattr(e.common,'MODEL_FILES_SHA',e.digest({}))
    monkeypatch.setattr(e.common,'runtime_versions',lambda:e.common.FIRST_VERSIONS)
    monkeypatch.setattr(torch,'load',lambda *args,**kw:{})
    monkeypatch.setattr(e.stochastic,'checkpoint_state',lambda *args:'exactconfig')
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *args,**kw:object())))
    encoded={r['id']:r for r in c['encodings']}
    monkeypatch.setattr(e.common,'encode_prompt',lambda tokenizer,task:copy.deepcopy(encoded[task['id']]))
    monkeypatch.setattr(e,'baseline',lambda *args:dict(original_role='child',policy_sha256=e.PARENT_SHA))
    result=REAL_ADMIT(a)
    assert result['checkpoint_sha256']==child and len(result['encodings'])==40
    assert result['training_receipt']==receipt and result['cpu_environment']['OPENBLAS_NUM_THREADS']=='4'
    assert result['source_sha256']==e.source_identity() and result['optimizer_updates']==0
    a.arm='parent'
    with pytest.raises(ValueError,match='selected'):REAL_ADMIT(a)
