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
from tools import proof_sumsequence_proof_rl_stochastic as s
from harness.test_proof_token_rl_packet import row as rollout


@pytest.fixture
def pair(tmp_path,monkeypatch):
    a=SimpleNamespace(**{k:tmp_path/k for k in s.evaluation.INPUTS},output=tmp_path/'output',
        admission=tmp_path/'freeze.json',baseline_remote_root='/old',baseline_remote_parent='/f41',worker_seconds=3420.)
    a.prompts.write_bytes((s.ROOT/'results/runs/proof-sumsequence-repair-packet-20260906-main-v2/prompts.json').read_bytes())
    a.checkpoint.write_bytes(b'child');child=s.file_sha(a.checkpoint)
    parent=tmp_path/'parent.pt';parent.write_bytes(b'parent')
    manifest={key:str(tmp_path/key) for key in s.evaluation.training.PATHS};manifest['checkpoint']=str(parent)
    s.dump(a.training_inputs,manifest)
    original=s.file_sha
    monkeypatch.setattr(s,'file_sha',lambda path:s.evaluation.PARENT_SHA if Path(path)==parent else original(path))
    admissions={}
    for arm in s.ARMS:
        args=s.arm_args(a,arm);packet=s.evaluation.packet(args,child)
        encodings=[dict(id=t['id'],split=t['split'],prompt_sha256=t['prompt_sha256'],input_tokens=2,
            input_token_ids=[1,2],input_token_ids_sha256=s.digest([1,2]),rendered_prompt='prompt',
            rendered_prompt_sha256=s.sha(b'prompt'),status='ready') for t in packet['tasks']]
        admissions[arm]=dict(evaluation=packet,checkpoint_sha256=packet['policy_sha256'],checkpoint_config_sha256='config',
            encodings=encodings,model_files={},model_files_sha256=s.digest({}),versions={},profile={},eos_token_ids=s.common.EOS_IDS,
            source_sha256=s.evaluation.source_identity(),cpu_environment=s.evaluation.CPU_ENV,
            training_receipt=dict(child_sha256=child,parent_sha256=s.evaluation.PARENT_SHA))
    monkeypatch.setattr(s.evaluation,'admit',lambda args:copy.deepcopy(admissions[args.arm]))
    frozen=s.admit(a);s.dump(a.admission,frozen)
    return a,frozen


def proc(command,cwd):
    return dict(command=command,cwd=str(cwd),returncode=0,output='',seconds=1.,timed_out=False,
        execution_complete=True,cleanup_complete=True,output_complete=True,root_reaped=True,surviving_owned_processes=[])


def artifacts(output,admission):
    import torch
    rows=[rollout(r) for r in admission['evaluation']['requests']];s.old.persist_rows(output,rows)
    (output/'events.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    hashes={}
    for label in ('before','after'):
        path=output/('sampling_generator_'+label+'.pt');torch.save(torch.tensor([1,2],dtype=torch.uint8),path);hashes[label]=s.file_sha(path)
    phases=['after_model_load','after_checkpoint_restore']+['after_sample_'+str(i) for i in range(32)]+['after_final_admission']
    s.dump(output/'memory_events.json',[dict(phase=p,allocated=1,reserved=2) for p in phases])
    s.dump(output/'memory.json',dict(allocated=1,reserved=2))
    summary=dict(phase_complete=True,**s.old.accounting(rows),failure=None,identity_stable=True,optimizer_updates=0,
        frozen_weights_verified=True,checkpoint_restored_exactly=True,checkpoint_sha256=admission['checkpoint_sha256'],
        elapsed_seconds=1.,pre_admission_seconds=.1,post_admission_reserve_seconds=30.,memory=dict(allocated=1,reserved=2),
        sampling_generator_sha256=hashes,rollouts_sha256=s.file_sha(output/'rollouts.jsonl'),verification_pending=True,
        generalization_claim=False,seed=s.SEED,stochastic_sources_sha256=s.digest(s.sources()),
        pair_admission_sha256=s.file_sha(output.parent/'admission.json'))
    s.dump(output/'worker_summary.json',summary);return rows,summary


def test_exact_new_seed_parent_child_contract(pair):
    a,frozen=pair;s.validate_pair(a,frozen)
    assert frozen['requested_samples']==64 and s.BUDGET['seed']==20261003 and s.old.BUDGET['seed']==20261002
    for arm in s.ARMS:
        p=frozen['arms'][arm]['evaluation'];assert len(p['requests'])==32 and p['selection_indices']==[0,1,2,6,13,14,16,29]
        assert all(r['policy_sha256']==p['policy_sha256'] for r in p['requests'])
    assert frozen['arms']['parent']['checkpoint_sha256']==s.evaluation.PARENT_SHA
    assert frozen['arms']['child']['checkpoint_sha256']==s.file_sha(a.checkpoint)


@pytest.mark.parametrize('defect',['seed','policy','encodings','order','source','checkpoint'])
def test_pair_admission_drift(pair,defect):
    a,f=pair
    if defect=='seed':f['arms']['child']['evaluation']['budget']['seed']=20261002
    elif defect=='policy':f['arms']['parent']['evaluation']['policy_sha256']='bad'
    elif defect=='encodings':f['arms']['parent']['encodings'][0]['input_token_ids']=[3]
    elif defect=='order':f['phase_order'].reverse()
    elif defect=='source':f['sources']['tools/proof_sumsequence_proof_rl_stochastic.py']='bad'
    else:a.checkpoint.write_bytes(b'changed')
    with pytest.raises(ValueError):s.validate_pair(a,f)


def test_caps_unknown_and_exact_decode(pair,monkeypatch):
    a,f=pair;ad=f['arms']['child'];rows=[rollout(r) for r in ad['evaluation']['requests']]
    rows[0]=rollout(ad['evaluation']['requests'][0],tokens=[7]*3072,finish='token_limit')
    rows[1]=rollout(ad['evaluation']['requests'][1],tokens=[7],finish='time_limit')
    s.validate_rows(ad,rows);assert s.old.accounting(rows)['unknown_samples']==2
    monkeypatch.setattr(s.common,'decode_reply',lambda *args:'different')
    with pytest.raises(ValueError):s.validate_rows(ad,rows,object())


@pytest.mark.parametrize('defect',['count','order','input','logps','entropy','request'])
def test_raw_rows_fail_closed(pair,defect):
    a,f=pair;ad=f['arms']['child'];rows=[rollout(r) for r in ad['evaluation']['requests']]
    if defect=='count':rows.pop()
    elif defect=='order':rows[0],rows[1]=rows[1],rows[0]
    elif defect=='input':rows[0]['input_token_ids']=[9]
    elif defect=='logps':rows[0]['selected_token_logprobs']=[1.]
    elif defect=='entropy':rows[0]['token_entropies']=[float('nan')]
    else:rows[0]['request_sha256']='bad'
    with pytest.raises(ValueError):s.validate_rows(ad,rows)


def test_supervised_arm_actual_success(pair,monkeypatch):
    a,f=pair;path=a.output.parent/'child-admission.json';s.dump(path,f['arms']['child']);args=s.arm_args(a,'child',path)
    a.output.mkdir();s.dump(a.output/'admission.json',f)
    def run(command,cwd,seconds):
        assert 30<seconds<1500
        artifacts(args.output,f['arms']['child']);return proc(command,cwd)
    monkeypatch.setattr(s,'run_owned',run)
    result=s.generate_arm(args)
    assert result['generated_samples']==32 and result['phase_complete']
    assert result['supervisor_post_admission_reserve_seconds']>=30


@pytest.mark.parametrize('defect',['cleanup','malformed','partial','events','memory','weights','rng','count','seed'])
def test_arm_failure_keeps_denominator(pair,monkeypatch,defect):
    a,f=pair;path=a.output.parent/'child-admission.json';s.dump(path,f['arms']['child']);args=s.arm_args(a,'child',path)
    a.output.mkdir();s.dump(a.output/'admission.json',f)
    def run(command,cwd,seconds):
        rows,w=artifacts(args.output,f['arms']['child']);p=proc(command,cwd)
        if defect=='cleanup':p['cleanup_complete']=False
        elif defect=='malformed':(args.output/'rollouts.jsonl').write_text('{}')
        elif defect=='partial':s.old.persist_rows(args.output,rows[:1])
        elif defect=='events':(args.output/'events.jsonl').write_text('{}\n')
        elif defect=='memory':s.dump(args.output/'memory.json',dict(allocated=1,reserved=50*1024**3))
        elif defect=='weights':w['frozen_weights_verified']=False
        elif defect=='rng':(args.output/'sampling_generator_before.pt').write_bytes(b'bad')
        elif defect=='count':w['eos_complete_samples']=0
        else:w['seed']=20261002
        s.dump(args.output/'worker_summary.json',w);return p
    monkeypatch.setattr(s,'run_owned',run)
    with pytest.raises((ValueError,KeyError)):s.generate_arm(args)
    summary=s.load(args.output/'summary.json')
    assert summary['requested_samples']==32 and not summary['phase_complete']


def test_admission_rejects_before_cuda(pair,monkeypatch):
    a,f=pair;args=s.arm_args(a,'child',a.admission);args.worker_seconds=1400
    a.output.mkdir();s.dump(a.output/'admission.json',f)
    monkeypatch.setattr(s.train,'load_policy',lambda *a,**kw:pytest.fail('no CUDA load'))
    with pytest.raises(ValueError):s.worker(args) # pair admission is not an arm admission


def test_measured_admission_reserve():
    assert s.reserve(124.183)==pytest.approx(155.22875)
    assert s.reserve(1)==30 and s.ARM_SECONDS==1500 and s.SECONDS==3420


def test_full64_initialized_before_pair_admission(pair,monkeypatch):
    a,f=pair;s.dump(a.admission,dict(bad=True))
    monkeypatch.setattr(s,'run_owned',lambda *args:pytest.fail('must not launch'))
    with pytest.raises(ValueError):s.generate(a)
    state=s.load(a.output/'summary.json')
    assert state['accounted_samples']==64 and not state['complete']
    assert all(len(v)==32 for v in state['unattempted_sample_ids'].values())


def test_execute_stops_without_shortening_second_arm(pair,monkeypatch):
    a,f=pair;a.output.mkdir();times=iter([0.,0.,2000.]);monkeypatch.setattr(s.time,'monotonic',lambda:next(times))
    called=[]
    monkeypatch.setattr(s,'generate_arm',lambda args:called.append(args.arm) or {'done':True})
    monkeypatch.setattr(s,'validate_arm_result',lambda *args:{'done':True})
    with pytest.raises(TimeoutError):s.execute(a)
    assert called==['parent']
    state=s.load(a.output/'summary.json');assert state['unattempted_sample_ids']['parent']==[] and len(state['unattempted_sample_ids']['child'])==32


@pytest.mark.parametrize('defect',[None,'rng','childpartial','sources'])
def test_complete_owned_pair_execution_and_fail_closed(pair,monkeypatch,defect):
    import torch
    a,f=pair;calls=[]
    original_sources=s.sources
    def run(command,cwd,seconds):
        record=proc(command,cwd)
        if command[2]=='_run':
            args=copy.copy(a);args.admission=a.output/'admission.json';args.worker_seconds=seconds
            try:s.execute(args)
            except Exception as exc:record.update(returncode=1,output=str(exc))
            return record
        arm=command[command.index('--arm')+1];calls.append(arm)
        root=Path(command[command.index('--output')+1]);rows,w=artifacts(root,f['arms'][arm])
        if arm=='child':
            if defect=='rng':
                path=root/'sampling_generator_before.pt';torch.save(torch.tensor([8],dtype=torch.uint8),path)
                w['sampling_generator_sha256']['before']=s.file_sha(path);s.dump(root/'worker_summary.json',w)
            elif defect=='childpartial':s.old.persist_rows(root,rows[:1])
            elif defect=='sources':monkeypatch.setattr(s,'sources',lambda:dict(original_sources(),unexpected='changed'))
        return record
    monkeypatch.setattr(s,'run_owned',run)
    if defect:
        with pytest.raises(ValueError):s.generate(a)
        state=s.load(a.output/'summary.json');assert not state['complete'] and state['accounted_samples']==64
    else:
        state=s.generate(a)
        assert state['complete'] and state['phase']=='sampled_pending_verification'
        assert state['unattempted_sample_ids']=={'parent':[],'child':[]}
        assert state['requested_samples']==64 and state['optimizer_updates']==0
    assert calls==['parent','child']


@pytest.mark.parametrize('drift',[None,'weights','restore','encoding','memory'])
def test_real_worker_control_flow_mock_model(pair,monkeypatch,drift):
    import torch
    a,f=pair;path=a.output.parent/'worker-admission.json';s.dump(path,f['arms']['child']);args=s.arm_args(a,'child',path)
    args.worker_seconds=1400.;args.output.mkdir(parents=True)
    s.dump(args.output.parent/'admission.json',f)
    selected={'weight':torch.nn.Parameter(torch.tensor([2. if drift=='restore' else 1.]),requires_grad=False)}
    net=SimpleNamespace(parameters=lambda:selected.values(),generation_config=SimpleNamespace(eos_token_id=s.common.EOS_IDS))
    monkeypatch.setattr(s.train,'load_policy',lambda *a,**kw:net)
    monkeypatch.setattr(s.train,'restore_policy',lambda *a:selected)
    monkeypatch.setattr(s.old,'checkpoint_state',lambda *a:'config')
    original_load=torch.load
    monkeypatch.setattr(torch,'load',lambda p,**kw:dict(trainable_state={'weight':torch.tensor([1.])}) if Path(p)==args.checkpoint else original_load(p,**kw))
    original_tensor=torch.tensor;original_generator=torch.Generator
    monkeypatch.setattr(torch,'tensor',lambda *a,**kw:original_tensor(*a,**{k:v for k,v in kw.items() if k!='device'}))
    monkeypatch.setattr(torch,'Generator',lambda *a,**kw:original_generator())
    for name in ('manual_seed_all','reset_peak_memory_stats'):monkeypatch.setattr(torch.cuda,name,lambda *a:None)
    peaks=[]
    def memory():
        peaks.append(1)
        return dict(allocated=1,reserved=40*1024**3 if drift=='memory' and len(peaks)>2 else 2)
    monkeypatch.setattr(s.evaluation,'memory',memory)
    monkeypatch.setattr(s.train,'autocast',lambda *a:nullcontext())
    monkeypatch.setitem(sys.modules,'transformers',SimpleNamespace(AutoTokenizer=SimpleNamespace(from_pretrained=lambda *a,**kw:object())))
    enc={r['id']:r for r in f['arms']['child']['encodings']}
    monkeypatch.setattr(s.common,'encode_prompt',lambda t,task:dict(enc[task['id']],rendered_prompt='bad') if drift=='encoding' else copy.deepcopy(enc[task['id']]))
    monkeypatch.setattr(s.common,'decode_reply',lambda *a:'')
    sampled=[]
    def sample(net,ids,**kw):
        sampled.append(kw['generator'].initial_seed())
        if drift=='weights':selected['weight'].data.add_(1.)
        return dict(token_ids=[128009],output_tokens=1,selected_token_logprobs=[-.5],sequence_logprob=-.5,
            token_entropies=[1.],finish_reason='eos',eos_reached=True,hit_token_limit=False,deadline_exceeded=False,
            temperature=1.,distribution='full_vocabulary_categorical',elapsed_seconds=1.)
    monkeypatch.setattr(s,'sample_tokens',sample)
    if drift:
        with pytest.raises((ValueError,RuntimeError)):s.worker(args)
        if drift=='memory':
            assert s.load(args.output/'memory.json')['reserved']==40*1024**3
            recorded=s.rows_at(args.output/'rollouts.jsonl')
            assert recorded[0]['status']=='generated' and len(recorded)==32
            assert all(r['status']=='unattempted' for r in recorded[1:])
        return
    s.worker(args);rows=s.rows_at(args.output/'rollouts.jsonl');w=s.load(args.output/'worker_summary.json')
    s.validate_worker(f['arms']['child'],rows,w,args.output)
    assert sampled==[20261003]*32 and w['phase_complete'] and torch.equal(selected['weight'],original_tensor([1.]))


def test_isolated_source_archive_import(tmp_path):
    for relative in s.SOURCES:
        dest=tmp_path/relative;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(s.ROOT/relative,dest)
    script='import sys; sys.path.insert(0,'+repr(str(tmp_path))+'); from tools import proof_sumsequence_proof_rl_stochastic; print("ok")'
    env=dict(os.environ);env.pop('PYTHONPATH',None)
    result=subprocess.run([sys.executable,'-I','-c',script],cwd=tmp_path,env=env,capture_output=True,text=True,timeout=30)
    assert result.returncode==0,result.stderr
    assert result.stdout.strip()=='ok'
