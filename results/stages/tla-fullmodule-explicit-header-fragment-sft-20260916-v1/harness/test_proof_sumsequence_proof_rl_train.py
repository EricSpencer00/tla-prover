import argparse
from copy import deepcopy
import json
from pathlib import Path
from types import SimpleNamespace
import pytest
from tools import proof_sumsequence_proof_rl_train as driver


def test_budget_allocator_import_order_and_pbs():
    source=Path(driver.__file__).read_text()
    assert source.index('import proof_sumsequence_proof_rl_packet')<source.index('import torch')
    assert driver.SECONDS==driver.packet.BUDGET['seconds']==900
    assert driver.CHECKPOINT_RESERVE==driver.packet.BUDGET['checkpoint_reserve']==120
    assert driver.HOST_LIMIT==driver.packet.BUDGET['host_memory_limit']==64*1024**3
    assert driver.SEED==driver.packet.BUDGET['seed']==20261004
    pbs=Path(driver.__file__).with_suffix('.pbs').read_text()
    assert '#PBS -q debug' in pbs and '#PBS -A EVITA' in pbs
    assert 'select=1:system=polaris' in pbs and '950s' in pbs and '01:00:00' in pbs


def test_memory_evidence_persisted_before_host_guard(tmp_path,monkeypatch):
    monkeypatch.setattr(driver,'peak_rss',lambda:driver.HOST_LIMIT+1)
    events=[]
    with pytest.raises(ValueError,match='RSS'):driver.record_guard(tmp_path,events,'cpu',cuda=False)
    assert json.loads((tmp_path/'memory.json').read_bytes())[0]['peak_rss_bytes']==driver.HOST_LIMIT+1


def test_memory_evidence_persisted_before_gpu_guard(tmp_path,monkeypatch):
    monkeypatch.setattr(driver,'peak_rss',lambda:100)
    monkeypatch.setattr(driver.probe,'allocator_evidence',lambda:{'sentinel':'raw failure'})
    with pytest.raises(ValueError):driver.record_guard(tmp_path,[],'gpu')
    assert json.loads((tmp_path/'memory.json').read_bytes())[0]['allocator']=={'sentinel':'raw failure'}


def test_full_feedback_and_eligible_request_binding():
    update=SimpleNamespace(groups=[{'eligible':True}],requests=[dict(sample_id=f's{i}') for i in range(4)])
    rows=deepcopy(update.requests)
    feedback=dict(groups=update.groups,requested_samples=32,accounted_samples=32)
    driver.bind_requests(update,rows,feedback)
    rows.reverse()
    with pytest.raises(ValueError):driver.bind_requests(update,rows,feedback)
    feedback['accounted_samples']=31
    with pytest.raises(ValueError):driver.bind_requests(update,update.requests,feedback)


def test_checkpoint_save_once_reload_actual_tensors_and_logits(tmp_path):
    import torch
    from tools.proof_cpu_gradient_update import CPUGradientUpdate
    from harness.test_proof_cpu_gradient_update import rewards,fill
    class Tiny(torch.nn.Module):
        def __init__(self):
            super().__init__();self.weights=torch.nn.ParameterList([torch.nn.Parameter(torch.ones(2)) for _ in range(9)])
        def forward(self,input_ids,use_cache=False):
            logits=sum(self.weights).expand(1,input_ids.shape[1],2)
            return SimpleNamespace(logits=logits)
    net=Tiny();selected=dict(net.named_parameters());update=CPUGradientUpdate(selected,rewards())
    fill(update);prepared=update.prepare();update.commit()
    config=dict(model_files={'fixture':'cpu'},dtype_profile=driver.train.PROFILE,_parent_state=update.initial)
    phases=[];path=tmp_path/'policy_optimizer.pt'
    report=driver.save_reload(net,selected,prepared,config,[1,2,3],path,device='cpu',guard=phases.append)
    assert report['reload_tensors_exact'] and report['reload_logits_exact']
    assert report['logits_before']==report['logits_after']
    saved=torch.load(path,weights_only=False)
    assert config['_parent_state'] is update.initial
    assert saved['trainable_state'] is saved['cpu_update']['trainable_state']
    assert saved['optimizer'] is saved['cpu_update']['optimizer_state']
    assert saved['config']['dtype_profile']==driver.train.PROFILE
    assert saved['optimizer']['param_groups'][0]['lr']==1e-6
    assert saved['python_rng_state'] and saved['torch_rng_state'].dtype==torch.uint8
    assert phases==['before_checkpoint_save','after_checkpoint_save','before_checkpoint_reload','after_checkpoint_reload']
    config['_parent_state']=update.initial
    with pytest.raises(FileExistsError):driver.save_reload(net,selected,prepared,config,[1,2,3],path,device='cpu')


def test_failure_preserves_unknown_update_and_malformed_ledger(tmp_path,monkeypatch):
    args=argparse.Namespace(output=tmp_path/'output',admission=tmp_path/'admission.json')
    for name in driver.PATHS:setattr(args,name,tmp_path/name)
    def fail(a):
        (a.output/'rows.json').write_text('truncated')
        raise ValueError('Original admission failure')
    monkeypatch.setattr(driver,'admit',fail)
    with pytest.raises(ValueError,match='Original admission'):driver.run(args)
    summary=json.loads((args.output/'summary.json').read_bytes())
    assert summary['complete'] is False and summary['optimizer_updates'] is None
    assert summary['accounted_gradient_samples']==0
    assert 'ledger_error' in json.loads((args.output/'failure.json').read_bytes())


def test_failure_retains_completed_cpu_update_not_false_zero(tmp_path,monkeypatch):
    args=argparse.Namespace(output=tmp_path/'output',admission=tmp_path/'admission.json')
    for name in driver.PATHS:setattr(args,name,tmp_path/name)
    def fail(a):
        driver.train.dump(a.output/'stage.json',dict(phase='cpu_adamw_completed',optimizer_updates=1,
                          gpu_committed=False,checkpoint_writes=0))
        raise ValueError('Post-optimizer guard failure')
    monkeypatch.setattr(driver,'admit',fail)
    with pytest.raises(ValueError):driver.run(args)
    summary=json.loads((args.output/'summary.json').read_bytes())
    assert summary['optimizer_updates']==1 and summary['gpu_committed'] is False
    assert summary['checkpoint_writes']==0 and summary['accounted_gradient_samples']==4


def execution_fixture():
    original=[dict(sample_id=f's{i}') for i in range(4)]
    gradients={n:dict(norm=1.,dtype='torch.float32',elements=count) for n,count in driver.probe.GRADIENT_ELEMENTS.items()}
    results=[dict(sample_id=r['sample_id'],gradients=deepcopy(gradients)) for r in original]
    ledger=[dict(sample_id=r['sample_id'],gradients={n:dict(**g,shape=[g['elements']],source_device='cuda:0')
             for n,g in gradients.items()}) for r in original]
    phases=['after_cpu_adamw','after_child_commit','before_checkpoint_save','after_checkpoint_reload','after_final_admission']
    phases+=['after_cpu_accumulate_'+r['sample_id'] for r in original]
    memory=[dict(phase=p,peak_rss_bytes=100,allocator={}) for p in phases]
    reload=dict(logits_before=[[0.]*128256],logits_after=[[0.]*128256])
    return original,results,dict(ledger=deepcopy(ledger)),ledger,memory,reload,5.


def test_complete_raw_execution_evidence(monkeypatch):
    monkeypatch.setattr(driver.probe,'guard_allocator',lambda r:None)
    driver.validate_execution_evidence(*execution_fixture())


@pytest.mark.parametrize('mutation',['empty_memory','missing_phase','missing_gpu','ledger','raw_norm','raw_dtype',
                                   'raw_elements','order','logit_shape','logit_nan','elapsed_nan','elapsed_large'])
def test_execution_evidence_tampering_fails_closed(monkeypatch,mutation):
    monkeypatch.setattr(driver.probe,'guard_allocator',lambda r:None)
    original,results,update,ledger,memory,reload,elapsed=execution_fixture()
    if mutation=='empty_memory':memory=[]
    if mutation=='missing_phase':memory.pop()
    if mutation=='missing_gpu':memory[0].pop('allocator')
    if mutation=='ledger':ledger[0]['sample_id']='other'
    name=next(iter(driver.probe.GRADIENT_ELEMENTS))
    if mutation=='raw_norm':results[0]['gradients'][name]['norm']=2.
    if mutation=='raw_dtype':results[0]['gradients'][name]['dtype']='torch.bfloat16'
    if mutation=='raw_elements':results[0]['gradients'][name]['elements']=0
    if mutation=='order':results.reverse()
    if mutation=='logit_shape':reload['logits_before'][0].pop()
    if mutation=='logit_nan':reload['logits_after'][0][0]=float('nan')
    if mutation=='elapsed_nan':elapsed=float('nan')
    if mutation=='elapsed_large':elapsed=901
    with pytest.raises(ValueError):driver.validate_execution_evidence(original,results,update,ledger,memory,reload,elapsed)
