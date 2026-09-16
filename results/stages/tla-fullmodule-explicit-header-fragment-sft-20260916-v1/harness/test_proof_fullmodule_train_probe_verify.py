"""CPU-only verifier mechanics; no generated model or native SANY claims."""
import copy
from pathlib import Path
from types import SimpleNamespace
import pytest
from tools import proof_fullmodule_train_probe_verify as m


@pytest.fixture
def population():
    tasks=[dict(id=f'probe-{i}',split='train') for i in range(20)]
    selected=[dict(probe=t,checker_task=dict(id=f'original-{i}'),control_order=i) for i,t in enumerate(tasks)]
    raws=[dict(arm=arm,id=t['id'],raw_reply='reference',finish_reason='eos') for arm in m.evaluation.ARMS for t in tasks]
    return tasks,selected,raws


def actual():
    tasks=m.packet.validate_export(m.load(m.ROOT/'results/runs/proof-fullmodule-train-probe-packet-20260906-v1/prompts.json'))
    value=m.load(m.packet.INPUT)
    root=m.ROOT/'results/runs/proof-fullmodule-training-checks-20260906-v1'
    return tasks,value,root


def test_actual20_reference_staging_and_encoding_without_protected_reads(monkeypatch):
    for module,name in [(m.lineage,'prepare'),(m.lineage,'admitted_packet'),(m.controls,'inputs'),(m.controls,'audit')]:
        monkeypatch.setattr(module,name,lambda *a,**k:pytest.fail('Protected/whole audit traversal prohibited'))
    tasks,value,root=actual()
    originals,selected=m.bind_tasks(tasks,value,root)
    assert len(originals)==128 and len(selected)==20
    assert [s['checker_task']['id'] for s in selected]==[t['control_task_id'] for t in tasks]
    assert m.packet.select(m.packet.INPUT.read_bytes())==tasks
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(m.ROOT/'results/runs/proof-cuda-tokenizer-20260905-v2',local_files_only=True)
    for task in tasks:
        encoded=m.evaluation.encode(tokenizer,task)
        assert all(task[k]==v for k,v in encoded.items() if k!='status')
    assert max(t['required_context'] for t in tasks)==17113


@pytest.mark.parametrize('field,value',[('module_name','Foreign'),('source_sha256','a'*64),('audit_index',-1),('audit_row_sha256','a'*64),('split','holdout')])
def test_reference_binding_tamper(field,value):
    tasks,training,root=actual();tasks=copy.deepcopy(tasks);tasks[0][field]=value
    with pytest.raises(ValueError,match='binding'):m.bind_tasks(tasks,training,root)


def test40_attempts_use_original_task_adapter(tmp_path,population,monkeypatch):
    tasks,selected,raws=population;calls=[]
    def checker(task,reply,path,current,timeout):
        calls.append((task,path,timeout));return dict(sany=1,status='pass')
    rows,summary=m.evaluate(tasks,selected,raws,{},tmp_path,checker=checker)
    assert len(calls)==40 and [c[0] for c in calls]==[s['checker_task'] for s in selected]*2
    assert all(c[2]==30 for c in calls)
    assert summary['complete'] and summary['arms']['parent']['sany_pass']==20
    assert summary['train_only'] and summary['syntax_only']
    assert not any(summary[k] for k in ('training_authorized','holdout_claim','generalization_claim','gate2_claim','tlc_claim','proof_claim','nonvacuity_claim','pooled_score'))
    audited=[];monkeypatch.setattr(m.checks,'audit',lambda *a:audited.append(a))
    m.audit_rows(tasks,selected,raws,rows,{},tmp_path)
    assert len(audited)==40 and [a[0] for a in audited]==[s['checker_task'] for s in selected]*2
    rows[0]['sany']=0
    with pytest.raises(ValueError,match='Raw SANY'):m.audit_rows(tasks,selected,raws,rows,{},tmp_path)


def test_caps_timeouts_remain_unknown(tmp_path,population):
    tasks,selected,raws=population
    for i,raw in enumerate(raws):raw['finish_reason']='token_limit' if i%2 else 'time_limit'
    rows,summary=m.evaluate(tasks,selected,raws,{},tmp_path,checker=lambda *a,**k:pytest.fail('Incomplete generation checked'))
    assert all(r['sany'] is None for r in rows) and len(summary['paired']['unknown'])==20
    m.audit_rows(tasks,selected,raws,rows,{},tmp_path)
    rows[0]['sany']=0
    with pytest.raises(ValueError,match='remains unknown'):m.audit_rows(tasks,selected,raws,rows,{},tmp_path)


def test_checker_budget_preserves40_unknown(tmp_path,population):
    tasks,selected,raws=population;times=iter([0]+[601]*20+[631]+[632]+[1233]*20+[1263])
    rows,summary=m.evaluate(tasks,selected,raws,{},tmp_path,clock=lambda:next(times),checker=lambda *a,**k:pytest.fail('Out of budget'))
    assert not summary['complete'] and len(rows)==40 and all(r['status']=='unmeasured_budget' for r in rows)


@pytest.mark.parametrize('mutation',[lambda r:r.pop(),lambda r:r.reverse(),lambda r:r[0].update(id='foreign'),lambda r:r[0].update(arm='third')])
def test_wrong_keys_rejected(population,mutation):
    tasks,_,raws=population;mutation(raws)
    with pytest.raises(ValueError):m.validate_keys(tasks,raws)


def test_all40_persist_before_runtime_admission(tmp_path,population,monkeypatch):
    tasks,_,_=population;a=SimpleNamespace(output=tmp_path/'result')
    for name in m.LOCAL_PATHS:setattr(a,name,tmp_path/name)
    monkeypatch.setattr(m,'admitted_packet',lambda a:tasks)
    monkeypatch.setattr(m,'identity',lambda *a:(_ for _ in ()).throw(ValueError('runtime unavailable')))
    with pytest.raises(ValueError,match='runtime unavailable'):m.verify(a)
    rows=m.load(a.output/'rows.json');summary=m.load(a.output/'summary.json')
    assert len(rows)==40 and all(r['sany'] is None for r in rows) and not summary['complete']


def test_target_hash_precedes_model_reads(tmp_path):
    receipt=tmp_path/'receipt';m.dump(receipt,{})
    a=SimpleNamespace(target_admission=receipt,target_admission_sha256='wrong')
    with pytest.raises(ValueError,match='receipt hash'):m.target_admission(a,[],None)


def test_no_target_model_or_protected_admission_calls():
    source=Path(m.__file__).read_text()
    for forbidden in ('evaluation.paired_admit(', 'evaluation.validate_output(', 'lineage.prepare(', 'lineage.admitted_packet(', 'controls.inputs(', 'controls.audit('):
        assert forbidden not in source
    assert 'lineage.training_linkage(a,frozen,tokenizer,remote)' in source
    assert 'checks.audit(task,candidate,value' in source


def test_authentic256_receipt_selects_exact40_raw_controls(monkeypatch):
    tasks,training,root=actual();originals,selected=m.bind_tasks(tasks,training,root)
    before=m.load(root/'identity_before.json');calls=[]
    monkeypatch.setattr(m.checks,'identity',lambda t:before['runtime'])
    monkeypatch.setattr(m.checks,'audit',lambda *a:calls.append(a))
    current=m.admit_controls(SimpleNamespace(controls=root),originals,selected)
    assert current==before['runtime'] and len(calls)==40
    assert [a[0]['id'] for a in calls]==[s['checker_task']['id'] for s in selected for _ in range(2)]
    assert all(str(a[3]).startswith(str(root/'checks')) for a in calls)


def test_generation_process_and_supervisor_exact_linkage(tmp_path,monkeypatch):
    pre=100.;post=m.evaluation.reserve(pre);seconds=3420-pre-post
    a=SimpleNamespace(generations=tmp_path,target_admission_sha256='a'*64)
    for name in m.evaluation.HASH_ARGS:setattr(a,name,'b'*64)
    remote={name:'/observed/'+name for name in m.evaluation.PATHS}
    remote.update(evaluation_root='/observed/root',output='/observed/root/results/paired')
    command=[m.lineage.prior.common.PYTHON,remote['evaluation_root']+'/tools/proof_fullmodule_train_probe_eval.py','worker']
    for name in m.evaluation.PATHS:command+=['--'+name.replace('_','-'),remote[name]]
    for name in m.evaluation.HASH_ARGS:command+=['--'+name.replace('_','-'),getattr(a,name)]
    command+=['--admission',remote['output']+'/admission.json','--output',remote['output'],'--worker-seconds',str(seconds)]
    process=dict(command=command,cwd=remote['evaluation_root'],returncode=0,output='',seconds=20,root_reaped=True,
        execution_complete=True,cleanup_complete=True,output_complete=True,timed_out=False,output_limit=False,errors=[],surviving_owned_processes=[])
    worker=dict(worker_seconds=seconds,elapsed_seconds=10)
    m.dump(tmp_path/'process.json',process);m.dump(tmp_path/'worker_summary.json',worker)
    summary=dict(worker,total_seconds=30,supervisor_pre_admission_seconds=pre,
        supervisor_post_admission_reserve_seconds=post,worker_timeout_seconds=seconds,
        admission_sha256=a.target_admission_sha256,process_sha256=m.file_sha(tmp_path/'process.json'))
    m.dump(tmp_path/'summary.json',summary);calls=[]
    monkeypatch.setattr(m.evaluation,'validate_worker',lambda *a:calls.append(a) or ['validated40'])
    assert m.generation_rows(a,{},remote,'actual-tokenizer')==['validated40']
    assert calls[0][2]=='actual-tokenizer'
    process['cleanup_complete']=False;m.dump(tmp_path/'process.json',process)
    with pytest.raises(ValueError,match='owned process'):m.generation_rows(a,{},remote,'actual-tokenizer')
