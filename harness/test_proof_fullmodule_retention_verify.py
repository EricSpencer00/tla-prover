import copy
import inspect
import json
from pathlib import Path
from types import SimpleNamespace
import pytest
from tools import proof_fullmodule_retention_verify as module


def test_remote_paths_exact_absolute_inventory(tmp_path):
    path=tmp_path/'paths.json';value={k:'/remote/'+k for k in module.REMOTE_KEYS}
    module.dump(path,value);assert module.remote_paths(path)==value
    for key,replacement in [('model_path','relative'),('checkpoint','/a/../b'),('output','/a//b')]:
        bad=dict(value);bad[key]=replacement;module.dump(path,bad)
        with pytest.raises(ValueError):module.remote_paths(path)
    module.dump(path,dict(value,foreign='/elsewhere'))
    with pytest.raises(ValueError):module.remote_paths(path)


def test_authentic_receipt_hash_required(tmp_path):
    path=tmp_path/'receipt.json';module.dump(path,dict(complete=True))
    assert module.authenticated(path,module.file_sha(path))==dict(complete=True)
    with pytest.raises(ValueError,match='Authentic'):module.authenticated(path,'0'*64)


def test_local_adapter_never_calls_target_only_admission():
    text=Path(module.__file__).read_text()
    for forbidden in ('evaluation.admit(', 'evaluation.prospective_admit(', 'evaluation.validate_output(', 'learning.admit('):
        assert forbidden not in text
    assert 'lineage.training_linkage(' in text
    assert 'evaluation.validate_worker(' in text


@pytest.fixture
def generation(tmp_path,monkeypatch):
    remote={key:'/remote/'+key for key in module.REMOTE_KEYS}
    a=SimpleNamespace(generations=tmp_path,target_admission_sha256='a'*64,expected_child_sha256='c'*64)
    frozen=dict(training_admission=dict(input_sha256='b'*64))
    rows=dict(greedy40=[dict(id=str(i)) for i in range(40)],repair2=[dict(id=str(i)) for i in range(2)])
    monkeypatch.setattr(module.evaluation,'validate_worker',lambda f,p:rows)
    validated=[]
    monkeypatch.setattr(module.evaluation,'validate_rows',lambda f,phase,r,t:validated.append((phase,r,t)))
    worker=dict(elapsed_seconds=200,complete=True)
    module.dump(tmp_path/'worker_summary.json',worker)
    pre=10;post=module.evaluation.reserve(pre);seconds=module.evaluation.SECONDS-pre-post
    command=[module.common.PYTHON,str(Path(remote['evaluation_root'])/'tools/proof_fullmodule_retention_eval.py'),'worker']
    for key in module.evaluation.PATHS:command+=['--'+key.replace('_','-'),remote[key]]
    command+=['--expected-input-sha256','b'*64,'--expected-child-sha256','c'*64,'--prospective',remote['prospective'],
        '--admission',str(Path(remote['output'])/'admission.json'),'--output',remote['output'],'--worker-seconds',str(seconds)]
    process=dict(command=command,cwd=remote['evaluation_root'],returncode=0,output='',seconds=201,
        timed_out=False,execution_complete=True,cleanup_complete=True,output_complete=True)
    module.dump(tmp_path/'process.json',process)
    summary=dict(worker,total_seconds=250,process_sha256=module.file_sha(tmp_path/'process.json'),
        admission_sha256='a'*64,supervisor_pre_admission_seconds=pre,
        supervisor_post_admission_reserve_seconds=post,worker_timeout_seconds=seconds)
    module.dump(tmp_path/'summary.json',summary)
    return a,frozen,remote,rows,validated


def test_actual_remote_command_audit_and_each_phase_decoder(generation):
    a,frozen,remote,rows,validated=generation
    assert module.generation_rows(a,frozen,remote,'tokenizer')==rows
    assert validated==[('greedy40',rows['greedy40'],'tokenizer'),('repair2',rows['repair2'],'tokenizer')]


@pytest.mark.parametrize('field',['execution_complete','cleanup_complete','output_complete'])
def test_incomplete_owned_process_rejected(generation,field):
    a,frozen,remote,_,_=generation
    path=a.generations/'process.json';value=module.load(path);value[field]=False;module.dump(path,value)
    summary=module.load(a.generations/'summary.json');summary['process_sha256']=module.file_sha(path)
    module.dump(a.generations/'summary.json',summary)
    with pytest.raises(ValueError,match='owned process'):module.generation_rows(a,frozen,remote,None)


def test_remote_command_cannot_be_relabelled_to_local_path(generation):
    a,frozen,remote,_,_=generation
    changed=dict(remote,checkpoint='/different/policy_optimizer.pt')
    with pytest.raises(ValueError,match='owned process'):module.generation_rows(a,frozen,changed,None)


@pytest.mark.parametrize('change',[
    lambda s:s.update(admission_sha256='0'*64),
    lambda s:s.update(supervisor_post_admission_reserve_seconds=0),
    lambda s:s.update(worker_timeout_seconds=3000),
    lambda s:s.update(total_seconds=3001),
    lambda s:s.update(elapsed_seconds=999),
])
def test_supervisor_receipt_mutation_rejected(generation,change):
    a,frozen,remote,_,_=generation
    summary=module.load(a.generations/'summary.json');change(summary);module.dump(a.generations/'summary.json',summary)
    with pytest.raises(ValueError):module.generation_rows(a,frozen,remote,None)


def test_missing_tokenizer_file_cannot_pass(tmp_path):
    (tmp_path/'tokenizer.json').write_text('{}')
    expected=dict(tokenizer_json='unused')
    with pytest.raises(ValueError,match='tokenizer'):
        module.tokenizer_files(tmp_path,{'tokenizer.json':'0'*64,'config.json':'a'*64})


def test_actual_selected2_binding_uses_original_statements():
    source=inspect.getsource(module.prepare)
    assert 'checks.admit_controls' in source and 'old_repair.bind_tasks' in source
    assert 'validate_inputs' in source


def test_identity_drift_during_prepare_blocks_all_checks(tmp_path,monkeypatch):
    a=SimpleNamespace(output=tmp_path/'output',prospective_sha256='a'*64,target_admission_sha256='b'*64)
    for name in module.LOCAL_PATHS:
        path=tmp_path/(name+'.json');path.write_text('{}');setattr(a,name,path)
    tasks=dict(greedy40=[{'id':'one'}],repair2=[{'id':'one'}])
    monkeypatch.setattr(module.checks,'admit_tasks',lambda value:tasks['greedy40'])
    monkeypatch.setattr(module.evaluation.repair,'packet',lambda path:{})
    monkeypatch.setattr(module.old_repair,'bind_tasks',lambda packet,original:tasks['repair2'])
    calls=[]
    identities=iter([{'before':True},{'changed':True}])
    monkeypatch.setattr(module,'identity',lambda *args:next(identities))
    def prepare(args):
        calls.append('prepare');return tasks,{}, {}, {}, {}
    monkeypatch.setattr(module,'prepare',prepare)
    monkeypatch.setattr(module,'evaluate',lambda *args:pytest.fail('No checks after admission drift'))
    with pytest.raises(ValueError,match='during full local admission'):module.verify(a)
    assert calls==['prepare']
    assert module.load(a.output/'identity_before.json')=={'before':True}
    assert module.load(a.output/'summary.json')['complete'] is False
    assert len(module.load(a.output/'rows.json'))==84


def test_prepare_complete_production_dispatch_without_protected_data(tmp_path,monkeypatch):
    import transformers
    tasks,arms,policies=inputs()
    args=SimpleNamespace(prompts=tmp_path/'prompts.json',repair_packet=tmp_path/'repair.json',
        controls=tmp_path/'controls',baseline_combined=tmp_path/'baseline',remote_paths=tmp_path/'remote.json',
        tokenizer_path=tmp_path/'tokenizer',expected_child_sha256=policies['child'])
    args.controls.mkdir();module.dump(args.controls/'process.json',{})
    module.dump(args.prompts,{})
    for phase in module.PHASES:
        path=args.baseline_combined/phase;path.mkdir(parents=True)
        module.dump(path/'accounting.json',arms['parent'][phase])
    monkeypatch.setattr(module,'remote_paths',lambda path:{'observed':True})
    monkeypatch.setattr(module.checks,'admit_tasks',lambda value:tasks['greedy40'])
    monkeypatch.setattr(module.checks,'admit_controls',lambda path,tasks:{'actual_controls':46})
    monkeypatch.setattr(module.common,'audit_process',lambda *args:None)
    monkeypatch.setattr(module.evaluation.repair,'packet',lambda path:{'selected':True})
    monkeypatch.setattr(module.old_repair,'bind_tasks',lambda packet,original:tasks['repair2'])
    tokenizer=object()
    monkeypatch.setattr(transformers.AutoTokenizer,'from_pretrained',lambda *a,**kw:tokenizer)
    calls=[]
    def receipt(a,t):
        assert a is args and t is tokenizer;calls.append('receipts');return {},{'actual':338},{}
    monkeypatch.setattr(module,'receipts',receipt)
    def linkage(a,frozen,t,remote):
        assert frozen=={'actual':338} and t is tokenizer and remote=={'observed':True}
        calls.append('338_lineage');return {'child_sha256':policies['child']}
    monkeypatch.setattr(module.lineage,'training_linkage',linkage)
    monkeypatch.setattr(module.lineage,'admitted_packet',lambda *a:pytest.fail('No protected data in retention'))
    monkeypatch.setattr(module.lineage,'target_admission',lambda *a:pytest.fail('No fullmodule receipt adapter'))
    monkeypatch.setattr(module,'generation_rows',lambda a,f,r,t:arms['child'])
    actual=module.prepare(args)
    assert actual[:3]==(tasks,arms,policies) and calls==['receipts','338_lineage']


c=module

def inputs():
    whole = [dict(id=i,split='development' if 32<=n<36 else 'train') for n,i in enumerate(c.evaluation.requested_ids('greedy40'))]
    tasks = dict(greedy40=whole,repair2=[next(t for t in whole if t['id']==i) for i in c.REPAIR_IDS])
    arms = {a: {p: [dict(id=t['id'], raw_reply='unit fixture', finish_reason='eos') for t in ts]
                for p, ts in tasks.items()} for a in ('parent', 'child')}
    return tasks, arms, dict(parent=c.evaluation.PARENT_SHA, child='a'*64)


def success(*args):
    return dict(sany=1, proof=1, status='proof_success', evidence=None)


def test_complete_separate_denominators(tmp_path):
    tasks, arms, policies = inputs()
    arms['parent']['repair2'][0]['finish_reason'] = 'token_limit'
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=success)
    assert len(rows) == 84 and summary['complete'] and not summary['pooled_score']
    assert summary['phases']['greedy40']['arms']['parent']['proof_pass'] == 40
    assert summary['phases']['repair2']['arms']['parent']['proof_pass'] == 1
    assert summary['phases']['repair2']['arms']['parent']['proof_unknown'] == 1
    assert summary['phases']['greedy40']['arms']['parent']['per_population']['original_development']['requested'] == 4
    assert summary['phases']['repair2']['paired']['proof']['unknown'] == [c.REPAIR_IDS[0]]
    assert not summary['phases']['repair2']['paired']['proof']['gains']
    assert {r['policy_sha256'] for r in rows} == set(policies.values())
    assert (tmp_path/'rows.json').is_file()


@pytest.mark.parametrize('defect', ['count','order','phase','policy','binding','split'])
def test_exact_contract_required(tmp_path, defect):
    tasks, arms, policies = inputs()
    if defect == 'count': arms['child']['greedy40'].pop()
    elif defect == 'order': arms['parent']['repair2'].reverse()
    elif defect == 'phase': arms['child'].pop('repair2')
    elif defect == 'policy': policies['child'] = c.evaluation.PARENT_SHA
    elif defect == 'binding': tasks['repair2'] = copy.deepcopy(tasks['repair2']); tasks['repair2'][0]['theorem'] = 'changed'
    else: tasks['repair2'][0]['split'] = 'development'
    with pytest.raises(ValueError): c.evaluate(tasks, arms, policies, {}, tmp_path, checker=success)


def test_deadlines_preserve84_unknowns(tmp_path):
    tasks, arms, policies = inputs()
    tick = [-3000]
    def clock(): tick[0] += 3000; return tick[0]
    def forbidden(*args): raise AssertionError('checker after deadline')
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=forbidden, clock=clock)
    assert len(rows) == 84 and not summary['complete']
    assert all(r['sany'] is None and r['proof'] is None for r in rows)
    c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)
    rows[0]['proof'] = 1
    with pytest.raises(ValueError): c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)


def test_raw_provenance_and_extraction_audit(tmp_path, monkeypatch):
    tasks, arms, policies = inputs()
    extraction = dict(fragment=None)
    monkeypatch.setattr(c.checks, 'extract', lambda *args: extraction)
    def reject(task, raw, *args):
        return dict(sany=0, proof=0, status='model_extraction', evidence=None,
                    extraction=extraction, raw_reply_sha256=c.sha(raw.encode()))
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=reject)
    c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)
    assert summary['phases']['greedy40']['arms']['child']['sany_reject'] == 40
    rows[-1]['policy_sha256'] = 'b'*64
    with pytest.raises(ValueError): c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)


def test_original_task_reference_extractors_bind_both_phases():
    from tools import proof_sumsequence_sany_repair_packet as p
    ts = p.policy.greedy.broader.combined_tasks(p.policy.greedy.broader.load_manifests()) + p.policy.greedy.extra.static_tasks()
    selected = [next(t for t in ts if t['id'] == i) for i in c.REPAIR_IDS]
    for task in selected:
        fragment = task['reference_fragment']
        assert c.checks.extract(task, '```tla\n'+fragment+'\n```')['fragment'] == fragment.strip()
    tasks = dict(greedy40=ts, repair2=selected)
    arms = {a: {p: [dict(id=t['id']) for t in rows] for p, rows in tasks.items()} for a in ('parent', 'child')}
    c.validate_inputs(tasks, arms, dict(parent=c.evaluation.PARENT_SHA, child='a'*64))


def test_phase_specific_losses_not_hidden_by_repair_gains(tmp_path):
    tasks, arms, policies = inputs()
    def checker(task, raw, output, current):
        passed = not ('child/greedy40' in str(output) and task['id'] == c.REPAIR_IDS[0])
        return dict(sany=int(passed), proof=int(passed), status='fixture', evidence=None)
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=checker)
    assert summary['phases']['greedy40']['paired']['proof']['losses'] == [c.REPAIR_IDS[0]]
    assert not summary['phases']['repair2']['paired']['proof']['losses']
    rows[0]['sany'] = True
    with pytest.raises(ValueError): c.summarize(rows, True)
