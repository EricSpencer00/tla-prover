import copy
from types import SimpleNamespace

import pytest
from tools import proof_sumsequence_sany_repair_verify as v


@pytest.fixture(scope='module')
def actual():
    from transformers import AutoTokenizer
    p=v.evaluation.repair
    packet=v.evaluation.packet(v.ROOT/'results/runs/proof-sumsequence-sany-repair-packet-20260906-v1/packet.json')
    tasks=p.policy.greedy.broader.combined_tasks(p.policy.greedy.broader.load_manifests())+p.policy.greedy.extra.static_tasks()
    tokenizer=AutoTokenizer.from_pretrained(p.TOKENIZER,local_files_only=True)
    return packet,tasks,tokenizer


def test_actual_packet_original_task_adapters_and_full_context(actual):
    packet,tasks,tokenizer=actual;chosen=v.bind_tasks(packet,tasks)
    assert [t['id'] for t in chosen]==list(v.evaluation.IDS)
    for task,row in zip(chosen,packet['tasks']):
        encoded=v.evaluation.encode(tokenizer,row)
        assert encoded['status']=='ready' and encoded['input_tokens']+3072<=9216
        assert encoded['input_token_ids']==row['encoding']['input_token_ids']
        fragment=task['reference_fragment']
        extraction=v.checks.extract(task,'```tla\n'+fragment+'\n```')
        assert extraction['fragment']==fragment.strip()
    assert packet['tasks'][0]['encoding']['status']=='context_overflow'
    assert packet['budget']['max_context']==8192


def test_actual_prior_responses_decoder_compatibility_only(actual):
    # Historical response bytes exercise the new encoder/output schema, not new
    # repair generation or a measurement of repair success.
    packet,_,tokenizer=actual
    encodings=[v.evaluation.encode(tokenizer,row) for row in packet['tasks']]
    old=v.load(v.evaluation.repair.GENERATIONS/'accounting.json')
    rows=[]
    for encoding,task in zip(encodings,packet['tasks']):
        raw=old[task['original_index']]
        fields=v.evaluation.base.greedy.output_fields(raw['token_ids'],raw['raw_reply'],late=raw['deadline_exceeded'])
        rows.append(dict(encoding,**fields))
    frozen=dict(budget=v.evaluation.BUDGET,encodings=encodings)
    v.evaluation.validate_rows(frozen,rows,tokenizer)
    changed=copy.deepcopy(rows);changed[1]['raw_reply']+='wrong decode'
    changed[1].update(v.evaluation.base.greedy.output_fields(changed[1]['token_ids'],changed[1]['raw_reply'],late=False))
    with pytest.raises(ValueError):v.evaluation.validate_rows(frozen,changed,tokenizer)
    changed=copy.deepcopy(rows);changed[0]['input_token_ids'].pop()
    with pytest.raises(ValueError):v.evaluation.validate_rows(frozen,changed,tokenizer)


@pytest.mark.parametrize('defect',['context','index','order','denominator','dev'])
def test_original_task_binding_rejects_mutations(actual,defect):
    packet,tasks,_=actual;packet=copy.deepcopy(packet);tasks=copy.deepcopy(tasks)
    if defect=='context':packet['tasks'][0]['context']['prefix']+='TRUE'
    elif defect=='index':packet['tasks'][0]['original_index']=0
    elif defect=='order':packet['tasks'].reverse()
    elif defect=='denominator':packet['original_requested_ids'].pop()
    else:tasks[packet['tasks'][0]['original_index']]['split']='development'
    with pytest.raises(ValueError):v.bind_tasks(packet,tasks)


def selected():
    tasks=[dict(id=i,split='train') for i in v.evaluation.IDS]
    raws=[dict(id=i,raw_reply='sample fixture',finish_reason='eos') for i in v.evaluation.IDS]
    return tasks,raws


def test_selected_repairs_not_pooled_with_original40(tmp_path):
    tasks,raws=selected();raws[0]['finish_reason']='token_limit'
    calls=[]
    def checker(task,raw,work,current):
        calls.append(task['id']);return dict(sany=1,proof=None,status='unknown',evidence=None)
    rows,summary=v.evaluate(tasks,raws,{},tmp_path,checker=checker)
    assert calls==[v.evaluation.IDS[1]]
    assert summary['requested_repairs']==2 and summary['original_denominator']==40
    assert summary['sany_pass']==1 and summary['sany_unknown']==1 and summary['proof_unknown']==2
    assert summary['generation_cap']==1 and summary['original_pass_at1_unchanged']
    assert not summary['pooled_pass_at1_claim'] and not summary['training_authorized'] and not summary['gate_claim']
    rows[0]['proof']=1
    with pytest.raises(ValueError,match='cannot be scored'):v.audit_rows(tasks,raws,rows,{},tmp_path)


def test_budget_retains_both_unknown(tmp_path):
    tasks,raws=selected();ticks=iter((0,180,180,180))
    def fail(*args):raise AssertionError('No checker after deadline')
    rows,summary=v.evaluate(tasks,raws,{},tmp_path,checker=fail,clock=lambda:next(ticks))
    assert len(rows)==2 and all(r['status']=='unmeasured_budget' for r in rows)
    assert not summary['complete'] and summary['proof_unknown']==2


def test_target_pin_checked_before_any_remote_admission(tmp_path,monkeypatch):
    path=tmp_path/'receipt.json';path.write_text('{}')
    def forbidden(*args):raise AssertionError('Remote-only admit must not run locally')
    monkeypatch.setattr(v.evaluation,'admit',forbidden)
    with pytest.raises(ValueError,match='authentic target-host receipt'):
        v.target_admission(SimpleNamespace(target_admission=path,target_admission_sha256='wrong'),None)


def test_observed_remote_paths_exact(tmp_path):
    path=tmp_path/'paths.json';value={k:'/remote/'+k for k in v.REMOTE_KEYS};v.dump(path,value)
    assert v.remote_paths(SimpleNamespace(remote_paths=path))==value
    for replacement in ('relative','/remote/../ambiguous'):
        value['output']=replacement;v.dump(path,value)
        with pytest.raises(ValueError):v.remote_paths(SimpleNamespace(remote_paths=path))


def generation_fixture(tmp_path,monkeypatch):
    output=tmp_path/'collected';output.mkdir()
    worker=dict(elapsed_seconds=100)
    remote={k:'/remote/'+k for k in v.REMOTE_KEYS};pre=10.;seconds=1200-pre-v.evaluation.reserve(pre)
    process={'fixture':'not an actual generation'}
    for name,value in [('accounting.json',[]),('worker_summary.json',worker),('process.json',process)]:v.dump(output/name,value)
    summary=dict(worker,total_seconds=150,process_sha256=v.file_sha(output/'process.json'),admission_sha256='receipt',
        supervisor_pre_admission_seconds=pre,supervisor_post_admission_reserve_seconds=30.,worker_timeout_seconds=seconds)
    v.dump(output/'summary.json',summary)
    monkeypatch.setattr(v.evaluation,'validate_rows',lambda *args:None)
    monkeypatch.setattr(v.evaluation,'validate_worker',lambda *args:None)
    calls=[];monkeypatch.setattr(v.common,'audit_process',lambda *args:calls.append(args))
    return SimpleNamespace(generations=output,target_admission_sha256='receipt'),remote,summary,calls


def test_worker_command_and_remaining_budget_bound(tmp_path,monkeypatch):
    a,remote,summary,calls=generation_fixture(tmp_path,monkeypatch)
    assert v.generation_rows(a,{},remote,None)==[]
    _,command,cwd,budget=calls[0]
    assert command[:3]==[v.common.PYTHON,'/remote/evaluation_root/tools/proof_sumsequence_sany_repair_eval.py','worker']
    assert command[-2:]==['--worker-seconds','1160.0'] and cwd==remote['evaluation_root'] and budget==1160
    assert command[3:13]==sum((['--'+k.replace('_','-'),remote[k]] for k in v.evaluation.INPUTS),[])


@pytest.mark.parametrize('defect',['reserve','elapsed','receipt','summary','nan'])
def test_generation_supervisor_tampering_rejected(tmp_path,monkeypatch,defect):
    a,remote,summary,calls=generation_fixture(tmp_path,monkeypatch)
    if defect=='reserve':summary['supervisor_post_admission_reserve_seconds']=0
    elif defect=='elapsed':summary['total_seconds']=1201
    elif defect=='receipt':summary['admission_sha256']='wrong'
    elif defect=='summary':summary['invented']='extra'
    else:summary['supervisor_pre_admission_seconds']=float('nan')
    v.dump(a.generations/'summary.json',summary)
    with pytest.raises(ValueError):v.generation_rows(a,{},remote,None)


def test_unchanged_existing_worker_raw_guards_are_used():
    import inspect
    source=inspect.getsource(v.generation_rows)
    assert 'evaluation.validate_rows(frozen,rows,tokenizer)' in source
    assert 'evaluation.validate_worker(frozen,rows,worker,a.generations)' in source
    assert 'common.audit_process' in source
    assert 'common.training_linkage' in inspect.getsource(v.prepare)
    assert 'evaluation.admit(' not in inspect.getsource(v)
