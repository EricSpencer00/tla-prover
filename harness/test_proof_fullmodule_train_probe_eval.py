import copy
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

import pytest
from tools import proof_fullmodule_train_probe_eval as m


def frozen():
    return dict(budget=m.BUDGET,encodings=[dict(id=str(i),prompt_sha256='fixture',rendered_prompt='fixture',
        rendered_prompt_sha256='fixture',input_token_ids=[1],input_token_ids_sha256=m.digest([1]),input_tokens=1,status='ready') for i in range(20)],
        policies=dict(parent=dict(checkpoint_sha256=m.PARENT_SHA),child=dict(checkpoint_sha256='f'*64)),declared_context=17113)


def completed_rows(value):
    return [dict({k:v for k,v in row.items() if k not in ('status','reason')},**m.output_fields([128009],'',late=False)) for row in m.initial_rows(value)]


def test_actual_train20_encoding_and_context():
    from transformers import AutoTokenizer
    tasks=m.packet.select(m.packet.INPUT.read_bytes())
    tokenizer=AutoTokenizer.from_pretrained(m.packet.TOKENIZER,local_files_only=True)
    for row in tasks:
        encoding=m.encode(tokenizer,row)
        assert all(row[k]==v for k,v in encoding.items() if k!='status')
        assert row['split']=='train'
    assert len(tasks)==20
    assert max(m.encode(tokenizer,r)['input_tokens'] for r in tasks)+16384==17113
    assert m.BUDGET['item_seconds']==45 and m.BUDGET['seed']==20261010
    assert m.BUDGET['train_only'] and not m.BUDGET['official_gate2_replication']


@pytest.mark.parametrize('tokens,late,finish',[([128009],True,'eos'),([1]*16384,True,'token_limit'),([],False,'time_limit'),([1,2],False,'time_limit')])
def test_exact_token_eos_precedence(tokens,late,finish):
    row=m.output_fields(tokens,'',late=late)
    assert row['finish_reason']==finish and row['deadline_exceeded']==late


@pytest.mark.parametrize('tokens',[[128009,1],[True],[-1],[128256],[1]*17113])
def test_invalid_raw_tokens_rejected(tokens):
    with pytest.raises(ValueError):m.output_fields(tokens,'')


def test_complete60_unknown_denominator_and_order():
    value=frozen();rows=m.initial_rows(value);m.validate_rows(value,rows)
    assert len(rows)==40 and all(c['unknown']==20 and c['generated']==0 for c in m.accounting(rows).values())
    rows[0],rows[20]=rows[20],rows[0]
    with pytest.raises(ValueError):m.validate_rows(value,rows)


@pytest.mark.parametrize('defect',['cap_promoted','decode','input','missing','arm','eos'])
def test_raw_row_tampering_rejected(defect):
    value=frozen();rows=completed_rows(value)
    if defect=='cap_promoted':rows[0].update(m.output_fields([1]*16384,''));rows[0]['finish_reason']='eos'
    elif defect=='decode':rows[0]['raw_reply']='changed'
    elif defect=='input':rows[0]['input_token_ids']=[2]
    elif defect=='missing':rows.pop()
    elif defect=='arm':rows[0]['arm']='child'
    else:rows[0]['token_ids']=[128009,1]
    with pytest.raises(ValueError):m.validate_rows(value,rows)


def test_memory_saved_before_guard(tmp_path,monkeypatch):
    import torch
    monkeypatch.setattr(torch.cuda,'max_memory_allocated',lambda:36*1024**3)
    monkeypatch.setattr(torch.cuda,'max_memory_reserved',lambda:36*1024**3+1)
    with pytest.raises(ValueError):m.memory(tmp_path,'failed')
    assert json.loads((tmp_path/'memory.jsonl').read_text())['reserved']==36*1024**3+1


def test_tiny_actual_causal_cache_fullcontext_probe(tmp_path):
    import torch
    from transformers import LlamaConfig,LlamaForCausalLM
    torch.set_num_threads(2)
    net=LlamaForCausalLM(LlamaConfig(vocab_size=16,hidden_size=16,intermediate_size=32,
        num_hidden_layers=2,num_attention_heads=2,num_key_value_heads=1)).eval()
    events=[]
    def measure(phase):
        events.append(phase);return dict(phase=phase,allocated=1,reserved=2)
    value=m.preflight(net,dict(declared_context=33),tmp_path,'parent',device='cpu',measure=measure,
        release=lambda:events.append('release'),test_only=True)
    assert value['prefill_tokens']==32 and value['decode_tokens']==1 and value['logits_finite']
    assert value['test_only'] and not value['model_result']
    assert events==['parent_preflight_prefill','parent_preflight_decode','release']
    with pytest.raises(ValueError):m.preflight(net,dict(declared_context=33),tmp_path,'parent',device='cpu')


@pytest.fixture
def worker_fixture(tmp_path):
    import torch
    value=frozen();rows=completed_rows(value)
    m.dump(tmp_path/'accounting.json',rows)
    (tmp_path/'events.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    m.dump(tmp_path/'timing.json',[dict(arm=r['arm'],id=r['id'],limit_seconds=45,actual_seconds=.1) for r in rows])
    phases=['after_model_load']+[arm+'_preflight_'+phase for arm in m.ARMS for phase in ('restore','prefill','decode')]
    phases += [phase for arm in m.ARMS for phase in [arm+'_generation_restore']+[arm+'_sample_'+str(i) for i in range(20)]]+['after_final_admission']
    records=[dict(phase=p,allocated=1,reserved=2) for p in phases]
    (tmp_path/'memory.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
    rng={}
    for arm in m.ARMS:
        rng[arm]={}
        for label in ('before','after'):
            path=tmp_path/(arm+'_rng_'+label+'.pt')
            torch.save(dict(seed=m.BUDGET['seed'],cpu=torch.tensor([1],dtype=torch.uint8),cuda=torch.tensor([2],dtype=torch.uint8)),path)
            rng[arm][label]=m.file_sha(path)
        m.dump(tmp_path/(arm+'_preflight.json'),dict(arm=arm,synthetic=True,model_result=False,context=17113,prefill_tokens=17112,decode_tokens=1,
            use_cache=True,logits_to_keep=1,token_id=1,logits_finite=True,device='cuda',test_only=False,
            prefill_memory=next(r for r in records if r['phase']==arm+'_preflight_prefill'),
            decode_memory=next(r for r in records if r['phase']==arm+'_preflight_decode')))
    summary=dict(complete=True,counts=m.accounting(rows),elapsed_seconds=100,pre_admission_seconds=40,
        post_admission_reserve_seconds=120,measured_presampling_seconds=80,worker_seconds=3300,memory=records[-1],
        rng_sha256=rng,weights_unchanged=True,restore_exact=True,full_admission_stable=True,optimizer_updates=0,
        verification_pending=True,train_only=True,gate_claim=False,policies=value['policies'],
        accounting_sha256=m.file_sha(tmp_path/'accounting.json'))
    m.dump(tmp_path/'worker_summary.json',summary)
    return value,tmp_path,summary


def test_complete_raw_worker_fixture(worker_fixture):
    value,path,_=worker_fixture
    assert len(m.validate_worker(value,path))==40


@pytest.mark.parametrize('defect',['sample_time','probe','memory','rng','budget','weights','unknown','events'])
def test_worker_evidence_tampering(worker_fixture,defect):
    value,path,summary=worker_fixture
    if defect=='sample_time':
        rows=m.load(path/'timing.json');rows[0]['limit_seconds']=29;m.dump(path/'timing.json',rows)
    elif defect=='probe':
        row=m.load(path/'parent_preflight.json');row['prefill_tokens']=10;m.dump(path/'parent_preflight.json',row)
    elif defect=='memory':(path/'memory.jsonl').write_text('')
    elif defect=='rng':summary['rng_sha256']['parent']['before']='changed'
    elif defect=='budget':summary['measured_presampling_seconds']=2000
    elif defect=='weights':summary['weights_unchanged']=False
    elif defect=='unknown':
        rows=m.load(path/'accounting.json');rows[0]=m.initial_rows(value)[0];m.dump(path/'accounting.json',rows)
    else:(path/'events.jsonl').write_text('')
    m.dump(path/'worker_summary.json',summary)
    with pytest.raises(ValueError):m.validate_worker(value,path)


def test_source_closure_and_no_future_checker():
    code="""import sys
from pathlib import Path
from tools import proof_fullmodule_train_probe_eval as m
actual=m.sources();missing=[]
for obj in list(sys.modules.values()):
 p=getattr(obj,'__file__',None)
 if not p:continue
 try:n=Path(p).resolve().relative_to(m.ROOT).as_posix()
 except ValueError:continue
 if n.startswith(('tools/','harness/')) and '/.venv/' not in n and not n.endswith('__init__.py') and n not in actual:missing.append(n)
assert not missing,missing
assert not any('proof_fullmodule_holdout_check' in n for n in actual)
"""
    subprocess.run([sys.executable,'-c',code],cwd=m.ROOT,check=True,timeout=30)


def test_probe_failure_preserves_all60_initial_keys(tmp_path,monkeypatch):
    rows=m.initial_rows(frozen());m.dump(tmp_path/'accounting.json',rows)
    def fail(a):raise ValueError('synthetic preflight failed')
    monkeypatch.setattr(m,'_worker',fail)
    with pytest.raises(ValueError,match='synthetic preflight'):m.worker(SimpleNamespace(output=tmp_path))
    assert m.load(tmp_path/'accounting.json')==rows
    assert m.load(tmp_path/'worker_failure.json')['requested']==40


def test_declared_budget_not_squeezed_or_official_claim():
    import inspect
    source=inspect.getsource(m._worker)
    assert 'max_new_tokens=16384,max_time=45' in source
    assert '1800+BUDGET' in source and 'min(45' not in source
    assert source.index('preflight(net')<source.index("torch.manual_seed(BUDGET['seed'])")
    assert not m.BUDGET['official_gate2_replication']


def test_frozen_pure_helpers_reused_without_global_changes():
    for name in ('encode','training_args','training_receipt','output_fields','unknown','memory','preflight','restore','audit_process'):
        assert getattr(m,name) is getattr(m.lineage,name)
    assert m.lineage.BUDGET['requested_total']==60 and m.lineage.BUDGET['seed']==20261009
    assert m.BUDGET['requested_total']==40 and m.BUDGET['seed']==20261010


def test_portable_train_packet_runtime_cannot_call_protected_functions(tmp_path,monkeypatch):
    from tools import proof_fullmodule_holdout_packet as protected
    value=m.packet.prepare()
    path=tmp_path/'train20.json';m.dump(path,value)
    def forbidden(*a,**kw):raise AssertionError('Protected data function invoked')
    for name,obj in vars(protected).copy().items():
        if callable(obj) and getattr(obj,'__module__',None)==protected.__name__:
            monkeypatch.setattr(protected,name,forbidden)
    monkeypatch.setattr(m.lineage,'paired_admit',forbidden)
    args=SimpleNamespace(packet=path,expected_packet_sha256=m.file_sha(path),
        expected_input_sha256=m.packet.INPUT_SHA,expected_child_sha256=m.packet.POLICIES['child'])
    assert m.packet_rows(args)==value['tasks']
    assert len(m.learning.packet.validate_training_packet(m.load(m.packet.INPUT)))==169
    assert m.environment(value)==value['prompt_environment']
    assert m.sources()


@pytest.mark.parametrize('field',['expected_input_sha256','expected_child_sha256','expected_packet_sha256'])
def test_train_packet_policy_and_input_pins_required(tmp_path,field):
    value=m.packet.prepare();path=tmp_path/'train20.json';m.dump(path,value)
    args=SimpleNamespace(packet=path,expected_packet_sha256=m.file_sha(path),
        expected_input_sha256=m.packet.INPUT_SHA,expected_child_sha256=m.packet.POLICIES['child'])
    setattr(args,field,'bad')
    with pytest.raises(ValueError):m.packet_rows(args)


def test_isolated_source_closure_and_pbs(tmp_path):
    import shutil
    sources=m.sources()
    for name in sources:
        target=tmp_path/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(m.ROOT/name,target)
    result=subprocess.run([sys.executable,'-I','-c',
        'import sys;sys.path.insert(0,".");from tools import proof_fullmodule_train_probe_eval as m;print(len(m.sources()))'],
        cwd=tmp_path,capture_output=True,text=True,check=True,timeout=30)
    assert int(result.stdout.strip())==len(sources)
    pbs=m.ROOT/'tools/proof_fullmodule_train_probe_eval.pbs'
    subprocess.run(['bash','-n',str(pbs)],check=True)
    assert '3500s' in pbs.read_text() and 'walltime=01:00:00' in pbs.read_text()
