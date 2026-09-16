import copy
import json
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

import pytest
from tools import proof_fullmodule_learning_eval as m


def frozen():
    return dict(budget=m.BUDGET,encodings=[dict(id=str(i),prompt_sha256='fixture',rendered_prompt='fixture',
        rendered_prompt_sha256='fixture',input_token_ids=[1],input_token_ids_sha256=m.digest([1]),input_tokens=1,status='ready') for i in range(30)],
        policies=dict(parent=dict(checkpoint_sha256=m.PARENT_SHA),child=dict(checkpoint_sha256='f'*64)),declared_context=16385)


def completed_rows(value):
    return [dict({k:v for k,v in row.items() if k not in ('status','reason')},**m.output_fields([128009],'',late=False)) for row in m.initial_rows(value)]


def test_actual30_packet_encoding_and_context():
    from tools import proof_fullmodule_holdout_packet as p
    from transformers import AutoTokenizer
    path=m.ROOT/'results/runs/proof-fullmodule-holdout-packet-20260906-v1/prompts.json'
    rows=m.packet_rows(SimpleNamespace(packet=path,expected_packet_sha256='af1a0e5ee9477c1f76dc15359c487cdcf1dff365d1a5bbe2d7c5834eab4602eb'))
    tokenizer=AutoTokenizer.from_pretrained(p.TOKENIZER,local_files_only=True)
    for row in rows:
        encoding=m.encode(tokenizer,row)
        assert all(row[k]==v for k,v in encoding.items() if k!='status')
        assert row['split']=='official_holdout30'
    assert max(m.encode(tokenizer,r)['input_tokens'] for r in rows)+16384==17693
    assert m.BUDGET['item_seconds']==45 and not m.BUDGET['official_gate2_replication']


@pytest.mark.parametrize('tokens,late,finish',[([128009],True,'eos'),([1]*16384,True,'token_limit'),([],False,'time_limit'),([1,2],False,'time_limit')])
def test_exact_token_eos_precedence(tokens,late,finish):
    row=m.output_fields(tokens,'',late=late)
    assert row['finish_reason']==finish and row['deadline_exceeded']==late


@pytest.mark.parametrize('tokens',[[128009,1],[True],[-1],[128256],[1]*16385])
def test_invalid_raw_tokens_rejected(tokens):
    with pytest.raises(ValueError):m.output_fields(tokens,'')


def test_complete60_unknown_denominator_and_order():
    value=frozen();rows=m.initial_rows(value);m.validate_rows(value,rows)
    assert len(rows)==60 and all(c['unknown']==30 and c['generated']==0 for c in m.accounting(rows).values())
    rows[0],rows[30]=rows[30],rows[0]
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
    phases += [phase for arm in m.ARMS for phase in [arm+'_generation_restore']+[arm+'_sample_'+str(i) for i in range(30)]]+['after_final_admission']
    records=[dict(phase=p,allocated=1,reserved=2) for p in phases]
    (tmp_path/'memory.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in records))
    rng={}
    for arm in m.ARMS:
        rng[arm]={}
        for label in ('before','after'):
            path=tmp_path/(arm+'_rng_'+label+'.pt')
            torch.save(dict(seed=m.BUDGET['seed'],cpu=torch.tensor([1],dtype=torch.uint8),cuda=torch.tensor([2],dtype=torch.uint8)),path)
            rng[arm][label]=m.file_sha(path)
        m.dump(tmp_path/(arm+'_preflight.json'),dict(arm=arm,synthetic=True,model_result=False,context=16385,prefill_tokens=16384,decode_tokens=1,
            use_cache=True,logits_to_keep=1,token_id=1,logits_finite=True,device='cuda',test_only=False,
            prefill_memory=next(r for r in records if r['phase']==arm+'_preflight_prefill'),
            decode_memory=next(r for r in records if r['phase']==arm+'_preflight_decode')))
    summary=dict(complete=True,counts=m.accounting(rows),elapsed_seconds=100,pre_admission_seconds=40,
        post_admission_reserve_seconds=120,measured_presampling_seconds=80,worker_seconds=3300,memory=records[-1],
        rng_sha256=rng,weights_unchanged=True,restore_exact=True,full_admission_stable=True,optimizer_updates=0,
        verification_pending=True,protected_outputs_never_train=True,gate_claim=False,policies=value['policies'],
        accounting_sha256=m.file_sha(tmp_path/'accounting.json'))
    m.dump(tmp_path/'worker_summary.json',summary)
    return value,tmp_path,summary


def test_complete_raw_worker_fixture(worker_fixture):
    value,path,_=worker_fixture
    assert len(m.validate_worker(value,path))==60


@pytest.mark.parametrize('defect',['sample_time','probe','memory','rng','budget','weights','unknown','events'])
def test_worker_evidence_tampering(worker_fixture,defect):
    value,path,summary=worker_fixture
    if defect=='sample_time':
        rows=m.load(path/'timing.json');rows[0]['limit_seconds']=29;m.dump(path/'timing.json',rows)
    elif defect=='probe':
        row=m.load(path/'parent_preflight.json');row['prefill_tokens']=10;m.dump(path/'parent_preflight.json',row)
    elif defect=='memory':(path/'memory.jsonl').write_text('')
    elif defect=='rng':summary['rng_sha256']['parent']['before']='changed'
    elif defect=='budget':summary['measured_presampling_seconds']=1000
    elif defect=='weights':summary['weights_unchanged']=False
    elif defect=='unknown':
        rows=m.load(path/'accounting.json');rows[0]=m.initial_rows(value)[0];m.dump(path/'accounting.json',rows)
    else:(path/'events.jsonl').write_text('')
    m.dump(path/'worker_summary.json',summary)
    with pytest.raises(ValueError):m.validate_worker(value,path)


def test_source_closure_and_no_future_checker():
    code="""import sys
from pathlib import Path
from tools import proof_fullmodule_learning_eval as m
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
    assert m.load(tmp_path/'worker_failure.json')['requested']==60


def test_declared_budget_not_squeezed_or_official_claim():
    import inspect
    source=inspect.getsource(m._worker)
    assert 'max_new_tokens=16384,max_time=45' in source
    assert '2700+BUDGET' in source and 'min(45' not in source
    assert source.index('preflight(net')<source.index("torch.manual_seed(BUDGET['seed'])")
    assert not m.BUDGET['official_gate2_replication']


@pytest.fixture
def receipt_fixture(tmp_path,monkeypatch):
    output=tmp_path/'training';output.mkdir()
    parent=tmp_path/'parent.pt';parent.write_bytes(b'parent')
    child=output/'policy_optimizer.pt';child.write_bytes(b'new338child')
    args=SimpleNamespace(training_input=tmp_path/'train.json',model_path=tmp_path/'model',
        parent_checkpoint=parent,checkpoint=child,training_output=output,
        training_admission=tmp_path/'admission.json',expected_input_sha256='a'*64,
        expected_child_sha256=m.file_sha(child),
        **{name:tmp_path/name for name in m.learning.PARENT_PATHS})
    admitted=dict(parent_checkpoint_sha256=m.PARENT_SHA,input_sha256='a'*64)
    summary=dict(actual_updates=338,requested_updates=338,checkpoint_sha256=m.file_sha(child))
    m.dump(output/'admission.json',admitted);m.dump(output/'summary.json',summary)
    m.dump(output/'process.json',dict(cwd=str(m.ROOT)))
    m.dump(output/'admitted.json',dict(complete=True,summary_sha256=m.file_sha(output/'summary.json'),
        process_sha256=m.file_sha(output/'process.json')))
    calls=[]
    monkeypatch.setattr(m.learning,'validate_output',lambda a,b:summary)
    monkeypatch.setattr(m,'audit_process',lambda p,c,r,s:calls.append((c,r,s)))
    return args,admitted,summary,calls


def test_actual338_receipt_required_and_exact_command_mechanics(receipt_fixture):
    args,admitted,_,calls=receipt_fixture
    value=m.training_receipt(args,admitted)
    assert value['optimizer_updates']==338 and value['parent_sha256']==m.PARENT_SHA
    assert value['child_sha256']==args.expected_child_sha256
    assert calls[0][2]==1800
    command=calls[0][0]
    for name in m.learning.PATHS:assert '--'+name.replace('_','-') in command
    assert command[-4:]==['--expected-input-sha256','a'*64,'--admission',str(args.training_output/'admission.json')]


def test_training_paths_and_receipt_command_canonicalize_aliases(receipt_fixture,tmp_path):
    args,admitted,_,calls=receipt_fixture
    alias=tmp_path/'alias';alias.symlink_to(tmp_path,target_is_directory=True)
    original=m.training_args(args)
    mapping={'training_input':'input','model_path':'model_path','parent_checkpoint':'checkpoint',
        'training_output':'output','training_admission':'admission',**{n:n for n in m.learning.PARENT_PATHS}}
    for source in mapping:
        setattr(args,source,alias/getattr(args,source).relative_to(tmp_path))
    canonical=m.training_args(args)
    assert vars(canonical)==vars(original)
    m.training_receipt(args,admitted)
    command=calls[0][0]
    assert command[command.index('--output')+1]==str(original.output)
    assert command[-1]==str(original.output/'admission.json')
    assert not any(str(alias) in part for part in command)


@pytest.mark.parametrize('defect',['old84','incomplete','wrong_child','same_parent','wrong_input','wrong_parent','receipt','process'])
def test_training_receipt_mutations_fail(receipt_fixture,defect,monkeypatch):
    args,admitted,summary,_=receipt_fixture
    if defect=='old84':summary['actual_updates']=84
    elif defect=='incomplete':summary['requested_updates']=337
    elif defect=='wrong_child':args.expected_child_sha256='b'*64
    elif defect=='same_parent':monkeypatch.setattr(m,'PARENT_SHA',args.expected_child_sha256)
    elif defect=='wrong_input':args.expected_input_sha256='c'*64
    elif defect=='wrong_parent':admitted['parent_checkpoint_sha256']='d'*64
    elif defect=='receipt':m.dump(args.training_output/'admitted.json',dict(complete=True))
    else:
        def fail(*a):raise ValueError('Actual process incomplete')
        monkeypatch.setattr(m,'audit_process',fail)
    with pytest.raises(ValueError):m.training_receipt(args,admitted)


def test_new_budget_never_mutates_old_contract():
    from tools import proof_fullmodule_holdout_eval as old
    assert old.BUDGET['item_seconds']==30 and old.BUDGET['seed']==20261007
    assert m.BUDGET['item_seconds']==45 and m.BUDGET['seed']==20261009
    assert m.BUDGET['seconds']==3420 and m.reserve(100)==125
    assert m.HASH_ARGS==('expected_packet_sha256','expected_input_sha256','expected_child_sha256')


def test_isolated_exact_source_only_closure(tmp_path):
    import shutil
    actual=m.sources()
    for name in actual:
        target=tmp_path/name;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(m.ROOT/name,target)
    code="from tools import proof_fullmodule_learning_eval as m; assert m.sources(); print(len(m.sources()))"
    result=subprocess.run([sys.executable,'-I','-c','import sys;sys.path.insert(0,'+repr(str(tmp_path))+');'+code],
        cwd=tmp_path,check=True,capture_output=True,text=True,timeout=30)
    assert int(result.stdout.strip())==len(actual)


def test_pbs_bounded_shell_contract():
    path=m.ROOT/'tools/proof_fullmodule_learning_eval.pbs'
    subprocess.run(['bash','-n',str(path)],check=True)
    code=path.read_text()
    assert '3500s' in code and 'walltime=01:00:00' in code
    assert '--expected-child-sha256' in code and '--expected-input-sha256' in code


def good_process():
    return dict(command=['python','worker'],cwd='/observed/training/stage',execution_complete=True,
        cleanup_complete=True,output_complete=True,root_reaped=True,timed_out=False,output_limit=False,
        surviving_owned_processes=[],errors=[],returncode=0,output='',seconds=100)


def test_actual_training_stage_not_evaluation_stage():
    value=good_process()
    m.audit_process(value,value['command'],Path('/observed/training/stage'),1800)
    with pytest.raises(ValueError):m.audit_process(value,value['command'],m.ROOT,1800)


@pytest.mark.parametrize('key,value',[('execution_complete',False),('cleanup_complete',False),('output_complete',False),
    ('root_reaped',False),('timed_out',True),('output_limit',True),('surviving_owned_processes',[1]),
    ('errors',['cleanup']),('returncode',True),('returncode',1),('seconds',float('nan')),('seconds',1801)])
def test_strict_owned_process_failures(key,value):
    row=good_process();row[key]=value
    with pytest.raises(ValueError):m.audit_process(row,['python','worker'],Path('/observed/training/stage'),1800)
