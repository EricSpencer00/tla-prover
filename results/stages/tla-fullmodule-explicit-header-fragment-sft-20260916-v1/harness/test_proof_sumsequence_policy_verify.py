import argparse
from copy import deepcopy
import json

import pytest

from tools import proof_sumsequence_policy_verify as module


def write(path,value):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(value))


def process(command,cwd):
    return dict(command=command,cwd=str(cwd),returncode=0,output='',seconds=1.,
        timed_out=False,execution_complete=True,cleanup_complete=True,output_complete=True)


@pytest.fixture
def prepared(tmp_path,monkeypatch):
    import transformers
    a=argparse.Namespace(output=tmp_path/'verified',prompts=tmp_path/'prompts.json',
        generations=tmp_path/'generated',tokenizer_path=tmp_path/'tokenizer',checkpoint=tmp_path/'child.pt',
        remote_root='/canonical/stage',remote_checkpoint_path='/canonical/child.pt',
        remote_model_path='/canonical/model')
    a.tokenizer_path.mkdir(); a.checkpoint.write_bytes(b'child')
    monkeypatch.setattr(module.policy,'CHILD_SHA',module.file_sha(a.checkpoint))
    tasks=[]
    for name in module.packet.TRAIN_IDS:
        theorem=name.removeprefix('sumsequence-')
        statement='THEOREM '+theorem+' == TRUE\n'
        tasks.append(dict(id=name,split='train',theorem_name=theorem,statement=statement,
                          prefix='---- MODULE Fixture ----\n'+statement))
    portable=[dict(t,prompt='prompt') for t in tasks]
    exported={'tasks':portable}
    write(a.prompts,exported)
    monkeypatch.setattr(module.packet,'export_tasks',lambda:(exported,tasks))
    monkeypatch.setattr(module.policy,'packet',lambda p:(p.read_bytes(),portable))
    monkeypatch.setattr(transformers.AutoTokenizer,'from_pretrained',lambda *a,**k:object())
    encode=lambda tokenizer,t:dict(id=t['id'],split='train',status='ready',input_token_ids=[1],input_tokens=1)
    monkeypatch.setattr(module.policy.common,'encode_prompt',encode)
    monkeypatch.setattr(module.policy.common,'decode_reply',lambda tokenizer,ids:'OBVIOUS')
    files={'weights.safetensors':'fixture'}
    monkeypatch.setattr(module.policy.common,'MODEL_FILES_SHA',module.digest(files))
    for arm in module.ARMS:
        root=a.generations/arm;root.mkdir(parents=True)
        inputs=[encode(None,t) for t in tasks]
        admission=dict(budget=deepcopy(module.policy.BUDGET),prompts_sha256=module.sha(a.prompts.read_bytes()),
            model_files=files,model_files_sha256=module.digest(files),
            versions=module.policy.common.FIRST_VERSIONS,checkpoint_sha256=module.policy.CHILD_SHA if arm=='child' else None,
            arm='checkpoint' if arm=='child' else 'base',eos_token_ids=module.policy.common.EOS_IDS,
            input_evidence=inputs,implementation_sha256={n:module.file_sha(module.ROOT/n) for n in module.policy.SOURCES})
        write(root/'admission.json',admission)
        rows=[dict(r,**module.policy.common.output_fields([5,128009],set(module.policy.common.EOS_IDS),'OBVIOUS')) for r in inputs]
        (root/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
        cmd=['/home/eric-spencer/ChatTLA/.venv/bin/python',a.remote_root+'/tools/proof_sumsequence_policy_eval.py','worker',
            '--prompts',a.remote_root+'/prompts.json','--expected-input-sha256',admission['prompts_sha256'],
            '--model-path',a.remote_model_path,'--admission',a.remote_root+'/results/'+arm+'/admission.json',
            '--output',a.remote_root+'/results/'+arm]
        if arm=='child':cmd+=['--checkpoint',a.remote_checkpoint_path]
        write(root/'process.json',process(cmd,a.remote_root))
        write(root/'summary.json',dict(requested_tasks=4,accounted_rows=4,unattempted_ids=[],complete=True,
            returncode=0,timed_out=False,optimizer_updates=0,eos_completed=4))
        write(root/'runtime.json',dict(optimizer_updates=0,checkpoint_restored_exactly=arm=='child',reserved=100,allocated=80))
    module.policy.write_batch_summary(a.generations)
    return a,tasks,exported


def test_complete_local_admission(prepared):
    a,tasks,_=prepared
    found,arms=module.prepare(a)
    assert found==tasks and all(v['execution_complete'] for v in arms.values())


@pytest.mark.parametrize('file,key,value',[
    ('admission.json','arm','base'),('admission.json','prompts_sha256','bad'),
    ('admission.json','implementation_sha256',{}),('process.json','cwd','/wrong'),
    ('runtime.json','checkpoint_restored_exactly',False),('runtime.json','reserved',2**50),
    ('summary.json','accounted_rows',3),('summary.json','eos_completed',0),
    ('process.json','seconds',1001),('process.json','seconds',float('nan')),
])
def test_rejects_provenance_mutations(prepared,file,key,value):
    a,_,_=prepared
    path=a.generations/'child'/file
    data=module.load(path);data[key]=value;write(path,data)
    with pytest.raises(ValueError):module.prepare(a)


def test_collected_checkpoint_required(prepared):
    a,_,_=prepared;a.checkpoint.write_bytes(b'other')
    with pytest.raises(ValueError,match='collected child'):module.prepare(a)


def test_coordinated_decoder_tampering_rejected(prepared):
    a,_,_=prepared;p=a.generations/'base/generations.jsonl'
    rows=[json.loads(s) for s in p.read_text().splitlines()]
    rows[0]['raw_reply']='changed';rows[0]['raw_reply_sha256']=module.sha(b'changed')
    p.write_text(''.join(json.dumps(r)+'\n' for r in rows))
    with pytest.raises(ValueError,match='output reconstruction'):module.prepare(a)


def test_partial_line_not_salvaged(prepared):
    a,_,_=prepared;p=a.generations/'base/generations.jsonl'
    p.write_text(p.read_text()+'{"partial":')
    with pytest.raises(ValueError,match='Incomplete raw'):module.prepare(a)


@pytest.fixture
def evaluating(prepared,monkeypatch):
    a,tasks,exported=prepared
    found,arms=module.prepare(a)
    monkeypatch.setattr(module,'prepare',lambda a:(found,arms))
    monkeypatch.setattr(module,'identity',lambda *a:{'fixed':True})
    monkeypatch.setattr(module,'extract',lambda *a:{'fragment':'OBVIOUS'})
    monkeypatch.setattr(module,'audit_result',lambda *a:None)
    calls=[]
    def checker(task,fragment,work,timeout):
        calls.append((task,fragment,work,timeout))
        return dict(classification='proof_success',certified=True,measured_model_outcome=True)
    return a,tasks,arms,calls,checker


def test_all_eight_separate_matched_checks(evaluating):
    a,_,_,calls,checker=evaluating
    result=module.evaluate(a,checker=checker)
    assert result['complete'] and len(calls)==8 and all(c[3]==30 for c in calls)
    assert all(v['certified_tasks']==4 for v in result['per_arm'].values())


@pytest.mark.parametrize('finish',['token_limit','time_limit'])
def test_incomplete_generation_never_checked(evaluating,finish):
    a,_,arms,calls,checker=evaluating
    arms['base']['rows'][0]['finish_reason']=finish
    result=module.evaluate(a,checker=checker)
    assert len(calls)==7 and result['per_arm']['base']['unknown_outcomes']==1


def test_failed_generation_process_entire_arm_unknown(evaluating):
    a,_,arms,calls,checker=evaluating;arms['base']['execution_complete']=False
    result=module.evaluate(a,checker=checker)
    assert len(calls)==4 and result['per_arm']['base']['unknown_outcomes']==4


def test_identity_drift_no_completed_claim(evaluating,monkeypatch):
    a,_,_,_,checker=evaluating
    count=[0]
    def identity(*a):count[0]+=1;return {'call':count[0]}
    monkeypatch.setattr(module,'identity',identity)
    with pytest.raises(ValueError,match='identity drift'):module.evaluate(a,checker=checker)
    result=module.load(a.output/'summary.json')
    assert not result['complete'] and all(v['certified_tasks']==0 for v in result['per_arm'].values())


def test_budget_keeps_unattempted_denominator(evaluating):
    a,_,_,calls,checker=evaluating
    tick=[0]
    def clock():tick[0]+=300;return tick[0]
    result=module.evaluate(a,checker=checker,clock=clock)
    assert not calls and all(v['unknown_outcomes']==4 for v in result['per_arm'].values())


def test_failed_admission_preserves_eight_keys(prepared):
    a,_,_=prepared;a.checkpoint.write_bytes(b'wrong')
    with pytest.raises(ValueError):module.evaluate(a)
    assert len(module.load(a.output/'rows.json'))==8
    assert not module.load(a.output/'summary.json')['complete']


def test_outer_incomplete_cannot_certify(tmp_path):
    work=tmp_path/'check';work.mkdir()
    task={'id':'fixture'};fragment='OBVIOUS'
    cmd=[module.sys.executable,str(module.ROOT/'tools/proof_token_rl_stochastic_tlaps.py'),'worker',
        '--input',str(work/'input.json'),'--output',str(work/'worker')]
    p=process(cmd,work);p['cleanup_complete']=False
    write(work/'process.json',p);write(work/'input.json',dict(task=task,fragment=fragment,timeout=28.5))
    result=dict(process=p,seconds=1.,certified=False,measured_model_outcome=False)
    module.audit_result(task,fragment,result,work)
    result['certified']=True
    with pytest.raises(ValueError,match='Incomplete checker'):module.audit_result(task,fragment,result,work)


def test_actual_packet_references_and_saved_simple_reply_extract():
    tasks=module.packet.static_tasks()
    for task in tasks:
        adapted=module.extraction_context(task)
        assert adapted['prefix']==task['prefix'] and adapted['statement']==task['statement']
        assert module.extract(task['reference_fragment'],adapted)['fragment'] is not None
    front=tasks[0]
    result=module.extract('BY DEF Front',module.extraction_context(front))
    assert result['fragment']=='BY DEF Front'


def test_bad_task_metadata_raises_before_model_classification():
    task=module.packet.static_tasks()[0]
    task['statement']='LEMMA Different == FALSE\n'
    with pytest.raises(ValueError,match='statement/prefix'):
        module.extraction_context(task)
