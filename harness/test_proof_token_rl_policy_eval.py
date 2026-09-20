"""Contract tests only; synthetic outcomes are not model/SANY measurements."""
import copy
import json
from pathlib import Path
from types import SimpleNamespace

import pytest
import torch

from tools import proof_token_rl_policy_eval as e
from tools import proof_token_rl_packet as p
from harness.test_proof_token_rl_packet import row

ROOT = Path(__file__).resolve().parents[1]


@pytest.fixture
def parent():
    return p.load_requests((ROOT/'results/runs/proof-token-rl-requests-20260906-v1/requests.json').read_bytes(),e.worker.REQUESTS_SHA)


def test_child_contract_is_distinct_and_parent_immutable(parent):
    old=copy.deepcopy(parent); child=e.derive_requests(parent)
    assert parent==old
    assert child['policy_sha256']==e.CHILD_SHA != p.POLICY_SHA
    assert child['seed']==20260929 and child['sampling_seconds']==1200
    assert child['max_optimizer_updates']==0
    assert [r['sample_id'] for r in child['requests']]==[r['sample_id'] for r in parent['requests']]
    assert child['tasks']==parent['tasks']
    assert all(r['policy_sha256']==e.CHILD_SHA for r in child['requests'])
    with pytest.raises(ValueError): p.validate_requests(child)
    child['tasks'][0]['prompt']='mutated'
    assert parent==old


def test_strict_tlaps_training_packet_not_relabelled(parent):
    parent['reward_stage']='strict_tlaps'
    for r in parent['requests']:r['reward_stage']='strict_tlaps'
    with pytest.raises(ValueError,match='Partial SANY'):e.derive_requests(parent)


@pytest.mark.parametrize('count',[0,31,33])
def test_exact32_count(parent,count):
    child=e.derive_requests(parent)
    rows=[row(child['requests'][i%32]) for i in range(count)]
    with pytest.raises(ValueError):e.validate_rows(child,rows)


def test_parent_rows_cannot_be_child_evaluation(parent):
    with pytest.raises(ValueError):e.validate_rows(e.derive_requests(parent),[row(r) for r in parent['requests']])


def test_order_and_request_hash_binding(parent):
    child=e.derive_requests(parent);rows=[row(r) for r in child['requests']]
    assert len(e.validate_rows(child,rows))==32
    rows[0],rows[1]=rows[1],rows[0]
    with pytest.raises(ValueError):e.validate_rows(child,rows)


def test_incomplete_accounting_not_syntax_failure(parent):
    child=e.derive_requests(parent);rows=[row(r) for r in child['requests']]
    rows[0]=row(child['requests'][0],[7],'time_limit')
    rows[1]=dict(child['requests'][1],request_sha256=p.digest(child['requests'][1]),status='unattempted',reason='deadline')
    dispositions=e.validate_rows(child,rows)
    assert sum(r['measured_generation'] for r in dispositions)==30
    assert not dispositions[0]['requires_verifier'] and not dispositions[1]['requires_verifier']


@pytest.mark.parametrize('field,value',[('policy_sha256',p.POLICY_SHA),('temperature',.7),
    ('raw_reply','changed'),('selected_token_logprobs',[]),('token_ids',[1]),('reward',1)])
def test_child_rollout_mutations_rejected(parent,field,value):
    child=e.derive_requests(parent);rows=[row(r) for r in child['requests']]
    rows[0][field]=value
    with pytest.raises(ValueError):e.validate_rows(child,rows)


def test_admission_rejects_wrong_child_before_model_loading(parent,tmp_path,monkeypatch):
    requests=tmp_path/'requests.json';requests.write_bytes(p.canonical_bytes(parent)+b'\n')
    broader=ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json'
    checkpoint=tmp_path/'wrong.pt';checkpoint.write_bytes(b'not child')
    args=SimpleNamespace(requests=requests,broader_prompts=broader,checkpoint=checkpoint,
        model_path=tmp_path/'model',output=tmp_path/'output')
    with pytest.raises(ValueError,match='Exact frozen child'):e.admit(args)
    assert not args.output.exists()


def test_admission_rejects_output_overwriting_input(parent,tmp_path):
    args=SimpleNamespace(requests=tmp_path/'requests',broader_prompts=tmp_path/'broader',
        model_path=tmp_path/'model',checkpoint=tmp_path/'checkpoint',output=tmp_path/'model'/'out')
    with pytest.raises(ValueError,match='isolated'):e.admit(args)


def test_checkpoint_cannot_be_empty_or_parent():
    from tools.proof_cuda_train import PROFILE
    saved=dict(config=dict(model_files={},dtype_profile=PROFILE,policy_sha256=p.POLICY_SHA,
        requests_sha256=e.worker.REQUESTS_SHA,reward_stage='sany_partial',trainable_names=[]),trainable_state={})
    with pytest.raises(ValueError,match='child configuration'):e.check_checkpoint(saved,{})


def test_source_attestation_contains_generator_and_decoder():
    hashes=e.source_hashes()
    for name in ('tools/proof_token_rl_policy_eval.py','tools/proof_token_rl_sampling.py',
                 'tools/proof_cuda_train.py','tools/proof_cuda_eval.py','tools/proof_token_rl_rewards.py'):
        assert hashes[name]==e.file_sha(ROOT/name)


def test_no_optimizer_or_checkpoint_output_path_in_generator():
    import ast
    tree=ast.parse(Path(e.__file__).read_text())
    calls=[node for node in ast.walk(tree) if isinstance(node,ast.Call)]
    assert not any(isinstance(c.func,ast.Attribute) and c.func.attr in ('AdamW','backward','step','save_pretrained') for c in calls)
    assert not any(isinstance(c.func,ast.Name) and c.func.id in ('save_reload','one_update') for c in calls)


@pytest.fixture
def runtime(parent,tmp_path,monkeypatch):
    """Execute production control flow with tiny CPU tensors and fake CUDA I/O."""
    import transformers
    from tools import proof_cuda_train as train, proof_cuda_eval as decoder
    from tools import proof_token_rl_sampling as sampling, proof_token_rl_rewards as bridge
    from contextlib import nullcontext
    args=SimpleNamespace(requests=tmp_path/'requests.json',broader_prompts=tmp_path/'broader.json',
        model_path=tmp_path/'model',checkpoint=tmp_path/'child.pt',output=tmp_path/'generation')
    args.requests.write_bytes(p.canonical_bytes(parent)+b'\n')
    args.broader_prompts.write_bytes((ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json').read_bytes())
    args.checkpoint.write_bytes(b'fake checkpoint')
    realsha=e.file_sha
    monkeypatch.setattr(e,'file_sha',lambda path:e.CHILD_SHA if Path(path)==args.checkpoint else realsha(path))
    monkeypatch.setattr(e,'check_checkpoint',lambda saved,files:'config-hash')
    monkeypatch.setattr(e.worker,'MODEL_SHA',p.digest({}))
    def encode(tokenizer,task):
        return dict(id=task['id'],prompt_sha256=task['prompt_sha256'],input_token_ids=[1,2],
            input_token_ids_sha256=p.digest([1,2]),input_tokens=2,rendered_prompt='prompt',
            rendered_prompt_sha256=p.sha(b'prompt'),status='ready')
    monkeypatch.setattr(decoder,'encode_prompt',encode)
    monkeypatch.setattr(decoder,'decode_reply',lambda tok,ids:'')
    monkeypatch.setattr(transformers.AutoTokenizer,'from_pretrained',lambda *a,**kw:object())
    evaluation=e.derive_requests(parent)
    config=dict(evaluation=evaluation,evaluation_sha256=p.digest(evaluation),checkpoint_sha256=e.CHILD_SHA,
        checkpoint_config_sha256='config-hash',implementation_sha256=e.source_hashes(),model_files={},
        **e.worker.VERSIONS,temperature=1.,max_new_tokens=3072,max_context=8192,requested_samples=32,
        broader_prompts_sha256=p.BROADER_SHA,cuda_memory_limit_bytes=e.worker.MEMORY_LIMIT,
        seed=e.worker.SEED,sampling_seconds=1200,optimizer_updates=0,
        dtype_profile=train.PROFILE,scope=e.SCOPE,proof_success_claim=False,generalization_claim=False,
        cpu_thread_profile=e.CPU_PROFILE,
        encodings=[encode(None,t) for t in evaluation['tasks']])
    args.admission=tmp_path/'frozen-admission.json'
    e.dump(args.admission,config)
    monkeypatch.setattr(e,'admit',lambda a:copy.deepcopy(config))
    net=torch.nn.Linear(1,1,bias=False).requires_grad_(False)
    net.generation_config=SimpleNamespace(eos_token_id=p.EOS_IDS)
    saved={'trainable_state':{'weight':net.weight.detach().clone()}}
    real_load=torch.load
    monkeypatch.setattr(torch,'load',lambda path,**kw:copy.deepcopy(saved) if Path(path)==args.checkpoint else real_load(path,**kw))
    monkeypatch.setattr(train,'load_policy',lambda *a:net)
    monkeypatch.setattr(train,'restore_policy',lambda *a:{'weight':net.weight})
    monkeypatch.setattr(train,'autocast',lambda *a:nullcontext())
    realtensor=torch.tensor;realgenerator=torch.Generator
    monkeypatch.setattr(torch,'tensor',lambda *a,**kw:realtensor(*a,**dict(kw,device='cpu')))
    monkeypatch.setattr(torch,'Generator',lambda **kw:realgenerator(device='cpu'))
    for name,value in {'reset_peak_memory_stats':None,'get_device_name':'fake CPU test',
            'get_device_capability':(8,0),'current_device':0,'max_memory_allocated':100,
            'max_memory_reserved':200,'get_device_properties':SimpleNamespace(total_memory=1000)}.items():
        monkeypatch.setattr(torch.cuda,name,lambda *a,v=value:v)
    def sample(*a,**kw):
        template=row(evaluation['requests'][0])
        fields=('token_ids','output_tokens','selected_token_logprobs','sequence_logprob','token_entropies',
            'finish_reason','eos_reached','hit_token_limit','deadline_exceeded','temperature','distribution','elapsed_seconds')
        return {k:template[k] for k in fields}
    monkeypatch.setattr(sampling,'sample_tokens',sample)
    tasks={t['id']:dict(t,theorem_name='Example') for t in parent['tasks']}
    events=[]
    monkeypatch.setattr(bridge,'prepare',lambda path:(parent,tasks,object()))
    monkeypatch.setattr(bridge,'identity',lambda tasks:{'fake':'stable'})
    monkeypatch.setattr(bridge,'admit_controls',lambda *a:events.append('controls'))
    monkeypatch.setattr(bridge,'extract',lambda *a:{'fragment':'BY Fake'})
    def check(*a,**kw):events.append('check');return dict(status='pass',reward=1)
    monkeypatch.setattr(bridge,'check',check)
    monkeypatch.setattr(bridge,'audit_check',lambda *a:events.append('audit'))
    return SimpleNamespace(args=args,config=config,net=net,saved=saved,events=events,
        bridge=bridge,sampling=sampling,decoder=decoder,train=train)


def verify_args(runtime):
    a=runtime.args
    return SimpleNamespace(requests=a.requests,checkpoint=a.checkpoint,generation=a.output,
        controls=a.output.parent/'controls',output=a.output.parent/'assessment')


def test_generate_verify_execution(runtime):
    initial=runtime.net.weight.clone();generated=e.generate(runtime.args)
    assert generated['accounted_samples']==32 and generated['optimizer_updates']==0
    assert torch.equal(initial,runtime.net.weight)
    assert not (runtime.args.output/'policy_optimizer.pt').exists()
    assessed=e.verify(verify_args(runtime))
    assert assessed['sany_passes']==32 and assessed['unmeasured']==0
    assert runtime.events==['controls']+['check','audit']*32
    assert not assessed['proof_success_claim'] and not assessed['generalization_claim']


def test_generate_deadline_accounts_unattempted(runtime,monkeypatch):
    times=iter([0,1300]+[1400]*40)
    monkeypatch.setattr(e.time,'monotonic',lambda:next(times))
    e.generate(runtime.args)
    rows=[json.loads(s) for s in (runtime.args.output/'rollouts.jsonl').read_text().splitlines()]
    assert len(rows)==32 and all(r['status']=='unattempted' for r in rows)


def test_generate_sampler_failure_accounts_remaining(runtime,monkeypatch):
    def fail(*a,**kw):raise RuntimeError('fake device failure')
    monkeypatch.setattr(runtime.sampling,'sample_tokens',fail)
    with pytest.raises(RuntimeError,match='fake device failure'):e.generate(runtime.args)
    rows=[json.loads(s) for s in (runtime.args.output/'rollouts.jsonl').read_text().splitlines()]
    assert rows[0]['status']=='worker_error' and all(r['status']=='unattempted' for r in rows[1:])
    assessed=e.verify(verify_args(runtime))
    assert assessed['unmeasured']==32 and assessed['measured_rejections']==0
    assert assessed['generation_complete'] is False and runtime.events==['controls']


def test_generate_exact_restore_required(runtime,monkeypatch):
    with torch.no_grad():runtime.net.weight.add_(1)
    with pytest.raises(ValueError,match='Exact child restore'):e.generate(runtime.args)
    assert not (runtime.args.output/'summary.json').exists()


def test_generate_frozen_weights_checked(runtime,monkeypatch):
    original=runtime.sampling.sample_tokens
    def change(*a,**kw):
        with torch.no_grad():runtime.net.weight.add_(1)
        return original(*a,**kw)
    monkeypatch.setattr(runtime.sampling,'sample_tokens',change)
    with pytest.raises(ValueError,match='weights changed'):e.generate(runtime.args)
    assert not (runtime.args.output/'summary.json').exists()


def test_generate_identity_drift_rejected(runtime,monkeypatch):
    monkeypatch.setattr(e,'source_hashes',lambda:{'changed':'yes'})
    with pytest.raises(ValueError,match='Frozen inputs/source'):e.generate(runtime.args)
    assert not (runtime.args.output/'summary.json').exists()


@pytest.mark.parametrize('field,value',[('checkpoint_sha256',p.POLICY_SHA),('requested_samples',31),
    ('accounted_samples',31),('optimizer_updates',1),('cuda_peak_reserved',e.worker.MEMORY_LIMIT+1),
    ('cuda_peak_allocated',None),('complete','yes')])
def test_verify_summary_provenance_rejected(runtime,field,value):
    e.generate(runtime.args);path=runtime.args.output/'summary.json'
    summary=json.loads(path.read_text());summary[field]=value;e.dump(path,summary)
    with pytest.raises(ValueError):e.verify(verify_args(runtime))
    assert runtime.events==[]


def test_verify_controls_required_before_any_checks(runtime,monkeypatch):
    e.generate(runtime.args)
    def fail(*a):raise ValueError('raw controls invalid')
    monkeypatch.setattr(runtime.bridge,'admit_controls',fail)
    with pytest.raises(ValueError,match='raw controls'):e.verify(verify_args(runtime))
    assert runtime.events==[]


def test_verify_raw_audit_required(runtime,monkeypatch):
    e.generate(runtime.args)
    def fail(*a):raise ValueError('raw SANY changed')
    monkeypatch.setattr(runtime.bridge,'audit_check',fail)
    args=verify_args(runtime)
    with pytest.raises(ValueError,match='raw SANY'):e.verify(args)
    assert not (args.output/'summary.json').exists()


def test_verify_runtime_drift_rejected(runtime,monkeypatch):
    e.generate(runtime.args);identities=iter([{'version':1},{'version':2}])
    monkeypatch.setattr(runtime.bridge,'identity',lambda *a:next(identities))
    args=verify_args(runtime)
    with pytest.raises(ValueError,match='runtime changed'):e.verify(args)
    assert not (args.output/'summary.json').exists()


def test_verify_exact_decode_required(runtime,monkeypatch):
    e.generate(runtime.args)
    monkeypatch.setattr(runtime.decoder,'decode_reply',lambda *a:'changed')
    with pytest.raises(ValueError,match='output decoding'):e.verify(verify_args(runtime))
    assert runtime.events==['controls']


def test_verify_false_unknown_not_conflated(runtime,monkeypatch):
    e.generate(runtime.args)
    verdicts=iter([dict(status='model_sany_reject',reward=0),dict(status='unmeasured_infrastructure',reward=None)]+
        [dict(status='pass',reward=1)]*30)
    monkeypatch.setattr(runtime.bridge,'check',lambda *a,**kw:next(verdicts))
    result=e.verify(verify_args(runtime))
    assert (result['sany_passes'],result['measured_rejections'],result['unmeasured'])==(30,1,1)
    assert runtime.events.count('audit')==32


def test_generate_memory_guard_preserves_output_and_stops(runtime,monkeypatch):
    monkeypatch.setattr(torch.cuda,'max_memory_reserved',lambda:e.worker.MEMORY_LIMIT+1)
    with pytest.raises(RuntimeError,match='memory ceiling'):e.generate(runtime.args)
    rows=[json.loads(s) for s in (runtime.args.output/'rollouts.jsonl').read_text().splitlines()]
    assert rows[0]['status']=='generated' and all(r['status']=='unattempted' for r in rows[1:])
    with pytest.raises(ValueError,match='memory ceiling'):e.verify(verify_args(runtime))


def test_verify_admission_encoding_changed(runtime):
    e.generate(runtime.args)
    path=runtime.args.output/'config.json';config=json.loads(path.read_text())
    config['encodings'][0]['input_tokens']=99;e.dump(path,config)
    summary_path=runtime.args.output/'summary.json';summary=json.loads(summary_path.read_text())
    summary['config_sha256']=e.file_sha(path);e.dump(summary_path,summary)
    with pytest.raises(ValueError,match='admission'):e.verify(verify_args(runtime))
    assert runtime.events==[]


def test_generate_frozen_admission_mismatch_before_model_load(runtime,monkeypatch):
    record=json.loads(runtime.args.admission.read_text());record['seed']+=1
    e.dump(runtime.args.admission,record)
    def forbidden(*a):raise AssertionError('CUDA model loaded before admission comparison')
    monkeypatch.setattr(runtime.train,'load_policy',forbidden)
    with pytest.raises(ValueError,match='differs from frozen full CPU admission'):e.generate(runtime.args)
    assert not runtime.args.output.exists()


def test_generate_admission_required_before_model_load(runtime,monkeypatch):
    runtime.args.admission=None
    def forbidden(*a):raise AssertionError('CUDA model loaded without admission')
    monkeypatch.setattr(runtime.train,'load_policy',forbidden)
    with pytest.raises(ValueError,match='admission file required'):e.generate(runtime.args)
    assert not runtime.args.output.exists()


def test_generate_admission_saved_exactly(runtime):
    frozen=runtime.args.admission.read_bytes()
    e.generate(runtime.args)
    assert (runtime.args.output/'admission.json').read_bytes()==frozen
    config=json.loads((runtime.args.output/'config.json').read_text())
    assert config['admission_sha256']==p.sha(frozen)
    assert e.verify(verify_args(runtime))['sany_passes']==32


def test_generate_admission_drift_detected(runtime,monkeypatch):
    original=runtime.sampling.sample_tokens
    def change(*a,**kw):
        runtime.args.admission.write_bytes(b'{}')
        return original(*a,**kw)
    monkeypatch.setattr(runtime.sampling,'sample_tokens',change)
    with pytest.raises(ValueError,match='Frozen inputs/source'):e.generate(runtime.args)
    assert not (runtime.args.output/'summary.json').exists()


@pytest.mark.parametrize('entry', ['admit','verify','generate'])
def test_cpu_environment_overrides_inherited64_before_numerical_import(entry,monkeypatch):
    import builtins
    for name in e.CPU_ENV:monkeypatch.setenv(name,'64')
    original=builtins.__import__
    class ObservedImport(Exception):pass
    def inspect(name,*a,**kw):
        if name in ('torch','transformers','numpy'):
            assert all(e.os.environ[k]=='4' for k in e.CPU_ENV)
            raise ObservedImport(name)
        return original(name,*a,**kw)
    monkeypatch.setattr(builtins,'__import__',inspect)
    with pytest.raises(ObservedImport):getattr(e,entry)(SimpleNamespace())


def test_cpu_runtime_sets_and_attests_four_threads(monkeypatch):
    for name in e.CPU_ENV:monkeypatch.setenv(name,'64')
    calls=[]
    monkeypatch.setattr(torch,'set_num_threads',lambda n:calls.append(n))
    monkeypatch.setattr(torch,'get_num_threads',lambda:4)
    assert e.cpu_runtime()==e.CPU_PROFILE and calls==[4]
    monkeypatch.setenv('OPENBLAS_NUM_THREADS','64')
    with pytest.raises(ValueError,match='four-thread CPU runtime'):e.check_cpu_runtime(torch)


def test_cpu_thread_profile_mismatch_rejected_locally(runtime):
    e.generate(runtime.args)
    admission_path=runtime.args.output/'admission.json'
    admission=json.loads(admission_path.read_text())
    admission['cpu_thread_profile']['environment']['OPENBLAS_NUM_THREADS']='64'
    e.dump(admission_path,admission)
    config_path=runtime.args.output/'config.json';config=json.loads(config_path.read_text())
    config['cpu_thread_profile']=admission['cpu_thread_profile']
    config['admission_sha256']=e.file_sha(admission_path);e.dump(config_path,config)
    summary_path=runtime.args.output/'summary.json';summary=json.loads(summary_path.read_text())
    summary['config_sha256']=e.file_sha(config_path);e.dump(summary_path,summary)
    with pytest.raises(ValueError,match='generation provenance'):e.verify(verify_args(runtime))
