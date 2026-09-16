import copy
from types import SimpleNamespace
import pytest
from tools import proof_cuda_train as t


class Tokenizer:
    eos_token_id=3
    def apply_chat_template(self,messages,tokenize=False,add_generation_prompt=False):
        prefix='<user>'+messages[0]['content']+'</user><assistant>'
        return prefix if add_generation_prompt else prefix+messages[1]['content']+'\x03\n'
    def __call__(self,text,**kwargs):
        assert kwargs == dict(add_special_tokens=False, truncation=False)
        return {'input_ids':[ord(c) for c in text]}


def test_rendered_bos_is_not_added_again_and_training_matches_inference():
    from tools.proof_cuda_eval import encode_prompt
    class BosTokenizer(Tokenizer):
        def apply_chat_template(self, *args, **kwargs):
            return '\x01'+super().apply_chat_template(*args, **kwargs)
        def __call__(self,text,add_special_tokens=True,truncation=False):
            return {'input_ids':([1] if add_special_tokens else [])+[ord(c) for c in text]}
    tokenizer=BosTokenizer(); row=packet()['rows'][0]
    training=t.encode_row(tokenizer,row)
    inference=encode_prompt(tokenizer,row)
    assert training['input_ids'][:training['prompt_tokens']] == inference['input_token_ids']
    assert training['input_ids'][:2] == [1,ord('<')]


def packet():
    rows=[]
    for i in range(50):
        rows.append(dict(id=str(i),split='train',source_family='family'+str(i%3),
            source_sha256='a'*64,assembled_sha256='b'*64,prompt='proof hole',
            prompt_sha256=t.sha(b'proof hole'),response='BY SMT',response_sha256=t.sha(b'BY SMT')))
    return dict(algorithm=t.ALGORITHM,split='train',evaluation_responses_exported=False,
        manifest_sha256='c'*64,train_ids=[r['id'] for r in rows],rows=rows,
        evidence=dict(populations={k:[str(i) for i in range(n)] for k,n in
            [('original18',18),('official119',119),('official30',30)]},threshold=.65,
            manifest_sha256='c'*64,controls_sha256='d'*64,original18_audit_sha256='e'*64,
            strict_controls_verified=True,max_jaccard=.4,canonical_matches=0))


def hierarchical_packet():
    import json
    p=packet(); p['rows']=p['rows'][:17]; p['train_ids']=p['train_ids'][:17]
    for row in p['rows'][6:]:
        row['response']='\n<1> QED BY SMT';row['response_sha256']=t.sha(row['response'].encode())
    p.update(schema_version=1,packet_kind='frozen17_hierarchical_repair_spans',training_ready=True,
             manifest_sha256=t.HIERARCHICAL_MANIFEST,
             task_shape=dict(train_spans=17,leaf_spans=6,hierarchical_spans=11,source_families=3,
                             independent_theorem_count_claimed=False,whole_target_generation=False))
    e=p['evidence'];e['manifest_sha256']=p['manifest_sha256']
    e['populations']['development']=['dev'+str(i) for i in range(4)]
    e.update(original18_eval_sha256='a'*64,original18_reference_blob_sha256='b'*64,
             original18_reference_text_exported=False)
    identity=dict(complete=True,manifest_sha256=p['manifest_sha256'],controls_sha256=e['controls_sha256'],
                  requested_controls=34,completed_controls=34,before={'fixture':True},after={'fixture':True})
    e['verifier_identity']=identity;e['verifier_identity_sha256']=t.sha((json.dumps(identity,indent=2)+'\n').encode())
    e['controls']=[dict(id=r['id'],proved=1,total=1,assembled_sha256=r['assembled_sha256'],
                        candidate_sha256=r['assembled_sha256'],command=['tlapm','--strict','--nofp']) for r in p['rows']]
    return p


def test_exact_fresh_hierarchical_packet_has_separate_population_contract():
    assert len(t.validate_packet(hierarchical_packet()))==17
    assert len(t.validate_packet(packet()))==50


def test_broader_packet_routes_only_explicit_contract(monkeypatch):
    import sys
    import types
    seen = []
    rows = [{'id': 'checked-broader-row'}]
    def validate(value):
        seen.append(value)
        if value.get('training_ready') is not True:
            raise ValueError('Broader packet not admitted')
        return rows
    monkeypatch.setitem(sys.modules, 'tools.proof_broader_packet',
                        types.SimpleNamespace(validate_training_packet=validate))
    p = {'packet_kind': 'frozen32_broader_whole_target_proofs', 'training_ready': True}
    assert t.validate_packet(p) is rows and seen == [p]
    with pytest.raises(ValueError, match='not admitted'):
        t.validate_packet(dict(p, training_ready=False))


def test_whole_proof_cache_policy_releases_only_unused_cuda_cache(monkeypatch):
    import torch
    calls=[]
    monkeypatch.setattr(torch.cuda,'empty_cache',lambda:calls.append('clear'))
    t.release_unused_cache('cpu',False)
    t.release_unused_cache('cuda',False)
    assert calls==[]
    with pytest.raises(ValueError):t.release_unused_cache('cpu',True)
    t.release_unused_cache('cuda',True)
    assert calls==['clear']


@pytest.mark.parametrize('fault',['historical','identity','controls','population','manifest','shape','heldout'])
def test_hierarchical_packet_cannot_bypass_controls_or_frozen_population(fault):
    p=hierarchical_packet()
    if fault=='historical':p['training_ready']=False
    elif fault=='identity':p['evidence']['verifier_identity']['completed_controls']=33
    elif fault=='controls':p['evidence']['controls'][0]['candidate_sha256']='c'*64
    elif fault=='population':p['rows'].pop()
    elif fault=='manifest':p['manifest_sha256']='a'*64
    elif fault=='shape':p['task_shape']['whole_target_generation']=True
    elif fault=='heldout':p['evidence']['populations']['development'][0]=p['train_ids'][0]
    with pytest.raises(ValueError):t.validate_packet(p)


def test_response_only_labels_and_eos():
    row=packet()['rows'][0];e=t.encode_row(Tokenizer(),row)
    n=e['prompt_tokens']
    assert e['labels'][:n]==[-100]*n
    assert e['labels'][n:]==[ord(c) for c in 'BY SMT\x03']
    assert e['labels'][1:][n-1]==ord('B')
    assert e['input_ids'][-1]==3


def test_no_truncation_or_changed_boundary():
    with pytest.raises(ValueError,match='truncation'):
        t.encode_row(Tokenizer(),packet()['rows'][0],5)
    class Broken(Tokenizer):
        def apply_chat_template(self,messages,**kwargs):
            return super().apply_chat_template(messages,**kwargs)+('!' if len(messages)==1 else '')
    with pytest.raises(ValueError,match='boundary'):
        t.encode_row(Broken(),packet()['rows'][0])


def test_shuffled_full_population_before_repeat():
    s=t.schedule(50,100,123)
    assert sorted(s[:50])==sorted(s[50:])==list(range(50))
    assert s==t.schedule(50,100,123) and s!=t.schedule(50,100,124)
    with pytest.raises(ValueError):t.schedule(50,101,1)


def test_valid_packet_is_sft_only():
    p=packet();assert len(t.validate_packet(p))==50
    assert 'SFT' in p['algorithm'] and 'no RL' in p['algorithm']


@pytest.mark.parametrize('split',['development','original18_test','official_test','test'])
def test_eval_rows_never_accepted(split):
    p=packet();p['rows'][0]['split']=split
    with pytest.raises(ValueError,match='split'):t.validate_packet(p)


@pytest.mark.parametrize('mutation',['answer','unknown_field','missing18','small30','bad_evidence','overlap','nan'])
def test_packet_provenance_and_exclusions_fail_closed(mutation):
    p=packet()
    if mutation=='answer':p['rows'][0]['response']='changed'
    elif mutation=='unknown_field':p['rows'][0]['development_response']='secret'
    elif mutation=='missing18':del p['evidence']['populations']['original18']
    elif mutation=='small30':p['evidence']['populations']['official30'].pop()
    elif mutation=='bad_evidence':p['evidence']['manifest_sha256']='f'*64
    elif mutation=='overlap':p['evidence']['max_jaccard']=.65
    elif mutation=='nan':p['evidence']['max_jaccard']=float('nan')
    with pytest.raises(ValueError):t.validate_packet(p)


def tiny_model():
    import torch
    class Tiny(torch.nn.Module):
        def __init__(self):
            super().__init__();self.embedding=torch.nn.Embedding(12,8)
            self.model=torch.nn.Module();self.model.layers=torch.nn.ModuleList([
                torch.nn.Linear(8,8),torch.nn.Linear(8,8)])
            self.head=torch.nn.Linear(8,12,bias=False)
        def forward(self,input_ids,labels=None,use_cache=False):
            h=self.embedding(input_ids)
            for layer in self.model.layers:h=torch.tanh(layer(h))
            logits=self.head(h)
            loss=None if labels is None else torch.nn.functional.cross_entropy(
                logits[:,:-1].float().reshape(-1,12),labels[:,1:].reshape(-1),ignore_index=-100)
            return SimpleNamespace(logits=logits,loss=loss)
    return Tiny().to(dtype=torch.bfloat16)


def test_cpu_mixed_dtype_train_save_restore_and_logits(tmp_path):
    torch=pytest.importorskip('torch');torch.manual_seed(5)
    net=tiny_model();selected=t.select_final_layer(net,train=False)
    assert not any(p.requires_grad for p in net.parameters())
    assert net.embedding.weight.dtype==torch.bfloat16
    assert all(p.dtype==torch.float32 for p in selected.values())
    frozen=net.embedding.weight.detach().clone()
    selected=t.select_final_layer(net,train=True)
    initial={n:p.detach().clone() for n,p in selected.items()}
    encoded=[dict(input_ids=[1,2,3,4],labels=[-100,-100,3,4],response_tokens=2)]*2
    records=[];optimizer,metrics,indices=t.train_steps(net,selected,encoded,[{'id':'a'},{'id':'b'}],
        4,7,1e-3,30,'cpu',records.append)
    config=dict(model_files={'weights.safetensors':'hash'},dtype_profile=t.PROFILE,algorithm=t.ALGORITHM)
    path=tmp_path/'checkpoint.pt'
    result=t.save_reload(net,selected,optimizer,initial,config,metrics,[1,2,3,4],path,'cpu')
    assert result['reload_tensors_exact'] and result['reload_logits_exact']
    assert result['parameter_delta_l2']>0 and len(records)==4
    assert torch.equal(frozen,net.embedding.weight)
    saved=torch.load(path,map_location='cpu',weights_only=False)
    assert saved['torch_rng_state'] is not None and saved['python_rng_state'] is not None
    assert all(v.dtype==torch.float32 for state in saved['optimizer']['state'].values()
               for k,v in state.items() if k in ('exp_avg','exp_avg_sq'))
    t.restore_policy(net,saved,config['model_files'])
    assert not any(p.requires_grad for p in net.parameters())
    with pytest.raises(ValueError,match='base model'):
        t.restore_policy(net,saved,{'wrong':'hash'})
    bad=copy.deepcopy(saved);name=next(iter(bad['trainable_state']))
    bad['trainable_state'][name]=bad['trainable_state'][name].bfloat16()
    with pytest.raises(ValueError,match='dtype'):
        t.restore_policy(net,bad,config['model_files'])


def test_finite_lr_and_time_guards():
    pytest.importorskip('torch');net=tiny_model();selected=t.select_final_layer(net,train=True)
    with pytest.raises(ValueError,match='finite'):
        t.train_steps(net,selected,[],[],1,1,float('nan'),1,'cpu',lambda row:None)


def test_actual_prepare_validation_no_model_or_verifier(tmp_path):
    base=t.ROOT/'results/runs/proof-leaf-manifest-20260905-v1/defs-complete'
    audit=t.ROOT/'results/runs/proof-original18-manifest-20260905-v1/decontamination.json'
    if not (base/'manifest.json').exists() or not audit.exists():
        pytest.skip('Local verified artifacts unavailable')
    p=t.prepare(base/'manifest.json',base/'controls.json',audit,tmp_path/'prepared')
    assert len(p['rows'])==50 and all(r['split']=='train' for r in p['rows'])
    assert p['evidence']['strict_controls_verified'] and not p['evaluation_responses_exported']


def test_supervisor_deadline_and_exit_owned_without_model(tmp_path,monkeypatch):
    seen=[]
    class FakeProcess:
        def __init__(self,command,**kwargs):seen.append((command,kwargs));self.pid=123456
        def wait(self,timeout):seen.append(timeout);return 7
    monkeypatch.setattr(t.subprocess,'Popen',FakeProcess)
    args=SimpleNamespace(seconds=600,steps=100,output=tmp_path/'run')
    assert t.supervise(args,['--seed','4'])==7
    assert seen[0][0][2]=='_worker' and seen[0][1]['start_new_session'] is True
    assert seen[1]==600


def test_supervisor_timeout_marks_incomplete(tmp_path,monkeypatch):
    args=SimpleNamespace(seconds=600,steps=100,output=tmp_path/'run');signals=[]
    class FakeProcess:
        def __init__(self,*a,**k):self.pid=123456;self.calls=0;args.output.mkdir()
        def wait(self,timeout):
            self.calls+=1
            if self.calls==1:raise t.subprocess.TimeoutExpired('fake',timeout)
            return -15
    monkeypatch.setattr(t.subprocess,'Popen',FakeProcess)
    monkeypatch.setattr(t.os,'killpg',lambda pid,sig:signals.append((pid,sig)))
    assert t.supervise(args,[])==124
    assert signals==[(123456,t.signal.SIGTERM)]
    assert (args.output/'timeout.json').exists()
