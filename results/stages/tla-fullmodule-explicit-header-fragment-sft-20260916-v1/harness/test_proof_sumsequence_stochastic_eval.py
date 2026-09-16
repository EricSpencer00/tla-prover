"""CPU contract/sampler mechanics only; no claims of GPU sampling or learning."""
from copy import deepcopy
import json
import math
from types import SimpleNamespace

import pytest
import torch

from tools import proof_sumsequence_stochastic_eval as module


@pytest.fixture
def evaluation():
    raw=(module.ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json').read_bytes()
    return module.derive_requests(raw,'parent')


def test_exact_existing8_both_arms(evaluation):
    raw=(module.ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json').read_bytes()
    child=module.derive_requests(raw,'child')
    assert evaluation['tasks']==child['tasks'] and len(evaluation['requests'])==32
    assert evaluation['selection_indices']==[0,1,2,6,13,14,16,29]
    assert all(r['reward_stage']=='strict_tlaps' for r in child['requests'])
    assert evaluation['policy_sha256']!=child['policy_sha256']
    assert child['training_authorized'] is False and child['reward_labels_exported'] is False


def test_modified_broader_bytes_rejected():
    with pytest.raises(ValueError):module.derive_requests(b'{}','parent')


def encoding():
    return dict(input_token_ids=[1],input_token_ids_sha256=module.digest([1]),input_tokens=1,
        rendered_prompt='prompt',rendered_prompt_sha256=module.sha(b'prompt'))


def sampled(request,finish='eos'):
    ids=[3,128009] if finish=='eos' else [3]*3072 if finish=='token_limit' else [3]
    lp=[-.5]*len(ids)
    return dict(request,request_sha256=module.digest(request),**encoding(),
        status='generation_time_limit' if finish=='time_limit' else 'generated',
        token_ids=ids,token_ids_sha256=module.digest(ids),output_tokens=len(ids),
        raw_reply='reply',raw_reply_sha256=module.sha(b'reply'),selected_token_logprobs=lp,
        sequence_logprob=sum(lp),token_entropies=[1.]*len(ids),finish_reason=finish,
        eos_reached=finish=='eos',deadline_exceeded=finish=='time_limit',hit_token_limit=finish=='token_limit',
        temperature=1.,distribution='full_vocabulary_categorical',elapsed_seconds=1.)


@pytest.fixture
def rows(evaluation):
    admission=dict(evaluation=evaluation,encodings=[encoding() for _ in range(8)])
    return admission,[sampled(r) for r in evaluation['requests']]


def test_full_unknown_accounting(evaluation):
    admission=dict(evaluation=evaluation,encodings=[encoding() for _ in range(8)])
    module.validate_rows(admission,[module.unknown(r) for r in evaluation['requests']])
    with pytest.raises(ValueError):module.validate_rows(admission,[])


@pytest.mark.parametrize('finish',['eos','token_limit','time_limit'])
def test_actual_termination_flags(rows,finish):
    a,values=rows;values[0]=sampled(a['evaluation']['requests'][0],finish)
    module.validate_rows(a,values)


@pytest.mark.parametrize('key,value', [('sequence_logprob',0),('token_entropies',[]),
    ('selected_token_logprobs',[float('nan')]),('policy_sha256','wrong'),('eos_reached',False),
    ('elapsed_seconds',181),('temperature',.5),('input_token_ids',[8])])
def test_sampling_tampering_rejected(rows,key,value):
    a,values=rows;values[0][key]=value
    with pytest.raises(ValueError):module.validate_rows(a,values)


def test_decode_checked_even_for_time_limit(rows,monkeypatch):
    a,values=rows;values[0]=sampled(a['evaluation']['requests'][0],'time_limit')
    monkeypatch.setattr(module.common,'decode_reply',lambda *a:'different')
    with pytest.raises(ValueError,match='decoding'):module.validate_rows(a,values,object())


def test_exact_rng_save_restore(tmp_path):
    generator=torch.Generator().manual_seed(20261002)
    path=tmp_path/'rng.pt';digest=module.save_rng(generator,path)
    expected=torch.rand(5,generator=generator)
    restored=torch.Generator();restored.set_state(torch.load(path,weights_only=True))
    assert torch.equal(expected,torch.rand(5,generator=restored)) and digest==module.train.file_sha(path)


def test_immutable_weights():
    p=torch.nn.Parameter(torch.ones(2),requires_grad=False)
    module.assert_unchanged({'p':p},{'p':p.detach().clone()})
    with pytest.raises(ValueError):module.assert_unchanged({'p':p},{'p':torch.zeros(2)})
    p.requires_grad_(True)
    with pytest.raises(ValueError):module.assert_unchanged({'p':p},{'p':p.detach().clone()})


class Tiny(torch.nn.Module):
    def forward(self,input_ids,**kwargs):
        logits=torch.tensor([-.5,.2,.4],device=input_ids.device).expand(1,input_ids.shape[1],3)
        return SimpleNamespace(logits=logits,past_key_values=('cache',))


def test_actual_sampler_same_seed_and_full_distribution():
    kwargs=dict(eos_token_ids=[2],max_new_tokens=30,max_context=50,seconds=1)
    a=module.sample_tokens(Tiny(),torch.tensor([1]),generator=torch.Generator().manual_seed(20261002),**kwargs)
    b=module.sample_tokens(Tiny(),torch.tensor([1]),generator=torch.Generator().manual_seed(20261002),**kwargs)
    assert a['token_ids']==b['token_ids'] and a['selected_token_logprobs']==b['selected_token_logprobs']
    expected=torch.tensor([-.5,.2,.4]).log_softmax(-1)
    assert all(math.isclose(lp,float(expected[t]),abs_tol=1e-7) for t,lp in zip(a['token_ids'],a['selected_token_logprobs']))
    assert a['distribution']=='full_vocabulary_categorical'


def test_device_mismatch_rejected():
    from tools.proof_token_rl_sampling import same_rng_device
    assert not same_rng_device('cpu','cuda:0')
    assert not same_rng_device('cuda:0','cuda:1')
    assert same_rng_device('cuda','cuda:0',current_cuda_index=0)


def test_complete_atomic_snapshot(tmp_path,evaluation):
    rows=[module.unknown(r) for r in evaluation['requests']]
    module.persist_rows(tmp_path,rows)
    assert len((tmp_path/'rollouts.jsonl').read_text().splitlines())==32
    assert not (tmp_path/'rollouts.pending').exists()


def test_generate_initializes32_before_failed_admission(tmp_path,evaluation,monkeypatch):
    args=SimpleNamespace(output=tmp_path/'output',broader_prompts=tmp_path/'prompts',
        model_path=tmp_path/'model',checkpoint=tmp_path/'child',admission=tmp_path/'admission.json',arm='parent')
    args.broader_prompts.write_bytes(b'fixture');args.checkpoint.write_bytes(b'checkpoint');args.model_path.mkdir()
    args.admission.write_text('{}')
    monkeypatch.setattr(module,'derive_requests',lambda *a:evaluation)
    monkeypatch.setattr(module,'admit',lambda a:{'different':True})
    with pytest.raises(ValueError,match='admission mismatch'):module.generate(args)
    rows=[json.loads(s) for s in (args.output/'rollouts.jsonl').read_text().splitlines()]
    assert len(rows)==32 and all(r['status']=='unattempted' for r in rows)
    assert not json.loads((args.output/'summary.json').read_text())['phase_complete']


def test_skipped_rows_not_generated_and_incomplete_results_unknown(evaluation):
    rows=[module.unknown(r) for r in evaluation['requests']]
    rows[0]=sampled(evaluation['requests'][0],'time_limit')
    rows[1]=sampled(evaluation['requests'][1],'token_limit')
    counts=module.accounting(rows)
    assert counts['generated_samples']==2 and counts['unknown_samples']==32
    assert len(counts['unattempted_sample_ids'])==30


def test_checkpoint_state_does_not_reuse_one_update_validator(monkeypatch):
    monkeypatch.setattr(module,'PARAMETERS',9)
    files={'frozen':'files'}
    saved=dict(config=dict(model_files=files,dtype_profile=module.train.PROFILE,actual_updates=80),
        trainable_state={n:torch.ones(1) for n in module.NAMES})
    assert module.checkpoint_state(saved,files)==module.digest(saved['config'])
    saved['trainable_state'][next(iter(module.NAMES))]=torch.tensor([float('nan')])
    with pytest.raises(ValueError):module.checkpoint_state(saved,files)


def test_cpu_environment_drift_rejected(monkeypatch):
    monkeypatch.setenv('OMP_NUM_THREADS','99')
    with pytest.raises(ValueError,match='CPU4'):module.cpu()


@pytest.fixture
def worker_result(tmp_path,rows):
    admission,values=rows
    module.persist_rows(tmp_path,values)
    rng={}
    for label in ('before','after'):
        path=tmp_path/('sampling_generator_'+label+'.pt')
        rng[label]=module.save_rng(torch.Generator().manual_seed(20261002),path)
    summary=dict(**module.accounting(values),phase_complete=True,identity_stable=True,
        failure=None,optimizer_updates=0,frozen_weights_verified=True,
        checkpoint_restored_exactly=True,checkpoint_sha256=module.POLICIES['parent'],
        verification_pending=True,generalization_claim=False,
        rollouts_sha256=module.train.file_sha(tmp_path/'rollouts.jsonl'),
        sampling_generator_sha256=rng)
    return summary,values,tmp_path


def test_worker_summary_matches_raw_evidence(worker_result):
    summary,values,path=worker_result
    module.validate_worker_summary(summary,values,path,'parent')


@pytest.mark.parametrize('key,value',[
    ('accounted_samples',31),('generated_samples',31),('unknown_samples',1),
    ('unattempted_sample_ids',['hidden']),('worker_error_sample_ids',['hidden']),
    ('phase_complete',False),('identity_stable',False),('failure','hidden failure'),
    ('optimizer_updates',1),('frozen_weights_verified',False),
    ('checkpoint_restored_exactly',False),('checkpoint_sha256','wrong'),
    ('verification_pending',False),('generalization_claim',True)])
def test_worker_summary_cannot_override_raw_evidence(worker_result,key,value):
    summary,values,path=worker_result;summary[key]=value
    with pytest.raises(ValueError,match='raw worker'):module.validate_worker_summary(summary,values,path,'parent')


def test_rng_file_changed_after_worker_rejected(worker_result):
    summary,values,path=worker_result
    (path/'sampling_generator_after.pt').write_bytes(b'changed')
    with pytest.raises(ValueError,match='RNG'):module.validate_worker_summary(summary,values,path,'parent')


@pytest.mark.parametrize('corruption',['malformed','missing','short','wrong_binding'])
def test_failure_accounting_keeps_all_unknown_on_invalid_ledger(tmp_path,evaluation,corruption):
    values=[module.unknown(r) for r in evaluation['requests']]
    if corruption=='short':values.pop()
    if corruption=='wrong_binding':values[0]['sample_id']='wrong'
    if corruption!='missing':module.persist_rows(tmp_path,values)
    if corruption=='malformed':(tmp_path/'rollouts.jsonl').write_text('{broken')
    result=module.failure_accounting(tmp_path,evaluation)
    assert result['accounting_unverified'] is True
    assert len(result['unknown_sample_ids'])==32
    assert result['unattempted_sample_ids'] is None


def test_failure_accounting_preserves_attempted_error(tmp_path,evaluation):
    values=[module.unknown(r) for r in evaluation['requests']]
    values[0]=module.unknown(evaluation['requests'][0],'failure',status='worker_error')
    module.persist_rows(tmp_path,values)
    result=module.failure_accounting(tmp_path,evaluation)
    assert result['worker_error_sample_ids']==[values[0]['sample_id']]
    assert len(result['unattempted_sample_ids'])==31
