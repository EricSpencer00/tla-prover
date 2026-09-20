import json
from pathlib import Path

import pytest

from tools import proof_token_rl_packet as p

ROOT=Path(__file__).resolve().parents[1]


@pytest.fixture
def packet():
    raw=(ROOT/'results/runs/proof-broader-train-prepared-20260905-v1/prompts.json').read_bytes()
    return p.prepare_requests(raw,reward_stage='sany_partial')


def row(request,tokens=None,finish='eos'):
    tokens=[p.EOS_IDS[-1]] if tokens is None else tokens
    return dict(**request,request_sha256=p.digest(request),status='generation_time_limit' if finish=='time_limit' else 'generated',
        input_token_ids=[1,2],input_token_ids_sha256=p.digest([1,2]),input_tokens=2,
        rendered_prompt='prompt',rendered_prompt_sha256=p.sha(b'prompt'),token_ids=tokens,
        token_ids_sha256=p.digest(tokens),output_tokens=len(tokens),raw_reply='',raw_reply_sha256=p.sha(b''),
        selected_token_logprobs=[-.5]*len(tokens),sequence_logprob=-.5*len(tokens),
        token_entropies=[1.]*len(tokens),finish_reason=finish,eos_reached=bool(tokens and tokens[-1] in p.EOS_IDS),
        hit_token_limit=len(tokens)==3072,deadline_exceeded=finish=='time_limit',temperature=1.,
        distribution='full_vocabulary_categorical',elapsed_seconds=1.)


def test_exact_preregistered_packet_and_32_keys(packet):
    requests=p.validate_requests(packet)
    assert len(requests)==32 and len({r['sample_id'] for r in requests})==32
    assert packet['selection_indices']==[0,1,2,6,13,14,16,29]
    assert all(t['split']=='train' for t in packet['tasks'])
    assert all(set(t)=={'id','split','prompt','prompt_sha256'} for t in packet['tasks'])
    raw=json.dumps(packet).encode()
    assert p.load_requests(raw,p.sha(raw))==packet


def test_original_bytes_sha_is_required():
    with pytest.raises(ValueError):p.prepare_requests(b'{}',reward_stage='sany_partial')


def test_request_file_requires_external_hash(packet):
    raw=json.dumps(packet).encode()
    with pytest.raises(ValueError):p.load_requests(raw,'a'*64)


def test_full_accounting_never_claims_decode_or_proof(packet):
    rows=[row(r) for r in packet['requests']]
    result=p.validate_rollouts(packet,rows)
    assert result['requested_samples']==result['eos_complete_samples']==32
    assert not result['tokenizer_decode_verified'] and not result['proof_rewards_assigned']
    assert not result['cryptographic_signature_verified']


def test_explicit_partial_prefix_keeps_denominator(packet):
    rows=[row(r) for r in packet['requests'][:2]]
    with pytest.raises(ValueError):p.validate_rollouts(packet,rows)
    result=p.validate_rollouts(packet,rows,complete_accounting=False)
    assert result['requested_samples']==32 and len(result['missing_sample_ids'])==30


def test_eos_only_valid(packet):
    request=packet['requests'][0]
    assert p.validate_rollout(request,row(request))['requires_verifier']


@pytest.mark.parametrize('tokens',[[],[3,4],[p.EOS_IDS[-1]]])
def test_time_limit_retains_sampled_tokens_but_unmeasured(packet,tokens):
    request=packet['requests'][0]
    disposition=p.validate_rollout(request,row(request,tokens,'time_limit'))
    assert not disposition['measured_generation'] and not disposition['requires_verifier']


def test_token_limit_excluded_from_eos_rl_group(packet):
    request=packet['requests'][0]
    assert not p.validate_rollout(request,row(request,[3]*3072,'token_limit'))['measured_generation']


@pytest.mark.parametrize('field,value',[
    ('policy_sha256','a'*64),('prompt_sha256','a'*64),('task_id','dev'),('attempt',2),
    ('request_sha256','a'*64),('raw_reply','changed'),('input_tokens',3),
    ('selected_token_logprobs',[]),('selected_token_logprobs',[float('nan')]),
    ('selected_token_logprobs',[.1]),('token_entropies',[-1]),('sequence_logprob',7),
    ('eos_reached',False),('deadline_exceeded',True),('temperature',.8),
])
def test_rollout_mutations_rejected(packet,field,value):
    request=packet['requests'][0];output=row(request);output[field]=value
    with pytest.raises(ValueError):p.validate_rollout(request,output)


def test_unknown_payload_keys_cannot_smuggle_rewards(packet):
    request=packet['requests'][0];output=row(request);output['reward']=1
    with pytest.raises(ValueError):p.validate_rollout(request,output)


def test_unattempted_row_is_explicit_unmeasured(packet):
    request=packet['requests'][0]
    output=dict(**request,request_sha256=p.digest(request),status='unattempted',reason='batch_deadline')
    assert not p.validate_rollout(request,output)['measured_generation']


def test_reordered_rows_rejected(packet):
    rows=[row(r) for r in packet['requests']];rows[0],rows[1]=rows[1],rows[0]
    with pytest.raises(ValueError):p.validate_rollouts(packet,rows)


@pytest.mark.parametrize('mutation',['split','selection','budget','answer'])
def test_request_scope_cannot_change(packet,mutation):
    if mutation=='split':packet['tasks'][0]['split']='development'
    elif mutation=='selection':packet['selection_indices'][0]=3
    elif mutation=='budget':packet['budget']['group_size']=3
    else:packet['tasks'][0]['reference_fragment']='BY SMT'
    with pytest.raises(ValueError):p.validate_requests(packet)


def test_reward_stage_is_bound_in_each_request(packet):
    original=packet['requests'][0];changed=dict(original,reward_stage='strict_tlaps')
    assert p.digest(original)!=p.digest(changed)
    with pytest.raises(ValueError):p.validate_rollout(original,row(changed))
    packet['reward_stage']='strict_tlaps'
    with pytest.raises(ValueError):p.validate_requests(packet)
