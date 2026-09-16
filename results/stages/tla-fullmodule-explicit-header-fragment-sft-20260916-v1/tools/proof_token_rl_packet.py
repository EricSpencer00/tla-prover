"""Stdlib-only TRAIN8 rollout request/response contracts for a one-update cycle.

Hashes bind bytes, not signatures, tokenizer correctness, theorem correctness
or policy authenticity. The local reward bridge must independently reconstruct
tokenization/decoding and attest frozen model/verifier/source provenance.
"""
import hashlib
import json
import math

BROADER_SHA='57717721f61a96bdc99b17c77601f4d4f208f1b6b852dfcb8bb854e6de340bd0'
POLICY_SHA='769115a0722f947efd1247bd66b6764ab82ba531671eaefab9e27be219d7aefa'
INDICES=[0,1,2,6,13,14,16,29]
EOS_IDS=[128001,128008,128009]
BUDGET=dict(temperature=1.0,max_new_tokens=3072,max_context=8192,group_size=4,
            requested_groups=8,requested_samples=32,global_batch_seconds=1500,
            distribution='full_vocabulary_categorical',top_k=0,top_p=1.0,
            forced_eos=False,repair_attempts=0,max_optimizer_updates=1)


def sha(raw):return hashlib.sha256(raw).hexdigest()


def canonical_bytes(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


def digest(value):return sha(canonical_bytes(value))


def _hash(value):
    return isinstance(value,str) and len(value)==64 and all(c in '0123456789abcdef' for c in value)


def request_keys(tasks,reward_stage):
    return [dict(sample_id=f'{t["id"]}:sample{attempt}',task_id=t['id'],attempt=attempt,
                 split='train',prompt_sha256=t['prompt_sha256'],policy_sha256=POLICY_SHA,reward_stage=reward_stage)
            for t in tasks for attempt in range(4)]


def prepare_requests(broader_raw,*,reward_stage):
    from tools.proof_broader_packet import validate_export
    if not isinstance(broader_raw,bytes) or sha(broader_raw)!=BROADER_SHA:
        raise ValueError('Exact immutable broader prompt bytes required')
    if reward_stage not in ('sany_partial','strict_tlaps'):
        raise ValueError('Explicit externally preregistered reward stage required')
    rows=validate_export(json.loads(broader_raw))
    train=[r for r in rows if r['split']=='train']
    if len(train)!=32:raise ValueError('Full original32 TRAIN required')
    selected=[{k:train[i][k] for k in ('id','split','prompt','prompt_sha256')} for i in INDICES]
    return dict(schema=1,kind='frozen_train8_token_rl_requests',broader_prompts_sha256=BROADER_SHA,
                policy_sha256=POLICY_SHA,selection_indices=INDICES[:],budget=dict(BUDGET),eos_token_ids=EOS_IDS[:],
                tasks=selected,requests=request_keys(selected,reward_stage),training_split_only=True,
                reward_stage=reward_stage,
                reference_answers_exported=False,candidates_exported=False,reward_labels_exported=False)


def validate_requests(packet):
    from tools.proof_broader_packet import TRAIN_IDS
    fields={'schema','kind','broader_prompts_sha256','policy_sha256','selection_indices','budget','eos_token_ids',
            'tasks','requests','training_split_only','reference_answers_exported','candidates_exported','reward_labels_exported','reward_stage'}
    if (not isinstance(packet,dict) or set(packet)!=fields or type(packet['schema']) is not int or packet['schema']!=1 or
        packet['kind']!='frozen_train8_token_rl_requests' or packet['broader_prompts_sha256']!=BROADER_SHA or
        packet['policy_sha256']!=POLICY_SHA or packet['selection_indices']!=INDICES or
        any(type(i) is not int for i in packet['selection_indices']) or canonical_bytes(packet['budget'])!=canonical_bytes(BUDGET) or
        packet['eos_token_ids']!=EOS_IDS or packet['training_split_only'] is not True or
        packet['reward_stage'] not in ('sany_partial','strict_tlaps') or
        any(packet[k] is not False for k in ('reference_answers_exported','candidates_exported','reward_labels_exported'))):
        raise ValueError('Frozen TRAIN8 request contract required')
    tasks=packet['tasks']
    if not isinstance(tasks,list) or len(tasks)!=8 or [t.get('id') for t in tasks]!=[TRAIN_IDS[i] for i in INDICES]:
        raise ValueError('Exact preregistered TRAIN8 population required')
    for task in tasks:
        if (set(task)!={'id','split','prompt','prompt_sha256'} or task['split']!='train' or
            not isinstance(task['prompt'],str) or not task['prompt'] or sha(task['prompt'].encode())!=task['prompt_sha256']):
            raise ValueError('Reference-free exact TRAIN prompt fields required')
    if canonical_bytes(packet['requests'])!=canonical_bytes(request_keys(tasks,packet['reward_stage'])):
        raise ValueError('Exact32 ordered request keys required')
    return packet['requests']


def load_requests(raw,expected_sha256,*,broader_raw=None):
    if not _hash(expected_sha256) or not isinstance(raw,bytes) or sha(raw)!=expected_sha256:
        raise ValueError('Explicit expected request file hash required')
    packet=json.loads(raw);validate_requests(packet)
    if broader_raw is not None and packet!=prepare_requests(broader_raw,reward_stage=packet['reward_stage']):
        raise ValueError('Requests differ from exact original broader prompts')
    return packet


def _tokens(value):
    return isinstance(value,list) and all(type(i) is int and i>=0 for i in value)


def validate_rollout(request,row):
    """Validate structure/hash consistency only; do not infer decoded correctness."""
    base={'sample_id','task_id','attempt','split','prompt_sha256','policy_sha256','reward_stage','request_sha256','status'}
    if (not isinstance(row,dict) or any(row.get(k)!=v for k,v in request.items()) or
        type(row.get('attempt')) is not int or row.get('request_sha256')!=digest(request)):
        raise ValueError('Rollout/request identity mismatch')
    if row.get('status') in ('unattempted','worker_error'):
        if set(row)!=base|{'reason'} or not isinstance(row['reason'],str) or not row['reason']:
            raise ValueError('Explicit unmeasured incomplete row required')
        return dict(measured_generation=False,requires_verifier=False,reason=row['status'])
    fields=base|{'input_token_ids','input_token_ids_sha256','input_tokens','rendered_prompt','rendered_prompt_sha256',
        'token_ids','token_ids_sha256','output_tokens','raw_reply','raw_reply_sha256','selected_token_logprobs',
        'sequence_logprob','token_entropies','finish_reason','eos_reached','hit_token_limit','deadline_exceeded',
        'temperature','distribution','elapsed_seconds'}
    if set(row)!=fields or row['status'] not in ('generated','generation_time_limit'):
        raise ValueError('Exact completed/partial rollout fields required')
    inputs=row['input_token_ids'];tokens=row['token_ids']
    if (not _tokens(inputs) or not 0<len(inputs)<=5120 or type(row['input_tokens']) is not int or row['input_tokens']!=len(inputs) or
        row['input_token_ids_sha256']!=digest(inputs) or not _tokens(tokens) or len(tokens)>3072 or
        type(row['output_tokens']) is not int or row['output_tokens']!=len(tokens) or row['token_ids_sha256']!=digest(tokens)):
        raise ValueError('Exact input/output token identities required')
    for field in ('raw_reply','rendered_prompt'):
        if not isinstance(row[field],str) or sha(row[field].encode())!=row[field+'_sha256']:
            raise ValueError('Raw text hash mismatch')
    logps=row['selected_token_logprobs'];entropy=row['token_entropies']
    if (not isinstance(logps,list) or not isinstance(entropy,list) or len(logps)!=len(tokens) or len(entropy)!=len(tokens)
        or any(type(v) not in (int,float) or not math.isfinite(v) or v>0 for v in logps)
        or any(type(v) not in (int,float) or not math.isfinite(v) or v<0 for v in entropy)
        or type(row['sequence_logprob']) not in (int,float) or not math.isfinite(row['sequence_logprob'])
        or not math.isclose(row['sequence_logprob'],sum(logps),abs_tol=1e-7,rel_tol=1e-7)):
        raise ValueError('Finite actual selected logprob/entropy lengths and sum required')
    if (type(row['temperature']) not in (int,float) or row['temperature']!=1.0 or row['distribution']!='full_vocabulary_categorical' or
        type(row['elapsed_seconds']) not in (int,float) or not math.isfinite(row['elapsed_seconds']) or row['elapsed_seconds']<0):
        raise ValueError('Sampling distribution/budget evidence required')
    reached=bool(tokens and tokens[-1] in EOS_IDS);cap=len(tokens)==3072
    if any(i in EOS_IDS for i in tokens[:-1]):raise ValueError('No tokens permitted after first EOS')
    if row['eos_reached'] is not reached or row['hit_token_limit'] is not cap:
        raise ValueError('Actual EOS/token cap flags mismatch')
    finish=row['finish_reason']
    if finish not in ('eos','token_limit','time_limit') or row['deadline_exceeded'] is not (finish=='time_limit'):
        raise ValueError('Explicit EOS/time/token-limit disposition required')
    if finish=='eos' and not reached or finish=='token_limit' and (not cap or reached):
        raise ValueError('Finish reason contradicts sampled tokens')
    if row['status']!=('generation_time_limit' if finish=='time_limit' else 'generated'):
        raise ValueError('Time-limited rows must remain unmeasured')
    # Token-capped generations are retained but excluded from this EOS-complete
    # policy-gradient experiment; no sampled termination token is invented.
    return dict(measured_generation=finish=='eos',requires_verifier=finish=='eos',reason=finish)


def validate_rollouts(packet,rows,*,complete_accounting=True):
    requests=validate_requests(packet)
    if not isinstance(rows,list) or len(rows)>32 or (complete_accounting and len(rows)!=32):
        raise ValueError('Full32 accounting required; incomplete prefix must be explicit')
    dispositions=[validate_rollout(request,row) for request,row in zip(requests,rows)]
    return dict(requested_samples=32,accounted_samples=len(rows),
                missing_sample_ids=[r['sample_id'] for r in requests[len(rows):]],
                eos_complete_samples=sum(r['measured_generation'] for r in dispositions),
                unmeasured_samples=32-sum(r['measured_generation'] for r in dispositions),
                dispositions=dispositions,tokenizer_decode_verified=False,
                proof_rewards_assigned=False,cryptographic_signature_verified=False)


def main():
    import argparse
    from pathlib import Path
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--broader-prompts',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--reward-stage',choices=('sany_partial','strict_tlaps'),required=True)
    args=parser.parse_args()
    packet=prepare_requests(args.broader_prompts.read_bytes(),reward_stage=args.reward_stage)
    validate_requests(packet)
    encoded=canonical_bytes(packet)+b'\n'
    args.output.mkdir(parents=True,exist_ok=False)
    (args.output/'requests.json').write_bytes(encoded)
    evidence=dict(requests_sha256=sha(encoded),broader_prompts_sha256=BROADER_SHA,
        expected_policy_sha256=POLICY_SHA,checkpoint_bytes_verified=False,
        requested_groups=8,requested_samples=32,reward_stage=args.reward_stage,
        tokenizer_decode_verified=False,proof_rewards_assigned=False,model_sampling=False,
        parameter_updates=0,implementation_sha256=sha(Path(__file__).read_bytes()),
        scope='Prepared TRAIN-only requests; not a running or completed learning cycle')
    (args.output/'evidence.json').write_bytes(canonical_bytes(evidence)+b'\n')
    print(json.dumps(evidence))


if __name__=='__main__':main()
