import copy
import json
import sys
from types import SimpleNamespace

import pytest

from tools.proof_cuda_eval import (BUDGET, digest, encode_prompt, export_tasks, left_pad,
    merge_shards, sha, shard_tasks, trim_output, validate_export,
    validate_shard, validate_tokenization, decode_reply)


class Tokenizer:
    clean_up_tokenization_spaces = False
    def apply_chat_template(self, messages, **kwargs):
        return 'USER:'+messages[0]['content']+'\nASSISTANT:'

    def __call__(self,text,**kwargs):
        assert kwargs==dict(add_special_tokens=False,truncation=False)
        return {'input_ids':[ord(c) for c in text]}

    def decode(self,ids,skip_special_tokens=True,clean_up_tokenization_spaces=False):
        assert clean_up_tokenization_spaces is False
        return ''.join(chr(x) for x in ids)


def test_decoder_explicitly_preserves_legacy_configured_cleanup():
    from transformers.tokenization_utils_base import PreTrainedTokenizerBase
    tokenizer = Tokenizer()
    tokenizer.clean_up_tokenization_spaces = True
    tokenizer.clean_up_tokenization = lambda text: PreTrainedTokenizerBase.clean_up_tokenization(tokenizer, text)
    text = 'BY Foo .  \\* "can not"\n'
    assert decode_reply(tokenizer, list(map(ord, text))) == 'BY Foo.  \\* "can not"\n'


def test_decoder_does_not_force_cleanup_when_snapshot_disables_it():
    text = 'BY Foo .\n'
    assert decode_reply(Tokenizer(), list(map(ord, text))) == text


def fixture():
    rows=[dict(id=str(i),prompt='Prompt '+str(i),prompt_sha256=sha(('Prompt '+str(i)).encode())) for i in range(119)]
    data=dict(schema=1,split='official_test',requested_tasks=119,manifest_sha256='m',
        reference_fragments_exported=False,candidates_exported=False,tasks=rows,
        sources=[dict(id=t['id'],source_sha256='s',category='math',theorem_name='T') for t in rows])
    raw=json.dumps(data).encode();shards=[]
    for index in range(4):
        tasks=shard_tasks(rows,index)
        config=dict(**BUDGET,shard_index=index,requested_task_ids=[t['id'] for t in tasks],
            prompts_sha256=sha(raw),model_files={'weights.safetensors':'abc'},
            model_files_sha256=digest({'weights.safetensors':'abc'}),restore_exact=True,
            checkpoint_sha256=None,arm='base',implementation_sha256={'eval':'abc'})
        generations=[]
        for task in tasks:
            row=encode_prompt(Tokenizer(),task);tokens=[ord(x) for x in 'BY SMT']
            row.update(status='generated',token_ids=tokens,token_ids_sha256=digest(tokens),
                output_tokens=len(tokens),hit_token_limit=False,raw_reply='BY SMT',raw_reply_sha256=sha(b'BY SMT'))
            generations.append(row)
        summary=dict(unattempted_task_ids=[],termination='complete')
        shards.append((config,generations,summary))
    return raw,data,shards


def test_all119_export_and_four_strided_shards():
    raw,data,shards=fixture()
    assert len(validate_export(data))==119
    assert [len(s[1]) for s in shards]==[30,30,30,29]
    merged,_=merge_shards(raw,data,shards)
    assert len(merged)==119


def test_export_forbids_candidates_and_reference_answers():
    _,data,_=fixture();data['tasks'][0]['candidates']=['BY SMT']
    with pytest.raises(ValueError):validate_export(data)


def test_prepare_projects_only_prompt_and_source_allowlists(monkeypatch,tmp_path):
    _,data,_=fixture()
    tasks=[dict(**task,**{k:v for k,v in source.items() if k!='id'},
                candidates=['ForbiddenCandidate'],reference_fragment='ForbiddenReference',
                prefix='Source',suffix='End') for task,source in zip(data['tasks'],data['sources'])]
    monkeypatch.setitem(sys.modules,'tools.proof_official_rank',SimpleNamespace(freeze_tasks=lambda path:tasks))
    manifest=tmp_path/'manifest.json';manifest.write_text('{}')
    exported,_=export_tasks(manifest)
    validate_export(exported)
    assert 'Forbidden' not in json.dumps(exported)


def test_left_padding_and_exact_mask():
    rows=[dict(input_token_ids=[1,2],input_tokens=2),dict(input_token_ids=[3],input_tokens=1)]
    assert left_pad(rows,9)==dict(input_ids=[[1,2],[9,3]],attention_mask=[[1,1],[0,1]])


def test_no_truncation_context_overflow():
    task=dict(id='a',prompt='x'*8192,prompt_sha256=sha(('x'*8192).encode()))
    row=encode_prompt(Tokenizer(),task)
    assert row['status']=='context_overflow' and len(row['input_token_ids'])>8192


def test_eos_trimming_removes_only_batch_padding_after_first_eos():
    assert trim_output([5,6,2,2,2],{2})==[5,6,2]
    assert trim_output([5,6],{2})==[5,6]


@pytest.mark.parametrize('field,value', [('max_new_tokens',513),('max_tokens',4096),
    ('batch_size',1),('profile','bf16'),('seconds',1600),('batch_seconds',91),('restore_exact',False)])
def test_budget_profile_restore_mismatch_rejected(field,value):
    raw,data,shards=fixture();shards[0][0][field]=value
    with pytest.raises(ValueError):merge_shards(raw,data,shards)


def test_only_declared_suffix_may_be_unattempted():
    raw,data,shards=fixture();config,rows,summary=shards[0]
    removed=rows.pop();summary.update(termination='phase_timeout',unattempted_task_ids=[removed['id']])
    assert len(merge_shards(raw,data,shards)[0])==118
    rows.pop(2)
    with pytest.raises(ValueError):merge_shards(raw,data,shards)


def test_duplicate_shard_and_duplicate_row_rejected():
    raw,data,shards=fixture()
    with pytest.raises(ValueError):merge_shards(raw,data,[shards[0]]*4)
    shards[0][1][1]=copy.deepcopy(shards[0][1][0])
    with pytest.raises(ValueError):merge_shards(raw,data,shards)


def test_arm_identity_cannot_mix_base_and_checkpoint():
    raw,data,shards=fixture();shards[0][0].update(arm='checkpoint',checkpoint_sha256='child')
    with pytest.raises(ValueError):merge_shards(raw,data,shards)


@pytest.mark.parametrize('field,value',[('prompt_sha256','bad'),('raw_reply_sha256','bad'),
    ('input_token_ids_sha256','bad'),('token_ids_sha256','bad'),('output_tokens',512),('hit_token_limit',True)])
def test_hash_and_token_accounting_rejected(field,value):
    raw,data,shards=fixture();shards[0][1][0][field]=value
    with pytest.raises(ValueError):merge_shards(raw,data,shards)


def test_tokenizer_reconstruction_catches_self_consistent_forged_text():
    _,data,shards=fixture();row=shards[0][1][0]
    validate_tokenization(Tokenizer(),data['tasks'][0],row)
    row['raw_reply']='BY FALSE';row['raw_reply_sha256']=sha(b'BY FALSE')
    with pytest.raises(ValueError):validate_tokenization(Tokenizer(),data['tasks'][0],row)


def test_overflow_is_retained_in_full_denominator():
    raw,data,shards=fixture();row=shards[0][1][0]
    for key in ('token_ids','token_ids_sha256','output_tokens','hit_token_limit','raw_reply','raw_reply_sha256'):
        row.pop(key)
    row.update(status='context_overflow',input_token_ids=[1]*8000,input_tokens=8000,input_token_ids_sha256=digest([1]*8000))
    assert len(merge_shards(raw,data,shards)[0])==119


def test_invalid_shard_count_rejected():
    with pytest.raises(ValueError):shard_tasks([],0,3)


def test_chat_template_boundary_trim_keeps_exact_token_reconstruction():
    class TrimTokenizer(Tokenizer):
        def apply_chat_template(self,messages,**kwargs):
            return 'USER:'+messages[0]['content'].strip()+'\nASSISTANT:'
    _,data,shards=fixture()
    task=data['tasks'][0];task['prompt']='  '+task['prompt']+'\n\n'
    task['prompt_sha256']=sha(task['prompt'].encode())
    row=shards[0][1][0];row.update(encode_prompt(TrimTokenizer(),task));row['status']='generated'
    raw=json.dumps(data).encode()
    for config,_,_ in shards:config['prompts_sha256']=sha(raw)
    assert len(merge_shards(raw,data,shards)[0])==119
    validate_tokenization(TrimTokenizer(),task,row)
    row['rendered_prompt']=row['rendered_prompt'].replace('Prompt','Altered')
    row['rendered_prompt_sha256']=sha(row['rendered_prompt'].encode())
    with pytest.raises(ValueError,match='rendered prompt'):
        merge_shards(raw,data,shards)
