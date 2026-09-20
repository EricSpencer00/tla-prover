import json

import pytest

from tools import proof_cuda_fresh_eval as ev
from tools.proof_fresh_packet import EVAL_IDS


@pytest.fixture
def run(monkeypatch):
    tasks=[dict(id=n,split='fresh_evaluation',prompt='a theorem '+n,
                prompt_sha256=ev.sha(('a theorem '+n).encode())) for n in EVAL_IDS]
    packet=dict(schema=1,manifest_sha256='a'*64,selection_sha256='b'*64,tasks=tasks,
                requested_tasks=14,reference_fragments_exported=False,candidates_exported=False,
                training_authorized=False,evaluation_authorized=True)
    raw=(json.dumps(packet,indent=2)+'\n').encode()
    files={'model.safetensors':'c'*64};modelsha=ev.digest(files)
    monkeypatch.setattr(ev,'MODEL_FILES_SHA',modelsha)
    rows=[]
    for task in tasks:
        row=dict(id=task['id'],split=task['split'],prompt_sha256=task['prompt_sha256'],
                 input_tokens=2,input_token_ids=[1,2],input_token_ids_sha256=ev.digest([1,2]),
                 rendered_prompt='prompt',rendered_prompt_sha256=ev.sha(b'prompt'))
        row.update(ev.output_fields([3,ev.EOS_IDS[-1]],set(ev.EOS_IDS),'BY SMT'))
        rows.append(row)
    sources={n:'d'*64 for n in ev.IMPLEMENTATION}
    config=dict(**ev.BUDGET,**ev.VERSIONS,prompts_sha256=ev.sha(raw),model_files=files,
        model_files_sha256=modelsha,eos_token_ids=ev.EOS_IDS,checkpoint_sha256=None,arm='base',
        restore_exact=True,requested_task_ids=list(EVAL_IDS),input_evidence=list(map(ev.input_evidence,rows)),
        implementation_sha256=sources,implementation_after_sha256=sources)
    summary=dict(requested_tasks=14,completed_rows=14,unattempted_task_ids=[],termination='complete')
    return raw,config,rows,summary


def check(run):
    raw,config,rows,summary=run
    return ev.validate_run(raw,ev.sha(raw),None,config,rows,summary)


def test_full14_valid(run):assert len(check(run))==14


def test_exact_checkpoint_identity_constant():
    assert len(ev.CHECKPOINT_SHA)==64
    assert ev.CHECKPOINT_SHA=='769115a0722f947efd1247bd66b6764ab82ba531671eaefab9e27be219d7aefa'


def test_incomplete_suffix_not_population_reduction(run):
    raw,config,rows,summary=run
    summary.update(completed_rows=3,unattempted_task_ids=list(EVAL_IDS[3:]),termination='phase_timeout')
    assert len(ev.validate_run(raw,ev.sha(raw),None,config,rows[:3],summary))==14


@pytest.mark.parametrize('key,value',[
    ('max_new_tokens',512),('batch_size',2),('seed',1),('seconds',1800),
    ('batch_seconds',181),('torch_version','2.13'),('transformers_version','5.14.1'),
    ('eos_token_ids',[128001]),('arm','checkpoint'),('restore_exact',False),
    ('checkpoint_sha256','a'*64),('prompts_sha256','a'*64)])
def test_contract_mutations_rejected(run,key,value):
    run[1][key]=value
    with pytest.raises(ValueError):check(run)


def test_duplicate_or_reordered_rows_rejected(run):
    run[2][1]=run[2][0]
    with pytest.raises(ValueError):check(run)


def test_split_substitution_rejected(run):
    run[2][0]['split']='train'
    with pytest.raises(ValueError):check(run)


def test_no_full_before_after_identity_rejected(run):
    del run[1]['implementation_after_sha256']
    with pytest.raises(ValueError,match='after identity'):check(run)


def test_unknown_checkpoint_not_admitted(tmp_path):
    p=tmp_path/'checkpoint';p.write_bytes(b'weights')
    with pytest.raises(ValueError,match='pinned'):ev.checkpoint_identity(p,ev.file_sha(p))
    with pytest.raises(ValueError,match='BASE'):ev.checkpoint_identity(None,ev.CHECKPOINT_SHA)


def test_pinned_checkpoint_hash_still_checked(tmp_path):
    p=tmp_path/'checkpoint';p.write_bytes(b'wrong weights')
    with pytest.raises(ValueError,match='pinned'):ev.checkpoint_identity(p,ev.CHECKPOINT_SHA)


def test_no_packet_hash_inference(run):
    with pytest.raises(ValueError,match='Explicit'):ev.validate_packet(run[0],None)


def test_short_unfinished_output_unmeasured(run):
    run[2][0].update(ev.output_fields([3,4],set(ev.EOS_IDS),'unfinished'))
    assert run[2][0]['status']=='generation_time_limit'
    assert len(check(run))==14


def test_token_cap_is_not_time_limit():
    result=ev.output_fields([3]*3072,set(ev.EOS_IDS),'unfinished')
    assert result['finish_reason']=='token_limit'
    assert result['status']=='generated'


@pytest.mark.parametrize('tokens',[[],[3]*3073,[True],[3,-1],[128009,3]])
def test_bad_output_tokens_rejected(tokens):
    with pytest.raises(ValueError):ev.output_fields(tokens,set(ev.EOS_IDS),'x')


def test_forged_time_completion_rejected(run):
    run[2][0].update(ev.output_fields([3,4],set(ev.EOS_IDS),'partial'))
    run[2][0]['status']='generated'
    with pytest.raises(ValueError):check(run)


def test_changed_output_bytes_rejected(run):
    run[2][0]['raw_reply']='DIFFERENT'
    with pytest.raises(ValueError):check(run)


def test_input_token_tampering_rejected(run):
    run[2][0]['input_token_ids']=[1,5]
    with pytest.raises(ValueError):check(run)


def test_full_denominator_required(run):
    run[3]['requested_tasks']=13
    with pytest.raises(ValueError):check(run)
