from copy import deepcopy
import json
from types import SimpleNamespace
import pytest
from tools import proof_sumsequence_policy_eval as module


@pytest.fixture
def data(monkeypatch):
    files = {'model.safetensors':'abc'}
    monkeypatch.setattr(module.common,'MODEL_FILES_SHA',module.digest(files))
    inputs = [dict(id='sumsequence-'+n,split='train',prompt_sha256='prompt',
        input_token_ids=[1],input_tokens=1,status='ready')
        for n in ('FrontDef','Lemma2','Lemma2a','Lemma3')]
    admission = dict(budget=deepcopy(module.BUDGET), eos_token_ids=module.common.EOS_IDS,
        versions=module.common.FIRST_VERSIONS,model_files=files,model_files_sha256=module.digest(files),
        arm='checkpoint',checkpoint_sha256=module.CHILD_SHA,input_evidence=inputs)
    rows = [dict(r,**module.common.output_fields([2,128009],set(module.common.EOS_IDS),'proof')) for r in inputs]
    return admission,rows


def test_full_and_partial_rows(data):
    a,rows=data
    module.validate_rows(a,rows)
    module.validate_rows(a,rows[:2])


def test_reordered_rows_rejected(data):
    a,rows=data
    with pytest.raises(ValueError,match='ordered input'):
        module.validate_rows(a,rows[::-1])


@pytest.mark.parametrize('field',['raw_reply','token_ids','finish_reason','status'])
def test_output_evidence_tampering(data,field):
    a,rows=data
    rows[0][field] = [2] if field=='token_ids' else 'tampered'
    with pytest.raises(ValueError):
        module.validate_rows(a,rows)


def test_cap_and_timeout_not_eos(data):
    a,rows=data
    for ids,expected in (([2]*3072,'token_limit'),([2]*5,'time_limit')):
        rows[0].update(module.common.output_fields(ids,set(module.common.EOS_IDS),'proof'))
        module.validate_rows(a,rows)
        assert rows[0]['finish_reason']==expected and not rows[0]['eos_reached']


def test_wrong_checkpoint_rejected(data):
    a,rows=data
    a['checkpoint_sha256']='0'*64
    with pytest.raises(ValueError,match='checkpoint identity'):
        module.validate_rows(a,rows)


def test_full_denominator(data):
    a,rows=data
    a['input_evidence'].pop()
    with pytest.raises(ValueError,match='denominator'):
        module.validate_rows(a,rows)


def test_wrong_population(data):
    a,rows=data
    a['input_evidence'][0]['id']='development-foreign'
    with pytest.raises(ValueError,match='TRAIN4'):
        module.validate_rows(a,rows)


def test_batch_keeps_skipped_child(tmp_path):
    (tmp_path/'base').mkdir()
    module.dump(tmp_path/'base/summary.json',dict(complete=False,unattempted_ids=['sumsequence-Lemma3']))
    module.write_batch_summary(tmp_path)
    report=json.loads((tmp_path/'batch-summary.json').read_text())
    assert report['requested_samples']==8 and not report['complete']
    assert report['per_arm']['child']['status']=='unattempted'
    assert len(report['per_arm']['child']['unattempted_ids'])==4


def test_bad_ledger_keeps_denominator(tmp_path,monkeypatch,data):
    admission,_=data
    module.dump(tmp_path/'admission.json',admission)
    args=SimpleNamespace(admission=tmp_path/'admission.json',prompts=tmp_path/'prompts.json',
        expected_input_sha256='x',model_path=tmp_path,checkpoint=None,output=tmp_path/'run')
    monkeypatch.setattr(module,'admit',lambda *a:admission)
    def run(*a):
        (args.output/'generations.jsonl').write_text('{invalid json}\n')
        return dict(returncode=0,output='',seconds=1,timed_out=False,
                    execution_complete=True,cleanup_complete=True,output_complete=True)
    monkeypatch.setattr(module,'run_owned',run)
    with pytest.raises(ValueError):
        module.generate(args)
    report=json.loads((args.output/'summary.json').read_text())
    assert report['requested_tasks']==4 and not report['complete']
    assert len(report['unattempted_ids'])==4
    assert (args.output/'failure.json').exists()


def test_coordinated_text_hash_edit_fails_redecode(monkeypatch,data):
    admission,rows=data
    tasks=[{'id':r['id']} for r in rows]
    originals={r['id']:r for r in admission['input_evidence']}
    monkeypatch.setattr(module.common,'encode_prompt',lambda tokenizer,t:originals[t['id']])
    monkeypatch.setattr(module.common,'decode_reply',lambda tokenizer,tokens:'proof')
    module.validate_decoding(tasks,rows,None)
    rows[0]['raw_reply']='forged';rows[0]['raw_reply_sha256']=module.sha(b'forged')
    module.validate_rows(admission,rows)
    with pytest.raises(ValueError,match='output reconstruction'):
        module.validate_decoding(tasks,rows,None)
