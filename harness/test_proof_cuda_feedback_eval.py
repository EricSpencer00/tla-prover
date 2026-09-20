import copy
import json
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest
from tools import proof_cuda_feedback_eval as f


@pytest.fixture(scope='module')
def packets():
    return {arm:f.export_tasks(arm) for arm in f.CHECKPOINTS}


@pytest.fixture(scope='module')
def tokenizer():
    return f.load_tokenizer(f.TOKENIZER)


def run_fixture(packet,tokenizer):
    raw=json.dumps(packet).encode()
    config=dict(**f.BUDGET,prompts_sha256=f.sha(raw),model_files=packet['model_files'],
        model_files_sha256=f.digest(packet['model_files']),requested_task_ids=f.DEV_IDS,
        restore_exact=True,arm='base' if packet['arm']=='base' else 'checkpoint',
        experiment_arm=packet['arm'],checkpoint_sha256=packet['checkpoint_sha256'],
        implementation_sha256={n:'a'*64 for n in f.IMPLEMENTATION},eos_token_ids=f.EOS_IDS,**f.FIRST_VERSIONS)
    row=f.encode_prompt(tokenizer,packet['tasks'][0])
    tokens=tokenizer('BY SMT',add_special_tokens=False,truncation=False)['input_ids']+[f.EOS_IDS[0]]
    row.update(f.output_fields(tokens,set(f.EOS_IDS),f.decode_reply(tokenizer,tokens)))
    summary=dict(termination='phase_timeout',unattempted_task_ids=f.DEV_IDS[1:])
    return raw,config,[row],summary


def test_actual_three_arm_exports_are_reference_free_and_fit(packets):
    expected={'base':[3890,1217,1305,4893],'parent':[4095,1297,1576,1687],
              'child':[3890,4480,4780,4597]}
    for arm,p in packets.items():
        assert [t['id'] for t in f.validate_export(p)]==f.DEV_IDS
        assert [e['input_tokens'] for e in p['evidence']]==expected[arm]
        assert all(set(t)=={'id','split','prompt','prompt_sha256'} for t in p['tasks'])
        assert p['reference_fragments_exported'] is False
        assert p['checkpoint_sha256']==f.CHECKPOINTS[arm]


def test_original_source_and_previous_reply_not_trimmed():
    source='  SOURCE <PROOF_HOLE>\n';reply=' \nPREVIOUS\n '
    prompt=f.feedback_prompt(source,reply,'exact error')
    assert prompt.startswith(source+'\n\n')
    assert '\n'+reply+'\n=== END PREVIOUS MODEL REPLY' in prompt


def test_diagnostic_cap_preserves_exact_raw_prefix(tokenizer):
    text='λ🙂 parse diagnostic\n'*800
    prefix=f.diagnostic_prefix(tokenizer,text)
    assert text.startswith(prefix) and prefix!=text
    assert len(tokenizer(prefix,add_special_tokens=False,truncation=False)['input_ids'])<=512
    assert f.diagnostic_prefix(tokenizer,'short raw error')=='short raw error'


@pytest.mark.parametrize('fault',['arm','checkpoint','model','prior','new','population','answer','artifact','evidence_answer','evidence_sha','diagnostic_cap'])
def test_export_fails_closed(packets,fault):
    p=copy.deepcopy(packets['base'])
    if fault=='arm':p['arm']='unknown'
    elif fault=='checkpoint':p['checkpoint_sha256']='wrong'
    elif fault=='model':p['model_files']={}
    elif fault=='prior':p['prior_attempts_per_task']=0
    elif fault=='new':p['new_attempts_per_task']=2
    elif fault=='population':p['tasks'].pop()
    elif fault=='answer':p['tasks'][0]['reference_fragment']='answer'
    elif fault=='artifact':p['first_artifacts_sha256']['verdicts']='wrong'
    elif fault=='evidence_answer':p['evidence'][0]['reference_fragment']='answer'
    elif fault=='evidence_sha':p['evidence'][0]['diagnostic_sha256']='not-a-sha'
    elif fault=='diagnostic_cap':p['evidence'][0]['diagnostic_tokens']=513
    with pytest.raises(ValueError):f.validate_export(p)


@pytest.mark.parametrize('row',[
 dict(certified=True,status='pass'),dict(certified=False,status='timeout',timed_out=True),
 dict(certified=False,status='generation_unattempted'),dict(certified=False,status='infra_error'),
 dict(certified=False,status='verifier_reject',returncode=1,output='Tool crashed'),
 dict(certified=False,status='verifier_reject',returncode=3,output='Unknown failure')])
def test_no_unknown_timeout_positive_or_unattempted_feedback(row):
    with pytest.raises(ValueError):f.failure_diagnostic(row)


def test_full_denominator_and_short_no_eos_unmeasured(packets,tokenizer):
    raw,c,rows,s=run_fixture(packets['base'],tokenizer)
    assert len(f.validate_run(raw,c,rows,s))==4
    tokens=[7,8];rows[0].update(f.output_fields(tokens,set(f.EOS_IDS),f.decode_reply(tokenizer,tokens)))
    assert rows[0]['status']=='generation_time_limit'
    f.validate_run(raw,c,rows,s)
    rows[0]['status']='generated'
    with pytest.raises(ValueError):f.validate_run(raw,c,rows,s)


@pytest.mark.parametrize('fault',['seed','runtime','arm','checkpoint','eos','token','input','prompt','complete','suffix'])
def test_run_rejects_budget_identity_and_accounting_changes(packets,tokenizer,fault):
    raw,c,r,s=run_fixture(packets['base'],tokenizer)
    if fault=='seed':c['seed']+=1
    elif fault=='runtime':c['torch_version']='changed'
    elif fault=='arm':c['experiment_arm']='child'
    elif fault=='checkpoint':c['checkpoint_sha256']='changed'
    elif fault=='eos':c['eos_token_ids']=[4]
    elif fault=='token':r[0]['token_ids']=[6]
    elif fault=='input':r[0]['input_token_ids_sha256']='changed'
    elif fault=='prompt':r[0]['raw_reply']='changed'
    elif fault=='complete':s['termination']='complete'
    elif fault=='suffix':s['unattempted_task_ids']=[]
    with pytest.raises(ValueError):f.validate_run(raw,c,r,s)


@pytest.mark.parametrize('fault',['hash','model','checkpoint'])
def test_generation_rejects_wrong_input_or_policy_before_process(tmp_path,monkeypatch,packets,fault):
    raw=json.dumps(packets['base']).encode();prompts=tmp_path/'p.json';prompts.write_bytes(raw)
    out=tmp_path/'out';out.mkdir();checkpoint=tmp_path/'c.pt';checkpoint.write_bytes(b'wrong')
    args=SimpleNamespace(prompts=prompts,output=out,model_path=tmp_path/'model',
        checkpoint=checkpoint if fault=='checkpoint' else None,
        expected_input_sha256='wrong' if fault=='hash' else f.sha(raw))
    monkeypatch.setattr('tools.proof_cuda_train.model_files',lambda p:{} if fault=='model' else packets['base']['model_files'])
    start=MagicMock();monkeypatch.setattr(f.subprocess,'Popen',start)
    with pytest.raises(ValueError):f.generate(args)
    start.assert_not_called()


def test_supervisor_kills_reaps_and_preserves_four_missing(tmp_path,monkeypatch,packets,tokenizer):
    raw=json.dumps(packets['base']).encode();prompts=tmp_path/'p.json';prompts.write_bytes(raw)
    out=tmp_path/'out';out.mkdir()
    args=SimpleNamespace(prompts=prompts,output=out,model_path=tmp_path/'model',checkpoint=None,
                         expected_input_sha256=f.sha(raw))
    monkeypatch.setattr('tools.proof_cuda_train.model_files',lambda p:packets['base']['model_files'])
    config=run_fixture(packets['base'],tokenizer)[1]
    monkeypatch.setattr(f,'admit',lambda *a:config)
    process=MagicMock(pid=456,returncode=-9);process.poll.return_value=None
    monkeypatch.setattr(f.subprocess,'Popen',lambda *a,**k:process)
    ticks=iter([0,601,602]);monkeypatch.setattr(f.time,'monotonic',lambda:next(ticks))
    kill=MagicMock();monkeypatch.setattr(f.os,'killpg',kill)
    f.generate(args);kill.assert_called_once_with(456,f.signal.SIGKILL);process.wait.assert_called_once()
    summary=json.loads((out/'summary.json').read_text())
    assert summary['unattempted_task_ids']==f.DEV_IDS and summary['termination']=='phase_timeout'


@pytest.mark.parametrize('fault',[None,'runtime','eos','token'])
def test_full_readonly_admission_reconstructs_all_inputs_before_gpu(tmp_path,monkeypatch,packets,tokenizer,fault):
    packet=copy.deepcopy(packets['base'])
    if fault=='token':packet['evidence'][0]['input_token_ids_sha256']='a'*64
    raw=json.dumps(packet).encode();prompts=tmp_path/'prompts.json';prompts.write_bytes(raw)
    model=tmp_path/'model';model.mkdir()
    (model/'generation_config.json').write_text(json.dumps(dict(eos_token_id=[4] if fault=='eos' else f.EOS_IDS)))
    monkeypatch.setattr('tools.proof_cuda_train.model_files',lambda p:packet['model_files'])
    monkeypatch.setattr(f,'runtime_versions',lambda:dict(torch_version='wrong') if fault=='runtime' else f.FIRST_VERSIONS)
    monkeypatch.setattr('transformers.AutoTokenizer.from_pretrained',lambda *a,**k:tokenizer)
    before=sorted(str(p) for p in tmp_path.rglob('*'))
    if fault:
        with pytest.raises(ValueError):f.admit(prompts,f.sha(raw),model)
    else:
        config=f.admit(prompts,f.sha(raw),model)
        assert config['restore_exact'] is False and config['requested_task_ids']==f.DEV_IDS
        assert set(config['implementation_sha256'])==set(f.IMPLEMENTATION)
        assert config['eos_token_ids']==f.EOS_IDS
    assert sorted(str(p) for p in tmp_path.rglob('*'))==before


def test_verify_uses_immutable_legacy_holes_and_adaptive_four_denominator(tmp_path,monkeypatch,packets,tokenizer):
    packet=packets['base'];raw,config,rows,summary=run_fixture(packet,tokenizer)
    timed=f.encode_prompt(tokenizer,packet['tasks'][1]);tokens=[7,8]
    timed.update(f.output_fields(tokens,set(f.EOS_IDS),f.decode_reply(tokenizer,tokens)))
    rows.append(timed);summary['unattempted_task_ids']=f.DEV_IDS[2:]
    prompts=tmp_path/'prompts.json';prompts.write_bytes(raw);out=tmp_path/'out';out.mkdir()
    gen=tmp_path/'gen';gen.mkdir();f.dump(gen/'config.json',config);f.dump(gen/'summary.json',summary)
    (gen/'generations.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in rows))
    source=tmp_path/'source';source.write_bytes(b'immutable test source')
    tasks=[dict(id=key,split='development',prefix='EXACT PREFIX\n',suffix='\nEXACT SUFFIX',
                theorem_name='Goal',dependencies=[],dependency_sha256={},source_path=str(source),
                source_sha256=f.file_sha(source),reference_fragment='NEVER EXPORT') for key in f.DEV_IDS]
    monkeypatch.setattr(f,'export_tasks',lambda *a:packet)
    monkeypatch.setattr(f,'checked',lambda *a:json.dumps(dict(tasks=tasks)).encode())
    certify=MagicMock(return_value=dict(certified=True,status='pass',returncode=0))
    monkeypatch.setattr('harness.proof_fragment_check.certify_fragment',certify)
    monkeypatch.setattr('harness.proof_gen.extract_proof_block',lambda text:'BY SMT')
    f.verify(SimpleNamespace(prompts=prompts,generations=gen,tokenizer_path=f.TOKENIZER,
                             manifest=tmp_path/'manifest',output=out))
    certify.assert_called_once()
    assert certify.call_args.args==('EXACT PREFIX\n','BY SMT','\nEXACT SUFFIX')
    assert certify.call_args.kwargs['timeout']==30
    result=json.loads((out/'summary.json').read_text())
    assert result['requested_tasks']==4 and result['adaptive_pass_at_2_rate']==.25
    assert result['prior_attempts']==4 and result['total_requested_attempts']==8
    assert result['status_counts']=={'pass':1,'generation_time_limit':1,'generation_unattempted':2}
