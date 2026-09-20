import copy
import json
from pathlib import Path
import pytest
from tools import proof_cuda_whole_cycle as c


def training_fixture(tmp_path):
    frozen = dict(model_files={'weights':'a'*64}, train_input_sha256='b'*64,
                  train_ids=['train'+str(i) for i in range(6)], train_evidence={'controlled':True},
                  implementation_sha256={n:'c'*64 for n in c.TRAIN_SOURCES})
    config = dict(model_files=frozen['model_files'],input_sha256=frozen['train_input_sha256'],
                  train_ids=frozen['train_ids'],evidence=frozen['train_evidence'],dtype_profile=c.PROFILE,
                  requested_updates=100,seconds=600,seed=20260926,lr=1e-5,max_tokens=8192,
                  cuda_cache_policy=c.CACHE_POLICY,
                  implementation_sha256=frozen['implementation_sha256'])
    (tmp_path/'policy_optimizer.pt').write_bytes(b'fixture checkpoint')
    summary = dict(reload_tensors_exact=True,reload_logits_exact=True,evaluation_responses_forwarded=0,
                   train_tasks=6,attempted_train_tasks=6,updates=100,requested_updates=100,
                   parameter_delta_l2=1.,cuda_peak_allocated=25*1024**3,cuda_peak_reserved=30*1024**3,
                   checkpoint_sha256=c.file_sha(tmp_path/'policy_optimizer.pt'))
    steps = [dict(step=i+1,task=frozen['train_ids'][i%6],loss=1.,gradient_norm=.3) for i in range(100)]
    return frozen,config,summary,steps


def write_training(path, config, summary, steps):
    c.dump(path/'config.json',config); c.dump(path/'summary.json',summary)
    (path/'steps.jsonl').write_text(''.join(json.dumps(r)+'\n' for r in steps))


def test_complete_six_task_training_requires_actual_hundred_steps(tmp_path):
    frozen,config,summary,steps=training_fixture(tmp_path)
    write_training(tmp_path,config,summary,steps)
    assert c.check_training(tmp_path,frozen)==summary


@pytest.mark.parametrize('fault',['coverage','steps','reload','memory','nan','source','checkpoint','heldout','seed','cache_policy'])
def test_training_advancement_fails_closed(tmp_path,fault):
    frozen,config,summary,steps=training_fixture(tmp_path)
    if fault=='coverage':
        for row in steps: row['task']='train0'
    elif fault=='steps':steps.pop()
    elif fault=='reload':summary['reload_logits_exact']=False
    elif fault=='memory':summary['cuda_peak_reserved']=37*1024**3
    elif fault=='nan':steps[0]['loss']=float('nan')
    elif fault=='source':config['implementation_sha256']=dict(config['implementation_sha256'],unexpected='f'*64)
    elif fault=='checkpoint':summary['checkpoint_sha256']='d'*64
    elif fault=='heldout':summary['evaluation_responses_forwarded']=1
    elif fault=='seed':config['seed']+=1
    elif fault=='cache_policy':config.pop('cuda_cache_policy')
    write_training(tmp_path,config,summary,steps)
    with pytest.raises(ValueError):c.check_training(tmp_path,frozen)


def test_new_pbs_has_nested_budget_and_required_frozen_inputs():
    source=(c.ROOT/'tools/proof_cuda_whole_cycle.pbs').read_text()
    assert 'walltime=00:50:00' in source and '2700s' in source
    for name in ('PROOF_WHOLE_ROOT','PROOF_WHOLE_PARENT','PROOF_WHOLE_TRAIN_SHA','PROOF_WHOLE_PROMPTS_SHA'):
        assert '${'+name+':?' in source


@pytest.mark.parametrize('fault',[None,'prefix','response','overflow'])
def test_actual_target_encoder_must_match_frozen_evidence(fault):
    from harness.test_proof_cuda_train import Tokenizer
    from tools.proof_cuda_whole_eval import encode_prompt
    tokenizer=Tokenizer()
    task=dict(id='x',split='train',prompt='a proof hole',prompt_sha256='unused')
    row=dict(task,response='BY SMT')
    actual=encode_prompt(tokenizer,task); encoded=c.encode_row(tokenizer,row)
    evidence=dict(id='x',prompt_tokens=actual['input_tokens'],
                  input_token_ids_sha256=c.digest(actual['input_token_ids']),
                  response_tokens=encoded['response_tokens'],total_tokens=len(encoded['input_ids']))
    packet=dict(rows=[row],token_feasibility=dict(rows=[evidence]))
    if fault=='prefix':evidence['input_token_ids_sha256']='a'*64
    elif fault=='response':evidence['response_tokens']+=1
    elif fault=='overflow':task['prompt']='x'*8192
    if fault:
        with pytest.raises(ValueError):c.check_encodings(tokenizer,packet,[task])
    else:c.check_encodings(tokenizer,packet,[task])


def recovery_fixture(tmp_path, monkeypatch):
    from tools.proof_cuda_whole_eval import IMPLEMENTATION
    runtime=tmp_path/'old'; source=runtime/'results/cycle'; source.mkdir(parents=True)
    names=set(IMPLEMENTATION)|set(c.TRAIN_SOURCES)|{
        'tools/proof_cuda_whole_cycle.py','tools/proof_cuda_whole_cycle.pbs',
        'tools/proof_cuda_cycle.py','tools/proof_cuda_hierarchical_cycle.py','tools/proof_cuda_repair_eval.py'}
    assert len(names)==12
    for name in names:
        path=runtime/name; path.parent.mkdir(parents=True,exist_ok=True); path.write_text(name)
    hashes={n:c.file_sha(runtime/n) for n in names}
    (runtime/'train.json').write_bytes(b'train'); (runtime/'prompts.json').write_bytes(b'prompts')
    old=dict(train_input_sha256=c.sha(b'train'),prompts_sha256=c.sha(b'prompts'),eos_token_ids=[4],
        parent_checkpoint_sha256=c.PARENT_SHA,model_files={'weights':'h'},train_ids=['x'],
        train_evidence={'checked':True},profile=c.PROFILE,implementation_sha256=hashes)
    frozen=copy.deepcopy(old)
    for name in c.RESUME_ALLOWED_CHANGES:frozen['implementation_sha256'][name]='changed'
    c.dump(source/'config.json',dict(frozen=old))
    c.dump(source/'failure.json',dict(error="ValueError('Memory headroom exceeded')",completed_phases=['matched_parent_probes']))
    files=['progress.json','training/config.json','training/encodings.json','training/steps.jsonl',
           'training/train.json']+[arm+'/'+name for arm in ('base','parent')
                                  for name in ('config.json','summary.json','generations.jsonl')]
    for name in files:
        path=source/name; path.parent.mkdir(parents=True,exist_ok=True);path.write_text('{}')
    checkpoint=source/'training/policy_optimizer.pt';checkpoint.write_bytes(b'failed checkpoint')
    c.dump(source/'training/summary.json',dict(checkpoint_sha256=c.file_sha(checkpoint),updates=100,
        attempted_train_tasks=6,reload_tensors_exact=True,reload_logits_exact=True,cuda_peak_reserved=39862665216))
    monkeypatch.setattr(c,'RESUME_CONFIG_SHA',c.file_sha(source/'config.json'))
    monkeypatch.setattr(c,'RESUME_FAILURE_SHA',c.file_sha(source/'failure.json'))
    monkeypatch.setattr(c,'FAILED_CHECKPOINT_SHA',c.file_sha(checkpoint))
    monkeypatch.setattr(c,'RESUME_ARTIFACT_SHA',{n:c.file_sha(source/n) for n in files+['training/summary.json']})
    versions=dict(torch_version='torch-fixture',transformers_version='transformers-fixture')
    monkeypatch.setattr(c,'runtime_versions',lambda:versions)
    calls=[]
    def probe(path,raw,frozen,checkpoint_sha,tokenizer):
        calls.append((path,raw,frozen,checkpoint_sha,tokenizer))
        return dict(generated=10,**versions)
    monkeypatch.setattr(c,'check_probe',probe)
    return source,tmp_path/'new/results/cycle',runtime,frozen,b'prompts',object(),calls


def test_recovery_reuses_only_pinned_parent_outputs_with_fresh_training(tmp_path,monkeypatch):
    source,output,runtime,frozen,raw,tok,calls=recovery_fixture(tmp_path,monkeypatch)
    result=c.validate_resume(source,output,runtime,frozen,raw,tok)
    assert result['parents_regenerated'] is False and result['optimizer_resume'] is False
    assert result['failed_checkpoint_loaded'] is False
    assert result['allowed_runtime_changes']==sorted(c.RESUME_ALLOWED_CHANGES)
    assert [call[0] for call in calls]==[source/'base',source/'parent']
    assert [call[3] for call in calls]==[None,c.PARENT_SHA]
    assert calls[0][2]['implementation_sha256']!=frozen['implementation_sha256']
    assert not output.exists()


@pytest.mark.parametrize('fault',['original_runtime','forbidden_new_runtime','inputs','new_model',
    'raw_prompt','failure','config','artifact','checkpoint','child_exists','complete_exists','overlap','runtime_version','incomplete_probe'])
def test_recovery_fails_closed(tmp_path,monkeypatch,fault):
    source,output,runtime,frozen,raw,tok,_=recovery_fixture(tmp_path,monkeypatch)
    if fault=='original_runtime':(runtime/'tools/proof_cuda_whole_eval.py').write_text('changed')
    elif fault=='forbidden_new_runtime':frozen['implementation_sha256']['tools/proof_cuda_whole_eval.py']='changed'
    elif fault=='inputs':(runtime/'train.json').write_text('changed')
    elif fault=='new_model':frozen['model_files']={'weights':'different'}
    elif fault=='raw_prompt':raw=b'different'
    elif fault=='failure':(source/'failure.json').write_text('{}')
    elif fault=='config':(source/'config.json').write_text('{}')
    elif fault=='artifact':(source/'base/generations.jsonl').write_text('changed')
    elif fault=='checkpoint':(source/'training/policy_optimizer.pt').write_text('changed')
    elif fault=='child_exists':(source/'whole').mkdir()
    elif fault=='complete_exists':(source/'summary.json').write_text('{}')
    elif fault=='overlap':output=source/'new'
    elif fault=='runtime_version':monkeypatch.setattr(c,'runtime_versions',lambda:dict(torch_version='changed'))
    elif fault=='incomplete_probe':
        def reject(*args):raise ValueError('Incomplete ten-task probe')
        monkeypatch.setattr(c,'check_probe',reject)
    with pytest.raises(ValueError):c.validate_resume(source,output,runtime,frozen,raw,tok)


def test_resume_main_skips_parents_but_retrains_fresh_then_generates_child(tmp_path,monkeypatch):
    source,output,runtime,frozen,raw,tok,calls=recovery_fixture(tmp_path,monkeypatch)
    versions=c.runtime_versions()
    arm=dict(model_files=frozen['model_files'],prompts_sha256=frozen['prompts_sha256'],**versions)
    recovery=dict(base=arm,parent=arm,source=str(source),optimizer_resume=False)
    monkeypatch.setattr(c,'freeze',lambda *a:frozen)
    monkeypatch.setattr(c,'validate_resume',lambda *a:recovery)
    monkeypatch.setattr(c,'check_training',lambda *a:dict(checkpoint_sha256='new-child'))
    monkeypatch.setattr(c,'check_probe',lambda *a:arm)
    import transformers
    monkeypatch.setattr(transformers.AutoTokenizer,'from_pretrained',lambda *a,**k:tok)
    commands=[]
    monkeypatch.setattr(c,'run_processes',lambda cmds,logs,seconds:commands.extend(cmds))
    monkeypatch.setattr(c.sys,'argv',['cycle','--train-input',str(runtime/'train.json'),
        '--prompts',str(runtime/'prompts.json'),'--parent-checkpoint',str(tmp_path/'immutable.pt'),
        '--output',str(output),'--train-sha256',frozen['train_input_sha256'],
        '--prompts-sha256',frozen['prompts_sha256'],'--resume-cycle',str(source),
        '--resume-runtime-root',str(runtime)])
    c.main()
    assert len(commands)==2
    assert commands[0][2]=='train' and '--checkpoint' not in commands[0]
    assert commands[1][2]=='generate'
    assert commands[1][commands[1].index('--checkpoint')+1]==str(output/'training/policy_optimizer.pt')
    assert not (output/'base').exists() and not (output/'parent').exists()
    assert json.loads((output/'summary.json').read_text())['verification_pending'] is True
