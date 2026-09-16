from copy import deepcopy
import json
from types import SimpleNamespace
import pytest
from tools import proof_sumsequence_proof_rl_stochastic_verify as verify


def fixture():
    tasks=[dict(id=f't{i}',split='train') for i in range(8)]
    arms={arm:[dict(task_id=t['id'],sample_id=t['id']+':sample'+str(i),attempt=i,status='generated',
        finish_reason='eos',raw_reply='BY DEF X',policy_sha256=('a' if arm=='parent' else 'b')*64,
        token_ids_sha256=str(i)*64) for t in tasks for i in range(4)] for arm in ('parent','child')}
    return tasks,arms


def test_exact64_counts_variance_sample0_pass4_and_unknown(tmp_path):
    tasks,arms=fixture();arms['parent'][0]['finish_reason']='token_limit';arms['child'][4]['finish_reason']='time_limit'
    calls=[]
    def checker(task,reply,work,current):
        calls.append(str(work));sample=int(work.name[-1]);arm=work.parent.name
        return dict(sany=1,proof=int(sample==(1 if arm=='parent' else 0)),status='measured')
    rows,summary=verify.evaluate(tasks,arms,{},tmp_path,checker=checker)
    assert len(rows)==64 and len(calls)==62 and summary['complete'] and summary['seed']==20261003
    parent=summary['arms']['parent'];child=summary['arms']['child']
    assert parent['requested_samples']==child['requested_samples']==32
    assert parent['proof']['sample0_pass_tasks']==0 and parent['proof']['pass_at4_tasks']==8
    assert parent['proof']['complete_groups']==7 and parent['proof']['nonzero_variance_groups']==7
    assert child['proof']['sample0_pass_tasks']==7 and child['proof']['pass_at4_unknown_tasks']==1
    assert summary['paired']['proof']['sample0']['unknown']==['t0','t1']
    assert parent['token_caps']==1 and child['generation_timeouts']==1
    assert 'training seed20261002' in summary['scope'] and summary['training_authorized'] is False
    assert json.loads((tmp_path/'rows.json').read_bytes())==rows


@pytest.mark.parametrize('values,variance,pass4',[
    ([0,1,0,0],.1875,1),([0,0,0,0],0.,0),([1,1,1,1],0.,1),
    ([0,None,0,0],None,None),([0,None,1,0],None,1),
])
def test_complete_group_variance_not_unknown_imputation(values,variance,pass4):
    result=verify.group_result([dict(proof=v) for v in values],'proof')
    assert result['variance']==variance and result['pass_at4']==pass4
    assert result['complete_group'] is (None not in values)


@pytest.mark.parametrize('values',[[0,1,0],[0,1,0,True],[0,1,0,float('nan')]])
def test_group_shape_and_explicit_binary_values_required(values):
    with pytest.raises(ValueError):verify.group_result([dict(proof=v) for v in values],'proof')


def test_budget_preserves64_unknowns(tmp_path):
    tasks,arms=fixture();ticks=iter([0]+[2000]*33+[2000]+[4000]*33)
    def forbidden(*a,**k):raise AssertionError('No checker outside budget')
    rows,summary=verify.evaluate(tasks,arms,{},tmp_path,checker=forbidden,clock=lambda:next(ticks))
    assert len(rows)==64 and not summary['complete']
    assert all(r['status']=='unmeasured_budget' and r['proof'] is None for r in rows)
    assert summary['arms']['parent']['proof_unknown']==32


def test_duplicate_accounting_is_separate_from_samples(tmp_path):
    tasks,arms=fixture()
    for row in arms['parent']:row['token_ids_sha256']='c'*64
    rows,summary=verify.evaluate(tasks,arms,{},tmp_path,checker=lambda *a:dict(sany=1,proof=0,status='reject'))
    assert summary['arms']['parent']['duplicate_samples']==31
    assert summary['arms']['parent']['tasks']['t0']['duplicate_samples']==3
    assert summary['arms']['parent']['requested_samples']==32


def test_actual_outer_command_parent_checkpoint_mapping():
    remote={k:'/frozen/'+k for k in verify.sampler.evaluation.INPUTS}
    remote.update(parent_checkpoint='/original/24d5',baseline_remote_root='/old/root',baseline_remote_parent='/old/f41')
    parent=verify.remote_command(remote,arm='parent');child=verify.remote_command(remote,arm='child')
    assert parent[parent.index('--checkpoint')+1]=='/original/24d5'
    assert child[child.index('--checkpoint')+1]=='/frozen/checkpoint'
    assert parent[-4:]==child[-4:]


def test_final_raw_caps_cannot_be_promoted(tmp_path,monkeypatch):
    tasks,arms=fixture();arms['parent'][0]['finish_reason']='token_limit'
    extraction=dict(fragment=None)
    monkeypatch.setattr(verify.checks,'extract',lambda *a:extraction)
    def checker(task,reply,*a):return dict(sany=0,proof=0,status='model_extraction',extraction=extraction,
                                          raw_reply_sha256=verify.sha(reply.encode()),evidence=None)
    rows,_=verify.evaluate(tasks,arms,{},tmp_path,checker=checker);verify.audit_rows(tasks,arms,rows,{},tmp_path)
    rows[0]['proof']=1
    with pytest.raises(ValueError,match='Unknown'):verify.audit_rows(tasks,arms,rows,{},tmp_path)


def test_wrong_receipt_pin_never_calls_remote_or_old_greedy_admit(tmp_path,monkeypatch):
    path=tmp_path/'receipt.json';path.write_text('{}')
    def forbidden(*a,**k):raise AssertionError('No remote-only or old greedy admission permitted')
    monkeypatch.setattr(verify.sampler,'admit',forbidden)
    monkeypatch.setattr(verify.sampler.evaluation,'admit',forbidden)
    monkeypatch.setattr(verify.common,'target_admission',forbidden)
    with pytest.raises(ValueError,match='receipt SHA'):
        verify.validate_pair_receipt(SimpleNamespace(target_admission=path,target_admission_sha256='0'*64),None)


def test_raw_logprob_entropy_and_rng_contract_helpers_preserved():
    from pathlib import Path
    source=Path(verify.__file__).read_text()
    assert 'sampler.validate_rows(admitted,rows,tokenizer)' in source
    assert 'sampler.validate_worker(admitted,rows,worker,output)' in source
    assert "torch.equal(rngs['parent']['before'],rngs['child']['before'])" in source
    assert 'POLICIES=' not in source and 'common.target_admission(' not in source


def test_actual_prior32_packet_schema_compatibility_only():
    """Old seed20261002 bytes exercise schema, NEVER newseed sampling evidence."""
    from pathlib import Path
    root=Path(verify.__file__).resolve().parents[1]
    old=root/'results/runs/proof-sumsequence-stochastic-cycle-20260906-v1/child'
    admitted=json.loads((old/'admission.json').read_bytes())
    rows=[json.loads(line) for line in (old/'rollouts.jsonl').read_bytes().splitlines()]
    prompts=root/'results/runs/proof-sumsequence-repair-packet-20260906-main-v2/prompts.json'
    packet=verify.sampler.evaluation.packet(SimpleNamespace(prompts=prompts,arm='parent',evaluation='stochastic32'),'b'*64)
    compatibility=dict(evaluation=packet,encodings=admitted['encodings'])
    verify.sampler.validate_rows(compatibility,rows)
    for mutation in ('nonfinite_logprob','wrong_entropy_length','wrong_input_token','wrong_policy','wrong_eos'):
        bad=deepcopy(rows)
        if mutation=='nonfinite_logprob':bad[0]['selected_token_logprobs'][0]=float('nan')
        if mutation=='wrong_entropy_length':bad[0]['token_entropies'].pop()
        if mutation=='wrong_input_token':bad[0]['input_token_ids'][0]+=1
        if mutation=='wrong_policy':bad[0]['policy_sha256']='c'*64
        if mutation=='wrong_eos':bad[0]['eos_reached']=not bad[0]['eos_reached']
        with pytest.raises(ValueError):verify.sampler.validate_rows(compatibility,bad)
