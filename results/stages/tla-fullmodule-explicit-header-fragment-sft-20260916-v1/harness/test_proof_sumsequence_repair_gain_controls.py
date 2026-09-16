import copy
from pathlib import Path
from types import SimpleNamespace
import pytest
from tools import proof_sumsequence_repair_gain_controls as g


@pytest.fixture
def real_inputs():
    v=g.verify
    tasks=v.policy.broader.combined_tasks(v.policy.broader.load_manifests())+v.policy.extra.static_tasks()
    root=v.ROOT/'results/runs/proof-sumsequence-repair-cycle-20260906-v1'
    arms={role:dict(rows=[__import__('json').loads(line) for line in (root/role/'generations.jsonl').read_bytes().splitlines()]) for role in ('parent','child')}
    replayed=g.load(v.ROOT/'results/runs/proof-sumsequence-repair-verified-20260906-v1/rows.json')
    return tasks,v.contexts(tasks),arms,replayed


def test_exact_five_real_child_fragments_and_negative_inputs(real_inputs):
    selected=g.select(*real_inputs)
    assert tuple(item['task']['id'] for item in selected)==g.IDS
    for item in selected:
        task,bad=item['task'],item['negative']
        assert all(task[k]==bad[k] for k in task if k!='prefix')
        assert task['prefix']!=bad['prefix']
        assert item['fragment']==item['previous']['fragment']
    contains=selected[3]
    before=contains['task']['prefix'];after=contains['negative']['prefix']
    assert before[:before.rfind('PROVE')+5]==after[:after.rfind('PROVE')+5]
    assert selected[-1]['negative']['prefix']==selected[-1]['task']['negative_prefix']


@pytest.mark.parametrize('mutation',['count','order','fragment','eos','gain'])
def test_no_adaptive_or_changed_inputs(real_inputs,mutation):
    tasks,contexts,arms,rows=copy.deepcopy(real_inputs)
    index=next(i for i,t in enumerate(tasks) if t['id']==g.IDS[0])
    if mutation=='count':rows.pop()
    elif mutation=='order':rows[0],rows[1]=rows[1],rows[0]
    elif mutation=='fragment':rows[40+index]['fragment']='OBVIOUS'
    elif mutation=='eos':arms['child']['rows'][index]['finish_reason']='time_limit'
    else:rows[index]['certified']=True
    with pytest.raises(ValueError):g.select(tasks,contexts,arms,rows)


@pytest.fixture
def run(real_inputs,tmp_path,monkeypatch):
    tasks=real_inputs[0];selected=g.select(*real_inputs)
    args=SimpleNamespace(output=tmp_path/'run')
    monkeypatch.setattr(g,'prepare',lambda a:(tasks,selected))
    monkeypatch.setattr(g,'identity',lambda *a:{'stable':True})
    monkeypatch.setattr(g,'audit_result',lambda *a:None)
    return args,selected


def result(positive):
    if positive:return dict(certified=True,measured_model_outcome=True,classification='proof_success')
    return dict(certified=False,measured_model_outcome=True,classification='unproved_obligation',
        strict=dict(status='verifier_reject',certified=False,returncode=10,timed_out=False,
        output='[ERROR]: Could not prove or check:\n           FALSE\n[ERROR]: 1/2 obligations failed.\n'))


def test_complete_ten_controls_separate_counts(run):
    args,selected=run;calls=[]
    def checker(task,fragment,work):
        calls.append((task,fragment));return result(work.name=='positive')
    output=g.evaluate(args,checker=checker)
    assert len(calls)==10 and output['accepted_controls']==10
    for index in range(5):assert calls[2*index][1]==calls[2*index+1][1]


def test_unsupported_false_is_preserved_not_waived(run):
    args,selected=run
    with pytest.raises(ValueError,match='unsupported'):
        g.evaluate(args,checker=lambda *a:dict(certified=False,measured_model_outcome=False,classification='unmeasured_timeout'))
    summary=g.load(args.output/'summary.json')
    assert summary['accounted_controls']==10 and summary['accepted_controls']==0 and not summary['complete']


def test_source_drift_invalidates_allclaims(run,monkeypatch):
    args,selected=run;identities=iter([{'v':1},{'v':2}])
    monkeypatch.setattr(g,'identity',lambda *a:next(identities))
    with pytest.raises(ValueError,match='identity'):
        g.evaluate(args,checker=lambda t,f,w:result(w.name=='positive'))
    summary=g.load(args.output/'summary.json')
    assert summary['accepted_controls']==0 and summary['observed_accepted_controls']==10


def test_budget_exhaustion_accounts_allten(run):
    args,selected=run;ticks=iter([0]+[401]*11)
    with pytest.raises(ValueError,match='budget'):
        g.evaluate(args,clock=lambda:next(ticks),checker=lambda *a:pytest.fail('late check'))
    assert len(g.load(args.output/'rows.json'))==10
