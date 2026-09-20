import copy

import pytest

from tools import proof_sany_repair_learning_checks as c


def inputs():
    whole = [dict(id=i, split='train') for i in c.REPAIR_IDS]
    whole += [dict(id='task'+str(i), split='development' if i >= 36 else 'train') for i in range(2, 40)]
    tasks = dict(greedy40=whole, repair2=whole[:2])
    arms = {a: {p: [dict(id=t['id'], raw_reply='unit fixture', finish_reason='eos') for t in ts]
                for p, ts in tasks.items()} for a in ('parent', 'child')}
    return tasks, arms, dict(parent=c.PARENT_SHA, child='a'*64)


def success(*args):
    return dict(sany=1, proof=1, status='proof_success', evidence=None)


def test_complete_separate_denominators(tmp_path):
    tasks, arms, policies = inputs()
    arms['parent']['repair2'][0]['finish_reason'] = 'token_limit'
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=success)
    assert len(rows) == 84 and summary['complete'] and not summary['pooled_score']
    assert summary['phases']['greedy40']['arms']['parent']['proof_pass'] == 40
    assert summary['phases']['repair2']['arms']['parent']['proof_pass'] == 1
    assert summary['phases']['repair2']['arms']['parent']['proof_unknown'] == 1
    assert summary['phases']['greedy40']['arms']['parent']['per_population']['original_development']['requested'] == 4
    assert summary['phases']['repair2']['paired']['proof']['unknown'] == [c.REPAIR_IDS[0]]
    assert not summary['phases']['repair2']['paired']['proof']['gains']
    assert {r['policy_sha256'] for r in rows} == set(policies.values())
    assert (tmp_path/'rows.json').is_file()


@pytest.mark.parametrize('defect', ['count','order','phase','policy','binding','split'])
def test_exact_contract_required(tmp_path, defect):
    tasks, arms, policies = inputs()
    if defect == 'count': arms['child']['greedy40'].pop()
    elif defect == 'order': arms['parent']['repair2'].reverse()
    elif defect == 'phase': arms['child'].pop('repair2')
    elif defect == 'policy': policies['child'] = c.PARENT_SHA
    elif defect == 'binding': tasks['repair2'] = copy.deepcopy(tasks['repair2']); tasks['repair2'][0]['theorem'] = 'changed'
    else: tasks['repair2'][0]['split'] = 'development'
    with pytest.raises(ValueError): c.evaluate(tasks, arms, policies, {}, tmp_path, checker=success)


def test_deadlines_preserve84_unknowns(tmp_path):
    tasks, arms, policies = inputs()
    tick = [-3000]
    def clock(): tick[0] += 3000; return tick[0]
    def forbidden(*args): raise AssertionError('checker after deadline')
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=forbidden, clock=clock)
    assert len(rows) == 84 and not summary['complete']
    assert all(r['sany'] is None and r['proof'] is None for r in rows)
    c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)
    rows[0]['proof'] = 1
    with pytest.raises(ValueError): c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)


def test_raw_provenance_and_extraction_audit(tmp_path, monkeypatch):
    tasks, arms, policies = inputs()
    extraction = dict(fragment=None)
    monkeypatch.setattr(c.checks, 'extract', lambda *args: extraction)
    def reject(task, raw, *args):
        return dict(sany=0, proof=0, status='model_extraction', evidence=None,
                    extraction=extraction, raw_reply_sha256=c.sha(raw.encode()))
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=reject)
    c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)
    assert summary['phases']['greedy40']['arms']['child']['sany_reject'] == 40
    rows[-1]['policy_sha256'] = 'b'*64
    with pytest.raises(ValueError): c.audit_rows(tasks, arms, policies, rows, {}, tmp_path)


def test_original_task_reference_extractors_bind_both_phases():
    from tools import proof_sumsequence_sany_repair_packet as p
    ts = p.policy.greedy.broader.combined_tasks(p.policy.greedy.broader.load_manifests()) + p.policy.greedy.extra.static_tasks()
    selected = [next(t for t in ts if t['id'] == i) for i in c.REPAIR_IDS]
    for task in selected:
        fragment = task['reference_fragment']
        assert c.checks.extract(task, '```tla\n'+fragment+'\n```')['fragment'] == fragment.strip()
    tasks = dict(greedy40=ts, repair2=selected)
    arms = {a: {p: [dict(id=t['id']) for t in rows] for p, rows in tasks.items()} for a in ('parent', 'child')}
    c.validate_inputs(tasks, arms, dict(parent=c.PARENT_SHA, child='a'*64))


def test_phase_specific_losses_not_hidden_by_repair_gains(tmp_path):
    tasks, arms, policies = inputs()
    def checker(task, raw, output, current):
        passed = not ('child/greedy40' in str(output) and task['id'] == c.REPAIR_IDS[0])
        return dict(sany=int(passed), proof=int(passed), status='fixture', evidence=None)
    rows, summary = c.evaluate(tasks, arms, policies, {}, tmp_path, checker=checker)
    assert summary['phases']['greedy40']['paired']['proof']['losses'] == [c.REPAIR_IDS[0]]
    assert not summary['phases']['repair2']['paired']['proof']['losses']
    rows[0]['sany'] = True
    with pytest.raises(ValueError): c.summarize(rows, True)
