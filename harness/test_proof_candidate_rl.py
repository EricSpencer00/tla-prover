import json

import pytest
import torch

from tools.proof_candidate_rl import (
    advantages_for, centered_surrogate, differentiable_mean_logp, freeze_train, grouped_weights, reward_for, task_schedule,
)


@pytest.mark.parametrize('temperature', [.25, 1., 2.])
def test_centered_gradient_exactly_matches_categorical_log_normalizer(temperature):
    scores = torch.tensor([-.3, -.8, -2.], dtype=torch.float64, requires_grad=True)
    sampled = torch.tensor([0, 1, 1, 2])
    advantages = torch.tensor([.75, -.25, -.25, -.25], dtype=torch.float64)
    exact = -(advantages*(scores/temperature).log_softmax(0)[sampled]).mean()
    expected, = torch.autograd.grad(exact, scores)
    reduced = centered_surrogate(scores[sampled], advantages, temperature)
    actual, = torch.autograd.grad(reduced, scores)
    assert torch.allclose(actual, expected, atol=1e-12)


def test_temperature_scales_sampled_gradient():
    scores = torch.tensor([-.2, -.8], requires_grad=True)
    one, = torch.autograd.grad(centered_surrogate(scores, [.5, -.5], 1.), scores)
    two, = torch.autograd.grad(centered_surrogate(scores, [.5, -.5], 2.), scores)
    assert torch.equal(one, 2*two)


def test_runtime_duplicate_aggregation_matches_categorical_gradient():
    scores = torch.tensor([-.5, -.7, -1.], dtype=torch.float64, requires_grad=True)
    sampled = [1, 1, 0, 2]
    advantages = advantages_for([1., 1., 0., 0.])
    temperature = .4
    exact = -(torch.tensor(advantages)*(scores/temperature).log_softmax(0)[sampled]).mean()
    expected, = torch.autograd.grad(exact, scores)
    for index, coefficient in grouped_weights(sampled, advantages, temperature).items():
        if coefficient:
            (-scores[index]*coefficient).backward()
    assert torch.allclose(scores.grad, expected, atol=1e-12)


def test_group_only_centering_and_zero_variance_no_update():
    assert advantages_for([1., 0., 0., 0.]) == [.75, -.25, -.25, -.25]
    assert advantages_for([1., 1.]) is None
    assert advantages_for([0., 0.]) is None
    assert advantages_for([1., None]) is None
    parameter = torch.nn.Parameter(torch.tensor(1.))
    optimizer = torch.optim.AdamW([parameter], lr=.1)
    before = parameter.detach().clone()
    for group in ([1., 1.], [0., 0.], [1., None]):
        if advantages_for(group) is not None:
            optimizer.step()
    assert torch.equal(parameter, before)
    assert optimizer.state == {}
    # Separately constant groups must not acquire cross-task reward contrast.
    assert advantages_for([1., 1., 0., 0.]) is not None
    with pytest.raises(ValueError, match='centered'):
        centered_surrogate(torch.zeros(2), [.5, .5], 1.)


def test_differentiable_logp_matches_ranker_and_preserves_gradient():
    from tools.proof_candidate_rank import response_logps
    logits = torch.arange(20., requires_grad=True).reshape(4, 5)
    labels = [-100, -100, 2, 4]
    score = differentiable_mean_logp(logits, labels)
    assert float(score.detach()) == pytest.approx(response_logps(logits.detach(), labels)['mean_logp'])
    grad, = torch.autograd.grad(score, logits)
    assert torch.equal(grad[0], torch.zeros(5))
    assert torch.equal(grad[3], torch.zeros(5))
    assert grad[1].abs().sum() > 0 and grad[2].abs().sum() > 0


def test_reward_known_good_bad_and_unknown():
    assert reward_for(dict(certified=True, status='pass', returncode=0, proved=1, total=1)) == 1.
    for proved, total in [(0, 0), (1, 2), (2, 1), (1, None)]:
        assert reward_for(dict(certified=True, status='pass', returncode=0, proved=proved, total=total)) is None
    output = '[ERROR]: Could not prove or check:\n[ERROR]: 1/21 obligations failed.\nThere were backend errors processing module X.'
    assert reward_for(dict(status='verifier_reject', output=output)) == 0.
    assert reward_for(dict(status='verifier_reject', output='Error: Operator "X" not found')) == 0.
    for status in ['timeout', 'infrastructure_error', 'contract_reject', 'unrecognized_output']:
        assert reward_for(dict(status=status, output=output)) is None
    assert reward_for(dict(status='verifier_reject', output='mysterious backend failure')) is None
    for diagnostic in ['command not found', 'backend zenon unavailable', 'out of memory', 'timeout']:
        assert reward_for(dict(status='verifier_reject', output=output+'\n'+diagnostic)) is None


def test_freeze_excludes_dev_and_all_reference_answers(monkeypatch):
    from tools import proof_retrieved_context, proof_repair_pilot, proof_fact_search
    def task(index, split):
        return dict(id=str(index), split=split, source_family=split, source_sha256=split,
                    assembled_sha256=str(index), prefix='prefix'+str(index), suffix='end',
                    theorem_name='Target', target_goal='x=x', reference_fragment='SECRET'+str(index))
    tasks = [task(i, 'train') for i in range(17)]+[task(99, 'development')]
    monkeypatch.setattr(proof_retrieved_context, 'retrieve', lambda t: {'library_sha256': {}})
    monkeypatch.setattr(proof_retrieved_context, 'render', lambda c: 'statements')
    monkeypatch.setattr(proof_repair_pilot, 'with_dependency_context', lambda t: t)
    monkeypatch.setattr(proof_repair_pilot, 'prompt_for', lambda t: json.dumps(t))
    seen = []
    def proposals(*args):
        seen.append(args)
        return ['BY SMT', 'BY X'], {}
    monkeypatch.setattr(proof_fact_search, 'proposals', proposals)
    frozen = freeze_train(json.dumps({'tasks':tasks}).encode(), 8)
    assert len(frozen) == 17
    assert 'SECRET' not in json.dumps(frozen)+str(seen)
    assert 'prefix99' not in json.dumps(frozen)+str(seen)
    del tasks[0]['target_goal']
    tasks[0]['prefix'] = 'THEOREM Target == x = x\n'
    derived = freeze_train(json.dumps({'tasks':tasks}).encode(), 8)
    assert derived[0]['target_goal']
    expanded = tasks[:-1]+[task(i, 'train') for i in range(17, 50)]+[tasks[-1]]
    assert len(freeze_train(json.dumps({'tasks':expanded}).encode(), 8)) == 50
    tasks[-1]['source_family'] = 'train'
    with pytest.raises(ValueError, match='overlap'):
        freeze_train(json.dumps({'tasks':tasks}).encode(), 8)


def test_shuffled_schedule_covers_whole_epoch_without_family_order_bias():
    schedule = task_schedule(50, 64, 20260917, True)
    assert len(schedule) == 64 and set(schedule[:50]) == set(range(50))
    assert len(set(schedule[50:])) == 14
    assert schedule != task_schedule(50, 64, 20260918, True)
    assert schedule == task_schedule(50, 64, 20260917, True)
    assert task_schedule(3, 7, 1) == [0, 1, 2, 0, 1, 2, 0]
