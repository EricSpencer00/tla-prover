import pytest
import torch

from tools.proof_syntax_preference_train import first_divergence, preference_loss, restore


def test_contrastive_update_increases_valid_token_margin():
    scores = torch.nn.Parameter(torch.tensor([-1., 2., .5]))
    optimizer = torch.optim.SGD([scores], lr=.1)
    loss, before = preference_loss(scores, 0, 1)
    before = float(before.detach())
    loss.backward()
    optimizer.step()
    assert float((scores[0] - scores[1]).detach()) > before


def test_restore_changes_base_and_exactly_reloads_checkpoint():
    net = torch.nn.Linear(3, 2, bias=False)
    selected = dict(net.named_parameters())
    saved = {'trainable_state': {'weight': torch.full((2, 3), .25)}}
    base = net(torch.ones(1, 3)).detach().clone()
    restore(selected, saved)
    assert torch.equal(net.weight, saved['trainable_state']['weight'])
    assert not torch.equal(net(torch.ones(1, 3)), base)
    with torch.no_grad():
        net.weight.zero_()
    restore(selected, saved)
    assert torch.equal(net(torch.ones(1, 3)), torch.full((1, 2), .75))


def test_restore_rejects_incompatible_weights():
    selected = {'weight': torch.nn.Parameter(torch.zeros(2, 3))}
    with pytest.raises(ValueError, match='names mismatch'):
        restore(selected, {'trainable_state': {'different': torch.zeros(2, 3)}})
    with pytest.raises(ValueError, match='tensor mismatch'):
        restore(selected, {'trainable_state': {'weight': torch.zeros(3, 2)}})


def test_preference_cannot_train_on_prompt_tokens():
    with pytest.raises(ValueError, match='response-only'):
        first_divergence([1, 2, 3], [1, 4, 3], prompt_length=2)
    assert first_divergence([1, 2, 3], [1, 2, 4], 2) == {
        'prefix': [1, 2], 'positive': 3, 'negative': 4}
