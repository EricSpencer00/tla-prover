import json

import pytest
import torch

from tools.proof_candidate_rank import encode_candidate, freeze_tasks, rank_scores, response_logps


class Tokenizer:
    eos_token_id = 9

    def apply_chat_template(self, messages, tokenize=False, add_generation_prompt=False):
        return 'prompt:' if len(messages) == 1 else 'prompt:answerEOSextra'

    def __call__(self, text, **kwargs):
        assert kwargs == dict(add_special_tokens=False, truncation=False)
        return {'input_ids': [1, 2] if text == 'prompt:' else [1, 2, 3, 4, 9, 5]}


def test_encoder_masks_prompt_includes_eos_and_excludes_trailing_template():
    encoded = encode_candidate(Tokenizer(), 'theorem', 'BY SMT', 20)
    assert encoded['input_ids'] == [1, 2, 3, 4, 9]
    assert encoded['labels'] == [-100, -100, 3, 4, 9]
    assert encoded['response_tokens'] == 3


def test_encoder_rejects_truncation_and_missing_eos():
    with pytest.raises(ValueError, match='budget'):
        encode_candidate(Tokenizer(), 'theorem', 'BY SMT', 4)
    tokenizer = Tokenizer()
    tokenizer.eos_token_id = 8
    with pytest.raises(ValueError, match='EOS'):
        encode_candidate(tokenizer, 'theorem', 'BY SMT', 20)


def test_encoder_rejects_retokenized_prefix():
    class Broken(Tokenizer):
        def __call__(self, text, **kwargs):
            return {'input_ids': [1, 2] if text == 'prompt:' else [1, 7, 3, 9]}
    with pytest.raises(ValueError, match='boundary'):
        encode_candidate(Broken(), 'theorem', 'BY SMT', 20)


def test_causal_alignment_and_mask_and_eos():
    logits = torch.tensor([[100., -100., 0.], [0., 1., 2.], [3., 2., 1.], [9., 0., 0.]])
    result = response_logps(logits, [-100, -100, 2, 0])
    expected = torch.stack([logits[1].log_softmax(0)[2], logits[2].log_softmax(0)[0]])
    assert result['sum_logp'] == pytest.approx(float(expected.sum()))
    assert result['mean_logp'] == pytest.approx(float(expected.mean()))
    assert result['response_tokens'] == 2
    logits[0] = -999  # Prompt prediction cannot alter candidate score.
    logits[-1] = 777  # Post-EOS prediction cannot alter candidate score.
    assert response_logps(logits, [-100, -100, 2, 0]) == result


def test_empty_nonfinite_and_mismatched_logits_rejected():
    with pytest.raises(ValueError, match='No scored'):
        response_logps(torch.zeros(2, 3), [-100, -100])
    with pytest.raises(ValueError, match='matching'):
        response_logps(torch.zeros(2, 3), [-100, 1, 2])
    with pytest.raises(ValueError, match='Nonfinite'):
        response_logps(torch.full((2, 3), float('nan')), [-100, 1])


def test_ranking_preregistered_mean_not_sum_and_stable_ties():
    rows = [dict(candidate_index=0, mean_logp=-2, sum_logp=-2),
            dict(candidate_index=2, mean_logp=-1, sum_logp=-100),
            dict(candidate_index=1, mean_logp=-1, sum_logp=-200)]
    assert [r['candidate_index'] for r in rank_scores(rows)] == [1, 2, 0]


def test_freeze_never_exposes_reference_answers(monkeypatch):
    from tools import proof_context_eval, proof_repair_pilot, proof_fact_search, proof_retrieved_context
    tasks = [dict(id=str(i), split='development', prefix='immutable', suffix='end',
                  theorem_name='Target', target_goal='x=x', reference_fragment='SECRET ANSWER') for i in range(4)]
    monkeypatch.setattr(proof_context_eval, 'validate_contexts', lambda *args: None)
    monkeypatch.setattr(proof_repair_pilot, 'with_dependency_context', lambda t: t)
    monkeypatch.setattr(proof_repair_pilot, 'prompt_for', lambda t: json.dumps(t))
    monkeypatch.setattr(proof_retrieved_context, 'render', lambda c: 'statement text')
    seen = []
    def proposals(*args):
        seen.append(args)
        return ['BY SMT', 'BY DEF X', 'BY Y', 'BY Z'], {}
    monkeypatch.setattr(proof_fact_search, 'proposals', proposals)
    contexts = {str(i): {'library_sha256': {}} for i in range(4)}
    frozen = freeze_tasks(json.dumps({'tasks': tasks}).encode(), contexts, {}, 32)
    assert 'SECRET ANSWER' not in json.dumps(frozen)
    assert 'reference_fragment' not in json.dumps(frozen)
    assert 'SECRET ANSWER' not in str(seen)
    tasks[0]['reference_fragment'] = 'DIFFERENT SECRET'
    assert freeze_tasks(json.dumps({'tasks': tasks}).encode(), contexts, {}, 32) == frozen
    with pytest.raises(ValueError, match='four-task'):
        freeze_tasks(json.dumps({'tasks': tasks[:3]}).encode(), contexts, {}, 32)
