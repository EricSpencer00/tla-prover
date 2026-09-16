from copy import deepcopy
from pathlib import Path
import pytest
from tools import protected_lineage_score as scoring


def fixture_record():
    selected = {47: ({'prompt': 'task'}, {'input_ids': [1, 2, 3], 'prompt_tokens': 2})}
    record = dict(phase='base', row=47, raw_reply='raw', raw_reply_sha256=scoring.sha('raw'),
        base_prompt_sha256=scoring.sha('task'), actual_prompt_token_ids=[1, 2],
        actual_prompt_token_count=2, actual_prompt_tokens_match_frozen=True,
        generation_seed=20261481, output_token_ids=[3],
        resolved_decode=dict(effective_num_beams=1, effective_do_sample=False,
                             effective_mode='greedy_search'))
    return selected, record


def test_partial_records_preserve_absent_candidates():
    selected, record = fixture_record()
    assert list(scoring.validate_records([record], selected)) == [('base', 47)]
    assert scoring.validate_records([], selected) == {}


@pytest.mark.parametrize('key,value', [('phase', 'unknown'), ('raw_reply', 'changed'),
    ('actual_prompt_token_ids', [1, 2, 3]), ('actual_prompt_token_count', 3),
    ('actual_prompt_tokens_match_frozen', False), ('generation_seed', 1),
    ('output_token_ids', []), ('output_token_ids', [3]*1025)])
def test_contract_tampering_fails_closed(key, value):
    selected, record = fixture_record()
    record[key] = value
    with pytest.raises(ValueError):
        scoring.validate_records([record], selected)


def test_duplicate_records_rejected():
    selected, record = fixture_record()
    with pytest.raises(ValueError):
        scoring.validate_records([record, deepcopy(record)], selected)


def test_malformed_header_is_explicit_raw_contract_rejection(tmp_path, monkeypatch):
    def forbidden(*args):
        raise AssertionError('Do not extract or pretend SANY ran')
    monkeypatch.setattr(scoring, 'score', forbidden)
    text = '```tla\n---- MODULE M ----\n====\n```'
    result = scoring.score_candidate({'raw_reply': text}, tmp_path / 'out', 'java', 'jar')
    assert result['status'] == 'model_contract_reject' and not result['sany_invoked']
    assert (tmp_path / 'out/raw.txt').read_bytes() == text.encode()


def test_canonical_header_delegates_verbatim_without_status_changes(tmp_path, monkeypatch):
    text = '---- MODULE M ----\n\\* truncated'
    def oracle(actual, output, java, jar):
        assert actual == text
        return {'status': 'unmeasured_infrastructure'}
    monkeypatch.setattr(scoring, 'score', oracle)
    assert scoring.score_candidate({'raw_reply': text}, tmp_path / 'out', 'java', 'jar') == {
        'status': 'unmeasured_infrastructure'}
