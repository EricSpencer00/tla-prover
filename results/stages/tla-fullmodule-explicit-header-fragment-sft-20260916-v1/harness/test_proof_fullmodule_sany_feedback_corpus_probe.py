import hashlib
import json

import pytest

from tools import proof_fullmodule_sany_feedback_corpus_probe as m

PACKET = m.ROOT / 'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json'


def base_admission(tmp_path):
    p = tmp_path / 'base.json'
    p.write_text(json.dumps({'kind': m.BASE_KIND,
                             'rows': {'train': [42, 43, 44, 49], 'eval': [47, 107]},
                             'input_sha256': m.INPUT_SHA}))
    return p


def test_corpus_pins_six_dev_rows_and_two_protected_eval_rows():
    chosen, _ = m.selected(PACKET.read_bytes())
    assert tuple(m.DEV_ROWS) == (45, 46, 50, 51, 52, 53)
    assert tuple(m.EVAL_ROWS) == (47, 107)
    assert set(chosen) == set(m.ALL_ROWS)
    assert set(m.DEV_ROWS).isdisjoint(m.EVAL_ROWS)
    assert all(chosen[i][0]['split'] == 'train' for i in m.ALL_ROWS)


def test_exact_packet_hashes_are_checked():
    raw = PACKET.read_bytes()
    changed = json.loads(raw)
    changed['rows'][50]['response'] += ' '
    with pytest.raises(ValueError, match='immutable'):
        m.selected(json.dumps(changed).encode())


def test_admission_binds_parent_and_forbids_eval_training(tmp_path):
    result = m.admit(PACKET, base_admission(tmp_path))
    assert result['kind'] == 'sany_feedback_corpus_scaffold'
    assert result['feedback_training_authorized'] is False
    assert result['eval_rows_never_train'] is True
    assert result['eval_rows_never_decoded'] is True
    assert result['dev_rows'] == [45, 46, 50, 51, 52, 53]
    with pytest.raises(ValueError, match='protected eval'):
        bad = tmp_path / 'bad.json'
        bad.write_text(json.dumps({'kind': m.BASE_KIND,
                                   'rows': {'train': [42, 43, 44, 49], 'eval': [47]},
                                   'input_sha256': m.INPUT_SHA}))
        m.admit(PACKET, bad)


def test_feedback_accepts_only_hashed_dev_records():
    draft = '---- MODULE W4Od10m2p0t3 ----\n===='
    record = {'row': 50, 'draft': draft,
              'diagnostic': 'SANY error: invalid operator ->',
              'draft_sha256': hashlib.sha256(draft.encode()).hexdigest()}
    assert m.validate_feedback(record)
    with pytest.raises(ValueError, match='development'):
        m.validate_feedback(dict(record, row=47))
    with pytest.raises(ValueError, match='hash'):
        m.validate_feedback(dict(record, draft_sha256='0' * 64))


def test_feedback_order_and_eval_isolation_are_strict(tmp_path):
    records = []
    for i in m.DEV_ROWS:
        draft = f'---- MODULE {i} ----\n===='
        records.append({'row': i, 'draft': draft,
                        'diagnostic': 'SANY status: model_sany_reject',
                        'draft_sha256': hashlib.sha256(draft.encode()).hexdigest()})
    stream = tmp_path / 'feedback.jsonl'
    stream.write_text(''.join(json.dumps(r, sort_keys=True) + '\n' for r in records))
    receipt = {'kind': 'sany_feedback_collection', 'complete': True,
               'dev_rows': list(m.DEV_ROWS), 'eval_rows': list(m.EVAL_ROWS),
               'eval_rows_never_train': True, 'eval_rows_never_decoded': True,
               'feedback_sha256': hashlib.sha256(stream.read_bytes()).hexdigest()}
    (tmp_path / 'receipt.json').write_text(json.dumps(receipt))
    loaded, found = m.load_feedback(tmp_path)
    assert loaded['complete'] is True and list(found) == list(m.DEV_ROWS)
    stream.write_text(stream.read_text().replace('"row": 50', '"row": 47', 1))
    with pytest.raises(ValueError, match='hash'):
        m.load_feedback(tmp_path)


def test_budget_has_no_gate_or_downstream_claims():
    assert m.BUDGET['updates'] == 128
    assert m.BUDGET['feedback_records'] == 6
    assert m.BUDGET['response_only'] and m.BUDGET['final_layer_only']
    assert not any(m.BUDGET[k] for k in ('gate_claim', 'generalization_claim',
                                         'proof_claim', 'tlc_claim', 'nonvacuity_claim'))
