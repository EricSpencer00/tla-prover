import hashlib
import json

import pytest
from tools import proof_fullmodule_sany_feedback_repair_probe as m

PACKET = m.ROOT / 'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json'


def base_admission(tmp_path):
    p = tmp_path / 'base.json'
    p.write_text(json.dumps({'kind': m.BASE_KIND, 'rows': {'train': [42, 43, 44, 49], 'eval': [47, 107]}, 'input_sha256': m.INPUT_SHA}))
    return p


def test_dev_eval_rows_and_exact_hashes():
    chosen, _ = m.selected(PACKET.read_bytes())
    assert set(chosen) == {45, 46, 47, 107}
    assert set(m.DEV_ROWS).isdisjoint(m.EVAL_ROWS)
    assert all(chosen[i][0]['split'] == 'train' for i in chosen)
    assert sum(chosen[i][1]['response_tokens'] for i in m.DEV_ROWS) == 430


def test_admission_requires_authenticated_four_row_parent(tmp_path):
    out = tmp_path / 'admission.json'
    result = m.admit(PACKET, base_admission(tmp_path))
    assert result['kind'] == 'sany_feedback_repair_scaffold'
    assert result['feedback_training_authorized'] is False
    assert result['eval_rows_never_train'] is True
    with pytest.raises(ValueError, match='four-row'):
        bad = tmp_path / 'bad.json'; bad.write_text(json.dumps({'kind': m.BASE_KIND, 'rows': {'train': [44, 49], 'eval': [47, 107]}, 'input_sha256': m.INPUT_SHA}))
        m.admit(PACKET, bad)


def test_feedback_accepts_only_dev_hashed_draft_and_diagnostic():
    draft = '---- MODULE W4Od18m9p1t2 ----\n===='
    record = {'row': 45, 'draft': draft, 'diagnostic': 'SANY error: invalid operator ->', 'draft_sha256': hashlib.sha256(draft.encode()).hexdigest()}
    assert m.validate_feedback(record)
    with pytest.raises(ValueError, match='development'):
        m.validate_feedback(dict(record, row=47))
    with pytest.raises(ValueError, match='hash'):
        m.validate_feedback(dict(record, draft_sha256='0' * 64))


def test_no_gate_claims_and_fixed_budget():
    assert m.BUDGET['updates'] == 128 and m.BUDGET['response_only'] and m.BUDGET['final_layer_only']
    assert not any(m.BUDGET[k] for k in ('gate_claim', 'generalization_claim', 'proof_claim', 'tlc_claim', 'nonvacuity_claim'))


def test_diagnostic_is_owned_process_output_and_missing_output_is_explicit():
    assert m._diagnostic({'status': 'model_sany_reject',
                          'process': {'output': '***Parse Error*** ->'}}) == '***Parse Error*** ->'
    assert m._diagnostic({'status': 'model_extraction', 'process': None}) == 'SANY status: model_extraction'


def test_collection_contract_never_places_eval_rows_in_feedback():
    source = (m.ROOT / 'tools/proof_fullmodule_sany_feedback_repair_probe.py').read_text()
    assert 'for i in DEV_ROWS' in source
    assert 'eval_rows_never_decoded=True' in source
    assert "out / 'sany' / str(i)" in source


def test_structural_repair_hint_is_syntax_specific():
    prompt = m.feedback_prompt('write module', 'bad draft', 'SANY parse error: ->')
    assert '[1..N -> 0..Cap]' in prompt
    assert 'one ==== footer' in prompt
    assert 'W4Od2m7p4t2' in m.eval_feedback_prompt('write module', 'bad draft', 'SANY parse error')
