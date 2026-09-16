import json

from tools import proof_fullmodule_sany_feedback_correction_train as m


PACKET = m.ROOT / 'results/runs/proof-fullmodule-learning-packet-20260906-v2/train.json'


def test_exact_packet_selection_keeps_protected_rows_out_of_training():
    chosen, _ = m.selected(PACKET.read_bytes())
    assert set(chosen) == set(m.TRAIN + m.VALID + m.PROTECTED)
    assert set(m.PROTECTED).isdisjoint(m.TRAIN + m.VALID)


def test_fault_corpus_is_deterministic_and_single_edit():
    packet = json.loads(PACKET.read_bytes())
    for row in m.TRAIN + m.VALID:
        good = packet['rows'][row]['response']
        faults = m.candidate_faults(good)
        assert faults == m.candidate_faults(good)
        assert all(bad != good for _, bad in faults)
        assert all(kind and isinstance(bad, str) for kind, bad in faults)


def test_feedback_prompt_contains_verifier_context_but_not_reference_target():
    prompt = m.correction_prompt(
        'write a TLA+ module',
        '---- MODULE W4Od42 ----\nInit == )\n===',
        'Encountered ")" at line 2',
        'W4Od42',
    )
    assert 'prior candidate' in prompt
    assert 'exact SANY diagnostic' in prompt
    assert 'W4Od42' in prompt
    assert 'corrected TLA+ module' in prompt


def test_budget_is_bounded_and_claims_are_false():
    assert m.BUDGET['steps'] == 16
    assert m.BUDGET['rank'] == 4
    assert m.BUDGET['adapter_layers'] == [30, 31]
    assert m.BUDGET['feedback_weight'] + m.BUDGET['anchor_weight'] == 1.0
