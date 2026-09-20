import pytest
from tools import proof_fullmodule_decode_budget_probe as m


@pytest.mark.parametrize('n,elapsed,finish', [
    (2048, 1, 'eos'), (2048, 1, 'token_limit'), (2048, 181, 'time_limit')])
def test_generation_completion_is_separate_and_exact(n, elapsed, finish):
    tokens = [128009] if finish == 'eos' else [1] * n if finish == 'token_limit' else [1]
    assert m.output_fields(tokens, '', elapsed, max_new_tokens=n, item_seconds=180)['finish_reason'] == finish


def test_only_supported_budget_sizes():
    with pytest.raises(ValueError):
        m.worker(type('A', (), dict(max_new_tokens=1024))())


def test_invalid_token_ids_rejected():
    with pytest.raises(ValueError):
        m.output_fields([True], '', .1, max_new_tokens=2048, item_seconds=180)


def test_checkpoint_and_admission_pins_are_distinct():
    assert m.CHILD_CHECKPOINT_SHA != m.multi.POLICY_SHA
    assert m.multi.lineage.CHILD_SHA != m.CHILD_CHECKPOINT_SHA


def test_no_training_or_gate_claims_in_contract():
    text = (m.ROOT / 'tools/proof_fullmodule_decode_budget_probe.py').read_text()
    assert 'parameter_updates=0' in text
    assert "gate_claim=False" in text and "tlc_claim=False" in text
