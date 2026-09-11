from tools import protected_checkpoint_paired_generation as paired


def test_frozen_contract_has_exactly_two_rows_two_arms_two_generations():
    assert len(paired.plan()) == 8
    assert {(row, arm) for row, arm, _ in paired.plan()} == {
        (47, "existing_decoder"), (47, "grammar_enforced"),
        (107, "existing_decoder"), (107, "grammar_enforced"),
    }


def test_generation_contract_is_bounded_and_provenanced():
    assert paired.MAX_NEW_TOKENS == 1024
    assert paired.SEED == 20261011
    assert paired.sha("frozen") == paired.sha(b"frozen")
