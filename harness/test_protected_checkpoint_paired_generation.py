from pathlib import Path

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


def test_repeats_are_labeled_deterministic_not_independent_samples():
    metadata = paired.generation_metadata(47, "existing_decoder", 1)
    assert metadata["sampling_mode"] == "greedy"
    assert metadata["generation_role"] == "deterministic_replicate"
    assert metadata["independent_sample"] is False
    assert metadata["generation_seed"] == 20261482


def test_real_grammar_mask_smoke_precedes_large_model_loading():
    source = Path("tools/protected_checkpoint_paired_generation.py").read_text()
    assert "def smoke_grammar_mask_kernel(" in source
    assert source.index("smoke_grammar_mask_kernel(") < source.index("AutoModelForCausalLM.from_pretrained")
