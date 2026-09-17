from tools import proof_fullmodule_typed_slot_sft_train as train


def test_typed_worker_has_distinct_renderer_owned_contract():
    train.configure()
    assert train.EXPERIMENT_KIND == "fullmodule_typed_slot_sft_v1"
    assert train.BUDGET["stream_segments"] == 1
    assert train.BUDGET["objective"] == "typed_declaration_operator_slot_response_sft"
    assert train.manifest_value


def test_typed_worker_does_not_use_protected_rows_as_training_rows():
    assert 47 not in train.TRAIN
    assert 107 not in train.TRAIN
    assert set(train.VALID).isdisjoint(train.TRAIN)
