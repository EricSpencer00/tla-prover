from tools import proof_fullmodule_typed_slot_probe as probe


def test_typed_slots_render_canonical_module_and_preserve_body():
    source = "---- MODULE Demo ----\nEXTENDS Naturals\nInit == TRUE\n====\n"
    encoded = probe.encode_slots(source)
    parsed = probe.parse_slots(encoded["text"])
    rendered = probe.render_slots(parsed)
    assert parsed["module_name"] == "Demo"
    assert [slot["kind"] for slot in parsed["slots"]] == ["declarations", "operator"]
    assert rendered == source


def test_typed_slots_normalize_noncanonical_framing_without_repairing_body():
    source = "--------- MODULE Demo ---------\nEXTENDS Naturals\nInit == TRUE\n================================\n"
    encoded = probe.encode_slots(source)
    rendered = probe.render_slots(probe.parse_slots(encoded["text"]))
    assert rendered == "---- MODULE Demo ----\nEXTENDS Naturals\nInit == TRUE\n====\n"
    assert rendered != source


def test_typed_slot_transport_controls_reject_identity_and_trailing_corruption():
    source = "---- MODULE Demo ----\nInit == TRUE\n====\n"
    checks = probe.transport_controls(probe.encode_slots(source)["text"])
    assert [item["label"] for item in checks] == [
        "exact", "wrong_ordinal", "reordered", "unknown_kind", "trailing"
    ]
    assert all(item["controls_ok"] for item in checks)


def test_contract_is_answer_free_and_protected_rows_are_metadata_only():
    text = open("tools/proof_fullmodule_typed_slot_probe.py").read().lower()
    assert "protected response bodies are never read" in text
    assert "target_injection=false" in text
    assert "generated_feedback_loaded=false" in text
    assert probe.PROTECTED == (47, 107)
    assert probe.VALIDATION == (59, 60, 61, 62, 63, 64)
