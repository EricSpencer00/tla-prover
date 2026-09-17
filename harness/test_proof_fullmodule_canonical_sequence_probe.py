from tools import proof_fullmodule_canonical_sequence_probe as probe


def test_canonical_sequence_round_trips_exact_utf8_bytes():
    source = "---- MODULE Demo ----\nEXTENDS Naturals\nInit == TRUE\n====\n"
    frame, structure, parts = probe.encode_sequence(source)
    reconstructed, decoded, decoded_parts = probe.decode_sequence(frame)
    assert reconstructed == source
    assert structure["module_name"] == "Demo"
    assert len(parts) == len(decoded_parts)
    assert all(item["byte_count"] > 0 for item in decoded_parts)


def test_canonical_sequence_rejects_transport_corruption():
    source = "---- MODULE Demo ----\nInit == TRUE\n====\n"
    frame, _, _ = probe.encode_sequence(source)
    checks = probe.transport_controls(frame)
    assert [item["label"] for item in checks] == [
        "exact", "wrong_length", "wrong_digest", "reordered", "trailing"]
    assert all(item["controls_ok"] for item in checks)


def test_contract_is_answer_free_and_has_protected_holdout():
    text = open("tools/proof_fullmodule_canonical_sequence_probe.py").read()
    assert "protected response bodies are never read" in text.lower()
    assert "target_injection=False" in text
    assert "generated_feedback_loaded=False" in text
    assert probe.PROTECTED == (47, 107)
    assert probe.VALIDATION == (59, 60, 61, 62, 63, 64)
