from tools import fullmodule_explicit_header_failure_family_audit as audit


def test_first_mismatch_is_byte_exact():
    assert audit.first_mismatch("abc", "abc") is None
    assert audit.first_mismatch("abX", "abY") == 2
    assert audit.first_mismatch("abc", "ab") == 2


def test_failure_families_do_not_turn_incomplete_bytes_into_sany_credit():
    record = {"stream_reject": "complete module footer required"}
    assert audit.classify(record, "body", "candidate_unmeasured") == "footer_liveness"
    assert audit.classify({}, "body", "model_sany_reject") == "complete_body_sany_reject"
