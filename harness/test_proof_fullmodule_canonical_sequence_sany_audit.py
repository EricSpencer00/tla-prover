from tools import proof_fullmodule_canonical_sequence_sany_audit as audit


def test_independent_audit_uses_frozen_protected_rows_and_ignores_worker_labels():
    text = open("tools/proof_fullmodule_canonical_sequence_sany_audit.py").read()
    assert audit.ROWS == (47, 107)
    assert "worker_labels_ignored=True" in text
    assert "candidate_sany_pass" in text
    assert "model_improvement_claim=False" in text
