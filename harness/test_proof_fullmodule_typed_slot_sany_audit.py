from tools import proof_fullmodule_typed_slot_sany_audit as audit
import inspect


def test_audit_binds_exact_worker_lineage_and_ignores_labels():
    assert audit.PARENT_SHA == "87489e4778193c15e12d1714eb26dd8da03c0bacb3712e26f96f24454dcf8511"
    assert audit.CHILD_SHA == "86f2104f302fe45fd96fd983e717031a80115f743753b02f3ce60056ff70e002"
    assert audit.PHASES == ("restored_parent", "trained_child")
    assert "worker_labels_ignored=True" in inspect.getsource(audit.run)
