import json

from tools.prover_artifact_census import census


def test_failed_run_with_checkpoint_and_rows_is_not_called_empty(tmp_path):
    (tmp_path / "policy_optimizer.pt").write_bytes(b"checkpoint")
    (tmp_path / "restored_parent-row-47.json").write_text("{}")
    (tmp_path / "trained_child-row-47.json").write_text("{}")
    result = census(tmp_path, exit_status=1)
    assert result["checkpoint_created"] is True
    assert result["sany_evaluation"] is True
    assert result["summary_metrics_unknown"] is True


def test_missing_result_directory_is_conservative(tmp_path):
    result = census(tmp_path / "missing", exit_status=1)
    assert result["checkpoint_created"] is False
    assert result["sany_evaluation"] is False
    assert result["summary_metrics_unknown"] is True
