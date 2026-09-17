from tools.proof_outcome_audit import classify_outcome


def test_site_tlaps_uncached_command_is_auditable():
    row = {
        "certified": True,
        "status": "pass",
        "proved": 1,
        "total": 1,
        "returncode": 0,
        "timed_out": False,
        "output": "All 1 obligations proved.\n",
        "command": ["tlapm", "--nofp", "--threads", "1", "M.tla"],
        "candidate_path": "/tmp/M.tla",
        "sha256": "a" * 64,
    }
    result = classify_outcome(row, provenance_verified=True)
    assert result["classification"] == "proof_success"
    assert result["reward_eligible"]


def test_target_scope_ignores_zero_obligation_dependency_sections():
    row = {
        "certified": True,
        "status": "pass",
        "proved": 7,
        "total": 7,
        "returncode": 0,
        "timed_out": False,
        "output": (
            'File "./Dependency.tla", line 1:\n'
            "[INFO]: All 0 obligation proved.\n"
            'File "./M.tla", line 1:\n'
            "[INFO]: All 7 obligations proved.\n"
        ),
        "command": ["tlapm", "--nofp", "--threads", "1", "M.tla"],
        "candidate_path": "/tmp/M.tla",
        "sha256": "a" * 64,
    }
    assert classify_outcome(row, provenance_verified=True)["classification"] == "proof_success"
