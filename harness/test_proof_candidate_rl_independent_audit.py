import json
from pathlib import Path

from tools.proof_candidate_rl_independent_audit import independent_reward


def test_independent_reward_keeps_unknown_parser_failures_out_of_zero_bucket():
    parser_failure = {
        "status": "verifier_reject", "returncode": 3, "timed_out": False,
        "certified": False, "proved": 0, "total": 0,
        "output": "Error: malformed parser diagnostic\n",
    }
    strict_failure = {
        "status": "verifier_reject", "returncode": 3, "timed_out": False,
        "certified": False, "proved": 0, "total": 0,
        "output": "[ERROR]: Could not prove or check:\n"
                  "[ERROR]: 1/4 obligations failed.\n",
    }
    timeout = {"status": "timeout", "timed_out": True, "output": ""}
    assert independent_reward(parser_failure) is None
    assert independent_reward(strict_failure) == 0.0
    assert independent_reward(timeout) is None


def test_real_candidate_rl_result_audits_without_model_load(tmp_path: Path):
    result = Path("results/runs/proof-candidate-rl-20260917-v1/job-7629827/result.7629827")
    if not (result / "summary.json").exists():
        return
    from tools.proof_candidate_rl_independent_audit import audit
    stage = Path("results/stages/tla-candidate-rl-gpu-20260917-v5")
    out = audit(stage, result,
                expected_checkpoint="daafb22ff346a1d6ba4c898417a22ebed08c4a23c4b0c17b44ea6bcdb5f14ce4")
    assert out["groups"] == 16
    assert out["checker_attempts"] == 46
    assert out["unknown_rewards"] == 29
    assert out["strict_reject_rewards"] == 17
    assert out["positive_rewards"] == 0
    assert out["updates"] == 0
