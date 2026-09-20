import pytest

torch = pytest.importorskip("torch")
from tools import verifier_grpo as grpo


class TinyPolicy(torch.nn.Module):
    def __init__(self):
        super().__init__()
        self.logits = torch.nn.Parameter(torch.zeros(4))


def logprob(model, _prompt, tokens):
    return torch.log_softmax(model.logits, 0)[list(tokens)].sum()


def row(sany, tlc=None, vac=None):
    return {"semantic_audit": "human_pass", "module_extracted": True, "sany": sany,
            "tlc": tlc, "tlc_vacuity": vac, "population": "state_machine"}


def test_real_optimizer_update_checkpoint_and_reload(tmp_path):
    policy = TinyPolicy()
    trainer = grpo.GRPO(policy, logprob, torch.optim.SGD(policy.parameters(), lr=.2))
    group = [grpo.Rollout("900", "p", (0,), row("fail")),
             grpo.Rollout("900", "p", (1,), row("pass", "fail_invariant")),
             grpo.Rollout("900", "p", (2,), row("pass", "pass", "clean")),
             grpo.Rollout("900", "p", (3,), {"semantic_audit": "rejected", "sany": "pass"})]
    before = policy.logits.detach().clone()
    result = trainer.step(group)
    assert result["updated"] and not torch.equal(before, policy.logits.detach())
    artifact = trainer.save(tmp_path, {"rollout_digest": grpo.rollout_digest(group), "step": 1})
    loaded = torch.load(artifact, weights_only=True)
    restored = TinyPolicy(); restored.load_state_dict(loaded["policy"])
    assert torch.equal(restored.logits, policy.logits)
    assert "optimizer" in loaded and "reference" in loaded
    with pytest.raises(FileExistsError):
        trainer.save(tmp_path, {})


def test_reward_refuses_unaudited_and_infrastructure_errors():
    # A clean verifier acceptance is not a rewardable pass without human audit.
    assert grpo.staircase_reward({"semantic_audit": "CLEAN", "module_extracted": True,
                                  "sany": "pass", "tlc": "pass",
                                  "tlc_vacuity": "clean"})[0] is None
    # Partial verifier rungs remain available for learning; neither is a pass claim.
    assert grpo.staircase_reward({"module_extracted": True, "sany": "fail"}) == (.25, "sany_fail")
    assert grpo.staircase_reward({"module_extracted": True, "sany": "pass",
                                  "tlc": "fail_invariant"}) == (.60, "tlc_reject")
    assert grpo.staircase_reward({"semantic_audit": "human_pass", "sany": "api_error"})[0] is None


@pytest.mark.parametrize("status", [None, "no_cfg", "error", "timeout"])
def test_no_partial_reward_for_unmeasured_tlc(status):
    assert grpo.staircase_reward(row("pass", status))[0] is None


def test_proof_population_cannot_be_scored_as_tlc():
    r = row("pass", "pass", "clean")
    r["population"] = "proof_module"
    assert grpo.staircase_reward(r)[0] is None


def test_update_rejects_mixed_prompts():
    policy = TinyPolicy()
    trainer = grpo.GRPO(policy, logprob, torch.optim.SGD(policy.parameters(), lr=.2))
    with pytest.raises(ValueError, match="identical prompt"):
        trainer.step([grpo.Rollout("900", "a", (0,), row("fail")),
                      grpo.Rollout("900", "b", (1,), row("pass", "fail_invariant"))])


def test_loader_fails_closed_when_a_holdout_is_present(tmp_path):
    holdout = tmp_path / "holdout.json"
    holdout.write_text('{"holdout_specs": ["30"]}')
    rollouts = tmp_path / "rollouts.jsonl"
    rollouts.write_text('{"spec":"30","prompt_id":"x","prompt":"p","tokens":[1],"verifier":{}}\n')
    with pytest.raises(ValueError, match="holdout spec 30"):
        grpo.load_groups(rollouts, holdout, group_size=1)
