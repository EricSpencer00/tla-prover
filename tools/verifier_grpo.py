"""Small, fail-closed verifier-rewarded GRPO update core.

This is deliberately a training primitive, not a claim that an offline ledger is
on-policy.  A caller supplies completions sampled from its *current* policy plus
the frozen verifier row and Rule-9 audit result for each completion.  We compute
the staircase reward, normalize only within a prompt group, and take a real
PyTorch policy-gradient optimizer step with squared-log-prob regularization.
This reference implementation is not a scalable 120B trainer. The caller must reload its serving
policy after a checkpoint before collecting the next group.

Infrastructure errors never receive reward.  A *human-confirmed* semantic audit
is required only to turn a clean verifier acceptance into the terminal tier-3
reward: ``CLEAN`` from the mechanical audit is queued for review, not treated as
a pass.  Earlier staircase rungs remain useful partial feedback and are not
claims that a candidate passed its intended property. Holdout specs fail at load
time.
"""
from __future__ import annotations

import copy
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Iterable

try:
    import torch
except ImportError:  # pragma: no cover - exercised by CLI error path
    torch = None


REWARD = {"no_module": 0.0, "sany_fail": 0.25, "tlc_reject": 0.60, "pass": 1.0}
INFRA_PREFIXES = ("api_error", "timeout", "infra", "worker_error", "exception")


def _holdout_specs(path: Path) -> set[str]:
    return {str(x) for x in json.loads(path.read_text())["holdout_specs"]}


def staircase_reward(row: dict) -> tuple[float | None, str]:
    """Return (reward, tier); None means exclude, never turn an error into loss."""
    status = " ".join(str(row.get(k, "")) for k in ("error", "sany", "tlc", "tlaps"))
    if any(x in status.lower() for x in INFRA_PREFIXES):
        return None, "infrastructure_error"
    if row.get("population") == "proof_module":
        return None, "proof_population_excluded"
    if row.get("error") or row.get("sany") in ("error", "fail_missing_module"):
        return None, "unclassified_verifier_error"
    if not row.get("module_extracted", row.get("sany") not in (None, "no_module_header")):
        return REWARD["no_module"], "no_module"
    if row.get("sany") != "pass":
        return REWARD["sany_fail"], "sany_fail"
    # Libraries are SANY-only, exactly matching repair.verdict_of population rules.
    if row.get("population") == "library":
        return (REWARD["pass"], "pass") if row.get("semantic_audit") == "human_pass" \
            else (None, "semantic_audit_pending_or_rejected")
    tlc = row.get("tlc")
    if tlc not in ("pass", "pass_expected_violation", "fail_invariant",
                   "fail_deadlock", "fail_liveness"):
        return None, "unclassified_verifier_error"
    clean = row.get("tlc_vacuity") == "clean"
    if tlc in ("pass", "pass_expected_violation") and clean:
        return (REWARD["pass"], "pass") if row.get("semantic_audit") == "human_pass" \
            else (None, "semantic_audit_pending_or_rejected")
    # A vacuous acceptance is deliberately only the middle rung.
    return REWARD["tlc_reject"], "tlc_reject"


@dataclass(frozen=True)
class Rollout:
    spec: str
    prompt: str
    tokens: tuple[int, ...]
    verifier: dict


def load_groups(path: Path, holdout_path: Path, group_size: int = 8) -> list[list[Rollout]]:
    """Load JSONL ordered into adjacent prompt groups; fail closed on contamination."""
    holdout = _holdout_specs(holdout_path)
    groups: dict[str, list[Rollout]] = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        raw = json.loads(line)
        spec = str(raw["spec"])
        if spec in holdout:
            raise ValueError(f"holdout spec {spec} appears in RL prompt pool")
        tokens = tuple(raw["tokens"])
        if not tokens:
            raise ValueError("empty completion token sequence")
        groups.setdefault(raw["prompt_id"], []).append(
            Rollout(spec, raw["prompt"], tokens, raw["verifier"]))
    out = list(groups.values())
    bad = [len(g) for g in out if len(g) != group_size]
    if bad:
        raise ValueError(f"every prompt needs exactly G={group_size} rollouts; got {bad[:4]}")
    return out


class GRPO:
    """A compact grouped REINFORCE/GRPO step over a causal log-prob callback.

    ``logprob(policy, prompt, tokens)`` must return a differentiable scalar.
    The reference is frozen at construction; it never receives gradients.
    """
    def __init__(self, policy, logprob: Callable, optimizer, beta: float = 0.01):
        if torch is None:
            raise RuntimeError("PyTorch is required for verifier GRPO")
        self.policy, self.logprob, self.optimizer, self.beta = policy, logprob, optimizer, beta
        self.reference = copy.deepcopy(policy).eval()
        for p in self.reference.parameters():
            p.requires_grad_(False)

    def step(self, group: Iterable[Rollout]) -> dict:
        group = list(group)
        if len({(r.spec, r.prompt) for r in group}) != 1:
            raise ValueError("an update must contain one spec and one identical prompt")
        usable = []
        for r in group:
            reward, tier = staircase_reward(r.verifier)
            if reward is not None:
                usable.append((r, reward, tier))
        if len(usable) < 2:
            return {"updated": False, "reason": "fewer_than_two_rewardable_rollouts"}
        rewards = torch.tensor([x[1] for x in usable], dtype=torch.float32)
        std = rewards.std(unbiased=False)
        if float(std) == 0.0:
            return {"updated": False, "reason": "zero_reward_variance", "zero_std": 1.0}
        advantages = (rewards - rewards.mean()) / (std + 1e-6)
        current = torch.stack([self.logprob(self.policy, x[0].prompt, x[0].tokens) for x in usable])
        advantages = advantages.to(current.device)
        with torch.no_grad():
            ref = torch.stack([self.logprob(self.reference, x[0].prompt, x[0].tokens) for x in usable])
        # Group-normalized REINFORCE with squared log-probability regularization.
        # This squared term is not a KL divergence or a PPO clipped objective.
        loss = -(advantages * current).mean() + self.beta * ((current - ref) ** 2).mean()
        before = [p.detach().clone() for p in self.policy.parameters()]
        self.optimizer.zero_grad(set_to_none=True)
        loss.backward()
        self.optimizer.step()
        delta = sum(float(((p.detach() - old) ** 2).sum())
                    for p, old in zip(self.policy.parameters(), before)) ** .5
        tiers = [x[2] for x in usable]
        return {"updated": True, "loss": float(loss.detach()), "reward_std": float(std),
                "zero_std": 0.0, "parameter_delta_norm": delta,
                "tiers": {t: tiers.count(t) for t in sorted(set(tiers))}}

    def save(self, directory: Path, metadata: dict) -> Path:
        directory.mkdir(parents=True, exist_ok=True)
        target = directory / "verifier_grpo.pt"
        if target.exists():
            raise FileExistsError(f"refusing to overwrite checkpoint: {target}")
        torch.save({"policy": self.policy.state_dict(),
                    "reference": self.reference.state_dict(),
                    "optimizer": self.optimizer.state_dict(), "metadata": metadata}, target)
        (directory / "metadata.json").write_text(json.dumps(metadata, indent=2, sort_keys=True))
        return target


def rollout_digest(group: Iterable[Rollout]) -> str:
    """Stable identity recorded with a checkpoint; prevents silent replay mixing."""
    body = "\n".join(f"{r.spec}\0{r.prompt}\0{r.tokens}" for r in group)
    return hashlib.sha256(body.encode()).hexdigest()
