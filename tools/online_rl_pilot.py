#!/usr/bin/env python3
"""Bounded real-Qwen online REINFORCE on a one-token TLA syntax repair.

This trains a real LM, but is a curriculum/mechanics pilot, not full-spec or
theorem-proving training. TLC is observed only; reward is explicitly SANY-only.
Every inserted byte comes from the sampled token, without cleanup or retries.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import sys
import time

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=int, default=4)
    parser.add_argument("--group-size", type=int, default=16)
    parser.add_argument("--seed", type=int, default=20260905)
    parser.add_argument("--lr", type=float, default=2e-5)
    parser.add_argument("--seconds", type=int, default=480)
    parser.add_argument("--model-path", type=Path)
    parser.add_argument("--device", choices=["cpu", "mps", "cuda"])
    parser.add_argument("--output", type=Path)
    parser.add_argument("--holdout-corpus", type=Path,
                        default=Path("/Users/eric/GitHub/tla_benchmark/data/tla_files"))
    args = parser.parse_args()
    assert 1 <= args.steps <= 20 and 2 <= args.group_size <= 32
    os.environ.update(HF_HUB_OFFLINE="1", TRANSFORMERS_OFFLINE="1",
                      TOKENIZERS_PARALLELISM="false")
    import torch
    import transformers
    from transformers import AutoModelForCausalLM, AutoTokenizer
    from harness.corpora import normalize_tla, shingle_set, jaccard
    from harness.runner import check_sany, check_tlc, module_name

    started = time.monotonic()
    rundir = args.output or REPO / "results/runs" / time.strftime("online-rl-qwen-syntax-%Y%m%d-%H%M%S")
    rundir.mkdir(exist_ok=False)
    (rundir / "trainer.py").write_text(Path(__file__).read_text())
    print(f"RUN_DIR={rundir}", flush=True)
    source = REPO / "data/chattla-corpora-v3-wide/tier3_tlc/CAPHTECH/kiri/docs/formal/AdaptiveK.tla"
    original = source.read_text()
    cfg = source.with_suffix(".cfg").read_text()
    manifest = next(json.loads(s) for s in (REPO / "data/chattla-corpora-v3-wide/manifest_tier3_tlc.jsonl").read_text().splitlines()
                    if json.loads(s)["module"] == "AdaptiveK")
    assert manifest["decontam_verdict"] == "clean"
    assert hashlib.sha256(source.read_bytes()).hexdigest() == manifest["content_sha256"]
    holdout_path = REPO / "corpus/holdout_30.json"
    holdout = json.loads(holdout_path.read_text())["holdout_specs"]
    shingles = shingle_set(normalize_tla(original))
    overlaps = {}
    for num in holdout:
        held = args.holdout_corpus / f"{num}.tla"
        held_text = held.read_text()
        assert module_name(held_text) != "AdaptiveK"
        overlaps[str(num)] = jaccard(shingles, shingle_set(normalize_tla(held_text)))
    assert max(overlaps.values()) < 0.65
    prefix, suffix = original.split('THEN', 1)
    prompt = ('Fill the missing TLA+ keyword in this expression. Reply with only the keyword, '
              'without explanation or punctuation.\n'
              'AdaptiveK(cat) == IF cat = "bugfix" [HOLE] K_BUGFIX ELSE K_DEFAULT\n')
    cache = Path.home() / ".cache/huggingface/hub/models--Qwen--Qwen2.5-0.5B-Instruct/snapshots"
    snapshot = args.model_path or sorted(p for p in cache.glob("*") if (p / "model.safetensors").exists())[-1]
    device = args.device or ("mps" if torch.backends.mps.is_available() else "cpu")
    if device == "cuda":
        torch.cuda.reset_peak_memory_stats()
    torch.set_num_threads(4)
    torch.manual_seed(args.seed)
    tokenizer = AutoTokenizer.from_pretrained(snapshot, local_files_only=True)
    exact_keyword_tokens = [i for i in range(len(tokenizer))
                            if tokenizer.decode([i], skip_special_tokens=False).strip() == "THEN"]
    net = AutoModelForCausalLM.from_pretrained(snapshot, local_files_only=True,
                                              torch_dtype=torch.float32).to(device).eval()
    for parameter in net.parameters():
        parameter.requires_grad_(False)
    for parameter in net.model.layers[-1].parameters():
        parameter.requires_grad_(True)
    trainable = {n: p for n, p in net.named_parameters() if p.requires_grad}
    optimizer = torch.optim.AdamW(trainable.values(), lr=args.lr, weight_decay=0.0)
    # Raw causal source completion avoids the tiny instruct model copying a
    # literal [HOLE] marker instead of answering. No reference token is supplied.
    rendered = prefix.rstrip()
    inputs = tokenizer(rendered, return_tensors="pt").to(device)
    config = {**{k: str(v) if isinstance(v, Path) else v for k, v in vars(args).items()}, "scope": "one-token repair of one training-source keyword; SANY partial reward only",
              "model": str(snapshot), "device": device, "dtype": "float32", "source": str(source),
              "torch_version": torch.__version__, "transformers_version": transformers.__version__,
              "source_manifest": manifest, "holdout_sha256": hashlib.sha256(holdout_path.read_bytes()).hexdigest(),
              "trainer_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "holdout_jaccard": overlaps, "prompt": prompt, "rendered_prompt": rendered,
              "prompt_token_ids": inputs.input_ids[0].tolist(), "trainable_names": list(trainable),
              "trainable_parameters": sum(p.numel() for p in trainable.values()),
              "sampling": "full-vocabulary categorical, temperature=1, top_k=0, one token",
              "reward": "0.60 if actual SANY passes, 0.25 if actual SANY rejects; infrastructure excluded; TLC never rewarded",
              "algorithm": "on-policy group-normalized REINFORCE, one update per fresh group, no KL term"}
    config["diversity_guard_scope"] = "One-token curriculum has naturally repeated keywords; full-spec duplicate threshold is inapplicable. Entropy and unique tokens are reported."
    dump(rundir / "config.json", config)
    (rundir / "source.tla").write_text(original)
    (rundir / "source.cfg").write_text(cfg)
    initial = {n: p.detach().cpu().clone() for n, p in trainable.items()}
    metrics = []
    for step in range(args.steps + 1):
        if time.monotonic() - started > args.seconds:
            break
        with torch.no_grad():
            logits = net(**inputs).logits[0, -1].float()
            probs = logits.softmax(-1)
            tokens = torch.multinomial(probs, args.group_size, replacement=True)
            entropy = float(-(probs * logits.log_softmax(-1)).sum())
            behavior_logp = logits.log_softmax(-1)[tokens].cpu().tolist()
            exact_keyword_probability = float(probs[exact_keyword_tokens].sum())
        rewards, usable_indices = [], []
        samples = []
        for sample_index, token in enumerate(tokens.tolist()):
            if time.monotonic() - started > args.seconds:
                break
            token_text = tokenizer.decode([token], skip_special_tokens=False)
            candidate = prefix + token_text + suffix
            work = rundir / f"step-{step:02d}" / f"sample-{sample_index:02d}"
            work.mkdir(parents=True)
            path = work / "AdaptiveK.tla"
            path.write_text(candidate)
            (work / "AdaptiveK.cfg").write_text(cfg)
            sany, sany_log, sany_s = check_sany(path, work, timeout=10)
            (work / "sany.log").write_text(sany_log)
            tlc, vacuity, tlc_s = None, None, None
            if sany == "pass":
                tlc, vacuity, tlc_log, tlc_s = check_tlc("AdaptiveK", cfg, work, timeout=10)
                (work / "tlc.log").write_text(tlc_log)
            reward = .60 if sany == "pass" else (.25 if sany == "fail" else None)
            if reward is not None:
                usable_indices.append(sample_index)
                rewards.append(reward)
            row = {"step": step, "sample": sample_index, "token_id": token, "text": token_text,
                   "behavior_logp": behavior_logp[sample_index], "sany": sany, "tlc": tlc,
                   "tlc_vacuity": vacuity, "sany_s": sany_s, "tlc_s": tlc_s, "reward": reward,
                   "semantic_audit": "exact_source_identity" if candidate == original else "unreviewed",
                   "terminal_pass_reward": False, "candidate_sha256": hashlib.sha256(candidate.encode()).hexdigest()}
            samples.append(row)
            with (rundir / "rollouts.jsonl").open("a") as stream:
                stream.write(json.dumps(row) + "\n")
        reward_tensor = torch.tensor(rewards, device=device)
        std = float(reward_tensor.std(unbiased=False)) if rewards else 0.0
        metric = {"step": step, "evaluation_only": step == args.steps, "entropy_nats": entropy,
                  "reward_std": std, "zero_variance": std < 1e-7, "updated": False,
                  "sany_pass": sum(r["sany"] == "pass" for r in samples), "n": len(samples),
                  "mean_reward": sum(rewards) / len(rewards) if rewards else None,
                  "exact_keyword_probability": exact_keyword_probability,
                  "unique_tokens": len(set(tokens.tolist()))}
        if std >= 1e-7 and len(rewards) > 1 and step < args.steps:
            advantage = (reward_tensor - reward_tensor.mean()) / reward_tensor.std(unbiased=False)
            optimizer.zero_grad(set_to_none=True)
            current_logits = net(**inputs).logits[0, -1].float()
            chosen_logp = current_logits.log_softmax(-1)[tokens[usable_indices]]
            # All completions have one token and one prompt; a single forward
            # computes the exact group objective without sequence padding.
            loss = -(advantage.detach() * chosen_logp).mean()
            loss.backward()
            norm = torch.nn.utils.clip_grad_norm_(trainable.values(), 1.0)
            optimizer.step()
            metric.update(updated=True, loss=float(loss.detach()), gradient_norm=float(norm))
        metrics.append(metric)
        print(json.dumps(metric), flush=True)
        dump(rundir / "metrics.json", metrics)
    state = {n: p.detach().cpu().clone() for n, p in trainable.items()}
    delta = sum(float(((state[n] - initial[n]) ** 2).sum()) for n in state) ** .5
    checkpoint = rundir / "policy_optimizer.pt"
    torch.save({"trainable_state": state, "optimizer": optimizer.state_dict(), "config": config,
                "torch_rng_state": torch.get_rng_state(), "metrics": metrics}, checkpoint)
    loaded = torch.load(checkpoint, map_location="cpu", weights_only=False)
    with torch.no_grad():
        before_reload = net(**inputs).logits[0, -1].detach().cpu()
        for p in trainable.values():
            p.zero_()
        for name, p in trainable.items():
            p.copy_(loaded["trainable_state"][name].to(device))
        optimizer.load_state_dict(loaded["optimizer"])
        after_reload = net(**inputs).logits[0, -1].detach().cpu()
    assert torch.equal(before_reload, after_reload), "checkpoint reload changed model output"
    assert all(torch.equal(p.detach().cpu(), loaded["trainable_state"][n]) for n, p in trainable.items())
    report = {"scope": config["scope"], "run_dir": str(rundir), "elapsed_s": time.monotonic() - started,
              "optimizer_steps": sum(m["updated"] for m in metrics), "parameter_delta_norm": delta,
              "checkpoint": str(checkpoint), "reload_logits_exact": True,
              "optimizer_state_entries": len(optimizer.state), "metrics": metrics,
              "generalization_measured": False, "full_spec_generation_measured": False}
    if device == "cuda":
        report["memory_bytes"] = {"cuda_peak_allocated": torch.cuda.max_memory_allocated(),
                                  "cuda_peak_reserved": torch.cuda.max_memory_reserved(),
                                  "cuda_current_allocated": torch.cuda.memory_allocated()}
    elif device == "mps":
        report["memory_bytes"] = {"mps_current_allocated": torch.mps.current_allocated_memory(),
                                  "mps_driver_allocated": torch.mps.driver_allocated_memory(),
                                  "note": "MPS API reports current allocation; this is not a measured peak."}
    dump(rundir / "summary.json", report)
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
