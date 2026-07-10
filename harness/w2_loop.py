"""W2.2 -- the RFT generation ("Ralph") loop.

Design: docs/superpowers/specs/2026-07-09-w21-quality-corpus-design.md,
Workstream 2. Per gold seed spec: spec -> NL (back-translation) -> the NL
becomes a generation seed -> NL -> spec' (property-frozen generation, gated
by SANY + non-vacuous TLC + the deterministic mutation battery), iterating
with repair-context feedback up to max_iters. Survivors re-pass decontam
before being recorded.

Model calls go through the same `Model` interface as harness.repair
(`.generate(prompt, n, temperature, max_tokens) -> list[str]`) -- this module
never talks to a model directly; the caller injects a Model (real or fake),
which is what keeps every test in test_w2_loop.py free of live Sophia spend.

Reuses (does not modify):
  harness.runner       check_sany, check_tlc, module_name, vacuity_flags (via check_tlc)
  harness.mutation      run_mutation_on_module
  harness.adequacy      structural_features, complexity_score, quality_label
  harness.corpora       shingle_set, normalize_tla, nearest_similarity, SHINGLE_K,
                        NEAR_DUP_THRESHOLD
  harness.w21_funnel    load_canonical (decontam corpus: bench + examples;
                        holdout-30 is a subset of bench, see project memory)
  harness.gen_eval      extract_module (module-block extraction reused, not
                        rewritten -- extract_module_and_cfg below layers a cfg
                        block extraction on top of it)

CLI:
  python3 -m harness.w2_loop --seeds data/chattla-corpora-v2/manifest_w2_seeds.jsonl \\
      --raw /Users/eric/GitHub/tla-dataset-pipeline/data/raw \\
      --run-dir results/runs/w2-<date> [--seed-cap N] [--k N] [--model NAME] [--dry-run]
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
from pathlib import Path

from .adequacy import complexity_score, structural_features
from .corpora import NEAR_DUP_THRESHOLD, SHINGLE_K, nearest_similarity, normalize_tla, shingle_set
from .gen_eval import extract_module
from .mutation import run_mutation_on_module
from .runner import check_sany, check_tlc, module_name

DEFAULT_MAX_ITERS = 8
DEFAULT_TIMEOUT_S = 90


# --------------------------------------------------------------- prompts

def backtranslate_prompt(spec_text: str, cfg_text: str) -> str:
    """Stage 1: spec -> NL back-translation prompt. Asks the model for a
    precise natural-language system description (including the safety
    property) with NO TLA+ syntax in the reply -- the NL becomes a
    generation seed later, so it must stand alone as an English spec."""
    return (
        "You are given a verified TLA+ specification and its TLC model-checker "
        "configuration below. Write a precise NATURAL LANGUAGE description of "
        "the system it models: what the variables represent, what each action "
        "does, and what the safety property (the invariant) guarantees. "
        "Do NOT use any TLA+ syntax, operators, or code in your answer -- plain "
        "English only, as if briefing an engineer who will re-implement the "
        "system from your description alone.\n\n"
        "===BEGIN SPEC===\n" + spec_text + "\n===END SPEC===\n\n"
        "===BEGIN CFG===\n" + cfg_text + "\n===END CFG===\n\n"
        "Natural language description:"
    )


_FENCE_RE = re.compile(r"```(?:\w+)?\n(.*?)```", re.S)


def parse_nl(reply: str) -> str:
    """Extract the natural-language description from a back-translation
    reply, stripping markdown fences if the model wrapped its answer in one."""
    m = _FENCE_RE.search(reply)
    text = m.group(1) if m else reply
    return text.strip()


def generation_prompt(nl_description: str, module_name: str, error_context: str | None = None) -> str:
    """Stage 2: NL -> spec' generation prompt (property-freeze -> gen). The
    model MUST emit both a TLA+ module AND its .cfg in one reply -- the
    simplest honest contract for a spec that needs a .cfg to TLC-check.
    error_context, if given, is prior-iteration SANY/TLC evidence fed back as
    repair context (Ralph-loop iteration)."""
    parts = [
        "Write a TLA+ specification that implements EXACTLY the system "
        "described below, and a TLC .cfg to model-check it. The system's "
        "safety property described in the NL text must be captured as a real, "
        "non-trivial INVARIANT (not `Inv == TRUE`) in the .cfg.\n\n"
        f"Name the module `{module_name}`.\n\n"
        "===BEGIN NATURAL LANGUAGE DESCRIPTION===\n" + nl_description +
        "\n===END NATURAL LANGUAGE DESCRIPTION===\n\n"
        "Reply with exactly one TLA+ module in a ```tla fenced block and "
        "exactly one .cfg in a ```cfg fenced block."
    ]
    if error_context:
        parts.append(
            "\n\nYour previous attempt failed verification. Fix it using this "
            "error evidence:\n" + error_context
        )
    return "\n".join(parts)


_CFG_FENCE_RE = re.compile(r"```cfg\n(.*?)```", re.S)
_ANY_FENCE_RE = re.compile(r"```(?:\w+)?\n(.*?)```", re.S)


def extract_module_and_cfg(reply: str):
    """Pull (module_text, cfg_text) out of a generation reply. Module
    extraction reuses harness.gen_eval.extract_module (not rewritten). cfg
    extraction looks for a ```cfg fenced block first, falling back to any
    fenced block that looks like a TLC config (has an INIT/NEXT/SPECIFICATION
    line) and isn't the module block itself."""
    mod = extract_module(reply)
    cfg_m = _CFG_FENCE_RE.search(reply)
    if cfg_m:
        return mod, cfg_m.group(1).strip()
    for m in _ANY_FENCE_RE.finditer(reply):
        block = m.group(1).strip()
        if mod and block == mod:
            continue
        if re.search(r"^\s*(INIT|NEXT|SPECIFICATION|INVARIANT)\b", block, re.M):
            return mod, block
    return mod, None


# --------------------------------------------------------------- loop

def _evidence(sany_out: str | None, tlc_status: str | None, tlc_out: str | None,
              vac: list | None, note: str | None = None) -> str:
    parts = []
    if note:
        parts.append(note)
    if sany_out is not None:
        parts.append("SANY output (truncated):\n" + sany_out[-1500:])
    if tlc_status is not None:
        parts.append(f"TLC status: {tlc_status}")
        if tlc_out:
            parts.append("TLC output (truncated):\n" + tlc_out[-1500:])
    if vac:
        parts.append("Vacuity flags: " + ", ".join(vac))
    return "\n".join(parts)


def run_loop_for_seed(model, nl: str, module_name_: str, workdir: Path, timeout: int,
                       max_iters: int = DEFAULT_MAX_ITERS) -> dict:
    """Property-freeze the NL (it is passed in already frozen -- the caller
    generates it once via backtranslate_prompt/parse_nl and reuses it across
    all iters of this seed) and iterate: generate -> SANY -> TLC (needs a
    cfg the model must emit) -> vacuity/thin gates -> deterministic mutation
    battery (recorded, NOT hard-gated per the reward-not-gate decision) ->
    converged survivor or iterate with error evidence fed back as repair
    context. Returns a result dict; see module docstring for reuse contract."""
    # MUST be absolute: check_sany/check_tlc build java-side paths (jtmp,
    # -metadir) from this dir; with a relative workdir SANY's module search
    # path resolves against a doubled prefix and even standard modules
    # (Naturals) come back fail_missing_module. Found live: first Sophia smoke
    # was 0/5 all-sany_fail purely from this (the specs were SANY-clean).
    workdir = Path(workdir).resolve()
    workdir.mkdir(parents=True, exist_ok=True)
    error_context = None
    last_reason = "unknown"

    for it in range(1, max_iters + 1):
        prompt = generation_prompt(nl, module_name_, error_context=error_context)
        [reply] = model.generate(prompt, 1, 0.8, 8192)
        mod_text, cfg_text = extract_module_and_cfg(reply)

        if mod_text is None:
            last_reason = "no_module_in_reply"
            error_context = _evidence(None, None, None, None,
                                       note="Your reply did not contain a parseable "
                                            "```tla fenced module block. Emit exactly one.")
            continue
        if cfg_text is None:
            last_reason = "no_cfg_in_reply"
            error_context = _evidence(None, None, None, None,
                                       note="Your reply did not contain a parseable "
                                            "```cfg fenced .cfg block. Emit exactly one.")
            continue

        mod = module_name(mod_text) or module_name_
        iter_dir = workdir / f"iter{it}"
        if iter_dir.exists():
            shutil.rmtree(iter_dir)
        iter_dir.mkdir(parents=True)
        tla_path = iter_dir / f"{mod}.tla"
        cfg_path = iter_dir / f"{mod}.cfg"
        tla_path.write_text(mod_text)
        cfg_path.write_text(cfg_text)

        sany_status, sany_out, _ = check_sany(tla_path, iter_dir, timeout)
        if sany_status != "pass":
            last_reason = f"sany_{sany_status}"
            error_context = _evidence(sany_out, None, None, None,
                                       note=f"SANY {sany_status}.")
            continue

        tlc_status, vac, tlc_out, _ = check_tlc(mod, cfg_text, iter_dir, timeout)
        if tlc_status != "pass":
            last_reason = f"tlc_{tlc_status}"
            error_context = _evidence(sany_out, tlc_status, tlc_out, None)
            continue

        distinct_states = None
        m = re.search(r"(\d+) distinct states found", tlc_out)
        if m:
            distinct_states = int(m.group(1))

        if vac:
            last_reason = "vacuous: " + ", ".join(vac)
            error_context = _evidence(sany_out, tlc_status, tlc_out, vac,
                                       note="The spec passed TLC but is vacuous "
                                            "(trivial invariant, no real property "
                                            "checked, or a degenerate state space). "
                                            "Fix the invariant/property to be real "
                                            "and meaningful.")
            continue
        if distinct_states is not None and distinct_states < 3:
            last_reason = f"thin_model: {distinct_states} states"
            error_context = _evidence(sany_out, tlc_status, tlc_out, vac,
                                       note=f"Only {distinct_states} distinct states "
                                            "were generated -- the model is too thin. "
                                            "Add real behavioral variety.")
            continue

        # converged: run the deterministic mutation battery for reward
        # weighting (recorded, NOT a hard gate -- Eric's 2026-07-10 decision).
        mut = run_mutation_on_module(tla_path, cfg_text, mod, timeout)
        safety_catch_rate = mut.get("safety_catch_rate")

        features = structural_features(mod_text)
        cscore = complexity_score(features)
        reward_weight = round(cscore * (1 + (safety_catch_rate or 0.0)), 3)

        return {
            "survived": True, "iters": it, "spec_text": mod_text, "cfg_text": cfg_text,
            "module": mod, "distinct_states": distinct_states, "vacuity": vac,
            "safety_catch_rate": safety_catch_rate, "kill_rate": mut.get("kill_rate"),
            "mutants_attempted": mut.get("attempted"),
            "features": features, "complexity_score": cscore,
            "reward_weight": reward_weight, "rejection_reason": None,
        }

    return {
        "survived": False, "iters": max_iters, "spec_text": None, "cfg_text": None,
        "module": module_name_, "distinct_states": None, "vacuity": None,
        "safety_catch_rate": None, "kill_rate": None, "mutants_attempted": None,
        "features": None, "complexity_score": None, "reward_weight": None,
        "rejection_reason": last_reason,
    }


# --------------------------------------------------------------- decontam

def decontam_survivor(spec_text: str, canon: dict):
    """Jaccard-vs-canonical decontam gate for a survivor (design: >= 0.65 vs
    the 206-corpus + tlaplus/examples + holdout-30 -- holdout-30 is a subset
    of the bench corpus, per project memory, so load_canonical's bench sweep
    already covers it). Returns (verdict, score)."""
    q = shingle_set(normalize_tla(spec_text), SHINGLE_K)
    _, score = nearest_similarity(q, canon)
    verdict = "rejected_contaminated" if score >= NEAR_DUP_THRESHOLD else "clean"
    return verdict, score


# --------------------------------------------------------------- driver

def _seed_key(source: str, k: int) -> str:
    return f"{source}::k{k}"


def run_w2(model, seeds_path: Path, raw: Path, run_dir: Path, seed_cap: int | None,
           k: int, timeout: int, max_iters: int, canon: dict | None = None):
    """Resumable driver: run_dir/w2_attempts.jsonl (every attempt, survived or
    not) + run_dir/w2_survivors.jsonl (decontam-clean survivors only). Skips
    seed x k keys already present in the attempts ledger so a restart resumes.
    Prints the yield rate (survivors / attempts) prominently."""
    from .w21_funnel import load_canonical

    run_dir = Path(run_dir)
    run_dir.mkdir(parents=True, exist_ok=True)
    seeds = [json.loads(l) for l in open(seeds_path) if l.strip()]
    if seed_cap:
        seeds = seeds[:seed_cap]

    attempts_path = run_dir / "w2_attempts.jsonl"
    survivors_path = run_dir / "w2_survivors.jsonl"
    done = set()
    if attempts_path.exists():
        done = {json.loads(l)["seed_key"] for l in open(attempts_path)}

    if canon is None:
        canon = load_canonical()

    n_attempts_this_run = 0
    n_survivors_this_run = 0

    with open(attempts_path, "a") as af, open(survivors_path, "a") as sf:
        for seed in seeds:
            source = seed["source"]
            for ki in range(k):
                key = _seed_key(source, ki)
                if key in done:
                    continue

                rel = source.removeprefix("data/raw/")
                spec_path = raw / rel
                spec_text = spec_path.read_text(errors="replace")
                cfg_candidates = list(spec_path.parent.glob("*.cfg"))
                cfg_path = next((c for c in cfg_candidates if c.stem == seed.get("module")), None) \
                    or (cfg_candidates[0] if cfg_candidates else None)
                cfg_text = cfg_path.read_text(errors="replace") if cfg_path else ""

                [nl_reply] = model.generate(backtranslate_prompt(spec_text, cfg_text), 1, 0.8, 4096)
                nl = parse_nl(nl_reply)

                workdir = run_dir / "work" / f"{seed.get('module', 'seed')}_k{ki}"
                result = run_loop_for_seed(model, nl, seed.get("module", "Gen"), workdir,
                                            timeout=timeout, max_iters=max_iters)

                attempt_row = {"seed_key": key, "source": source, "k": ki, "nl": nl,
                                **{k2: v for k2, v in result.items() if k2 != "spec_text"}}

                if result["survived"]:
                    verdict, score = decontam_survivor(result["spec_text"], canon)
                    attempt_row["decontam_verdict"] = verdict
                    attempt_row["decontam_similarity"] = score
                    if verdict == "clean":
                        sf.write(json.dumps({**result, "seed_key": key, "source": source,
                                              "k": ki, "nl": nl,
                                              "decontam_verdict": verdict,
                                              "decontam_similarity": score}) + "\n")
                        sf.flush()
                        n_survivors_this_run += 1
                    else:
                        attempt_row["survived"] = False
                        attempt_row["rejection_reason"] = "contaminated"

                af.write(json.dumps(attempt_row) + "\n")
                af.flush()
                n_attempts_this_run += 1

    total_attempts = sum(1 for _ in open(attempts_path))
    total_survivors = sum(1 for _ in open(survivors_path))
    rate = (total_survivors / total_attempts) if total_attempts else 0.0
    print(f"W2 loop: {n_attempts_this_run} attempts this run, {n_survivors_this_run} survivors this run")
    print(f"YIELD RATE (survivors/attempts, cumulative): {total_survivors}/{total_attempts} = {rate:.3f}")


# --------------------------------------------------------------- dry-run model

class DryRunModel:
    """Canned fake model for --dry-run: exercises the whole pipeline (real
    SANY/TLC/mutation/decontam gates) with zero API spend. Alternates a
    plausible NL back-translation reply with a small, always-valid generated
    module+cfg so the loop converges on iter 1 for any seed."""
    id = "dry-run-canned-v1"

    _NL = ("A bounded resource counter. A single integer variable tracks how "
           "many units are currently allocated, starting at zero. Two actions "
           "are possible at each step: allocate one more unit, or release one "
           "unit, but release is only permitted while the count is already at "
           "least one greater than zero so the count never goes negative. "
           "Safety property: the allocated count is always non-negative.")

    _MODULE = """---- MODULE {mod} ----
EXTENDS Integers
VARIABLE cnt
Init == cnt = 0
Alloc == cnt < 3 /\\ cnt' = cnt + 1
Release == cnt > 0 /\\ cnt' = cnt - 1
Next == Alloc \\/ Release
Spec == Init /\\ [][Next]_cnt
NonNegative == cnt >= 0
====
"""
    _CFG = "INIT Init\nNEXT Next\nINVARIANT NonNegative\n"

    def generate(self, prompt, n, temperature, max_tokens):
        if "NATURAL LANGUAGE DESCRIPTION" in prompt:
            mmod = re.search(r"Name the module `(\w+)`", prompt)
            mod = mmod.group(1) if mmod else "Gen"
            reply = (f"```tla\n{self._MODULE.format(mod=mod)}\n```\n"
                     f"```cfg\n{self._CFG}\n```\n")
        else:
            reply = f"Natural language description:\n\n```\n{self._NL}\n```\n"
        return [reply] * n


def main():
    ap = argparse.ArgumentParser(prog="harness.w2_loop")
    ap.add_argument("--seeds", type=Path,
                    default=Path("/Users/eric/GitHub/prove-TLA/data/chattla-corpora-v2/manifest_w2_seeds.jsonl"))
    ap.add_argument("--raw", type=Path,
                    default=Path("/Users/eric/GitHub/tla-dataset-pipeline/data/raw"))
    ap.add_argument("--run-dir", required=True, type=Path)
    ap.add_argument("--seed-cap", type=int, default=500)
    ap.add_argument("--k", type=int, default=1)
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT_S)
    ap.add_argument("--max-iters", type=int, default=DEFAULT_MAX_ITERS)
    ap.add_argument("--model", default=None,
                    help="anthropic|anthropic:<id>|openai:<id>|stub (harness.repair.make_model)")
    ap.add_argument("--dry-run", action="store_true",
                    help="use the built-in canned DryRunModel, zero API spend")
    a = ap.parse_args()

    if a.dry_run:
        model = DryRunModel()
    else:
        if not a.model:
            raise SystemExit("--model is required unless --dry-run is given")
        from .repair import make_model
        model = make_model(a.model)

    run_w2(model, a.seeds, a.raw, a.run_dir, seed_cap=a.seed_cap, k=a.k,
           timeout=a.timeout, max_iters=a.max_iters)


if __name__ == "__main__":
    main()
