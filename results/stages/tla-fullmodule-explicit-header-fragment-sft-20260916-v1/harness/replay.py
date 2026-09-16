"""Replay one ledgered sample at its recorded decoder seed and diff the result.

`harness replay <run-dir> --spec N --sample S [--framing A|B]`

Turns "the same model gave a different answer" into a command. The run that
motivated this (docs/designs/2026-08-08-decode-provenance-design.md) is spec 30
going 5 passes -> 1 pass between gate2-w4dg-120b-A and -A3 on a byte-identical
prompt, which could not be reproduced because no seed was ever sent.

The prompt is REBUILT from the corpus rather than read from the ledger (rows
store prompt_sha256, not the prompt text), and the rebuilt hash is checked
against the stored one BEFORE any API call. A mismatch means the corpus or a
prompt template moved since the run, which makes replay meaningless -- that is
reported as PROMPT_DRIFT and is a free corpus-drift detector.

Verdicts:
  IDENTICAL        replay produced byte-identical text
  DIVERGENT        replay differed (expected on a shared vLLM: continuous
                   batching changes float reduction order, so a seed pins the
                   sampling RNG but not the numerics)
  PROMPT_DRIFT     rebuilt prompt != recorded prompt; no request was made
  SEED_UNSUPPORTED the row carries no decoder seed (a pre-provenance run, or an
                   Anthropic row); replay cannot be meaningful
  NO_CANDIDATE     the row has no stored candidate to diff against
"""
import difflib
import hashlib
import json
from pathlib import Path

from .decoding import derive_seed, generate_traced_compat
from .gen_eval import (MAX_TOKENS, TEMPERATURE, _corruption_for_spec, _resolve_cfg,
                       build_generation_prompt, build_repair_prompt,
                       canonical_spec_text, corruption_seed, extract_module,
                       holdout_specs_and_hash)
from .repair import make_model
from .runner import REPO, build_module_index


def _load_row(run_dir: Path, spec: str, sample, framing=None):
    rows_path = run_dir / "rows.jsonl"
    if not rows_path.exists():
        raise SystemExit(f"no rows.jsonl in {run_dir}")
    matches = []
    for line in rows_path.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        if str(row.get("spec")) != str(spec):
            continue
        if str(row.get("sample")) != str(sample):
            continue
        if framing and row.get("framing") != framing:
            continue
        matches.append(row)
    if not matches:
        raise SystemExit(f"no row for spec={spec} sample={sample} "
                         f"{'framing=' + framing if framing else ''} in {rows_path}")
    if len({r.get("framing") for r in matches}) > 1:
        raise SystemExit(f"spec={spec} sample={sample} exists in both framings; "
                         "pass --framing A or B")
    # Rule 8 ledgers are append-only, so a resumed run can legitimately hold more
    # than one row for a pair. The last one is what the summary re-score used.
    return matches[-1]


def _rebuild_prompt(row, corpus: Path, run_dir: Path):
    """Reconstruct the exact prompt string the run sent, from the corpus."""
    num = str(row["spec"])
    num2mod, mod2path = build_module_index(corpus)
    cfg_dirs = [("override", REPO / "corpus" / "configs" / "overrides"),
                ("original", corpus / "cfg"),
                ("draft", REPO / "corpus" / "configs" / "drafts")]
    if row.get("framing") == "A":
        desc = json.loads((corpus / "descriptions" / f"{num}.json").read_text())
        cfg_text, _ = _resolve_cfg(num, cfg_dirs)
        mod = num2mod.get(num)
        if mod is None or cfg_text is None:
            raise SystemExit(f"spec {num}: module or cfg missing from corpus")
        return build_generation_prompt(desc, cfg_text, mod)

    # Framing B: the corruption is deterministic in (holdout hash, spec), but
    # regenerating it re-runs the scorer to pick a VALID corruption, so this is
    # slow. Correctness over speed: a reconstructed-by-hand corrupted module
    # would not carry the same error evidence, and the prompt hash would not
    # match anyway.
    _, holdout_hash = holdout_specs_and_hash()
    canonical = canonical_spec_text(num, corpus)
    seed = corruption_seed(holdout_hash, num)
    workroot = Path("/tmp/prove-tla-replay") / run_dir.name
    logdir = run_dir / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    corrupted, _record, evidence = _corruption_for_spec(
        num, canonical, seed, run_dir, corpus, num2mod, mod2path, cfg_dirs,
        workroot, logdir)
    if corrupted is None:
        raise SystemExit(f"spec {num}: corruption could not be regenerated")
    return build_repair_prompt(corrupted, evidence)


def replay(run_dir, spec, sample, framing=None, corpus=None, model_name=None):
    run_dir = Path(run_dir)
    row = _load_row(run_dir, spec, sample, framing)
    framing = row.get("framing")

    config_path = run_dir / "config.json"
    config = json.loads(config_path.read_text()) if config_path.exists() else {}
    corpus = Path(corpus or config.get("corpus") or "")
    if not corpus.is_dir():
        raise SystemExit(f"corpus dir not found: {corpus} (pass --corpus-data)")

    seed = row.get("decode_seed")
    if seed is None:
        # Pre-provenance rows predate this feature but the seed is DERIVED, so it
        # can still be recomputed -- it just was not the seed that run used.
        derived = derive_seed(config.get("run_id", run_dir.name), spec, framing,
                              row.get("sample"))
        return {"verdict": "SEED_UNSUPPORTED", "spec": spec, "sample": sample,
                "framing": framing,
                "note": ("row carries no decode_seed (pre-provenance run, or an "
                         "Anthropic row: the Messages API has no seed param). "
                         f"A replay today would use derived seed {derived}, which "
                         "is NOT what the original run sent."),
                "derived_seed": derived}

    prompt = _rebuild_prompt(row, corpus, run_dir)
    rebuilt_sha = hashlib.sha256(prompt.encode()).hexdigest()
    recorded_sha = row.get("prompt_sha256")
    if recorded_sha and rebuilt_sha != recorded_sha:
        return {"verdict": "PROMPT_DRIFT", "spec": spec, "sample": sample,
                "framing": framing, "recorded_prompt_sha256": recorded_sha,
                "rebuilt_prompt_sha256": rebuilt_sha,
                "note": ("the corpus or a prompt template changed since this run; "
                         "no request was made because a replay against a different "
                         "prompt measures nothing")}

    cand_rel = row.get("candidate_path")
    if not cand_rel:
        return {"verdict": "NO_CANDIDATE", "spec": spec, "sample": sample,
                "framing": framing,
                "note": "row stored no candidate (extraction failed at run time)"}
    stored = (run_dir / cand_rel).read_text()

    model = make_model(model_name or f"openai:{row['model']}")
    temperature = row.get("temperature",
                          0.0 if row.get("sample") == "greedy" else TEMPERATURE)
    text, meta = generate_traced_compat(
        model, prompt, 1, temperature, MAX_TOKENS, seed)[0]
    fresh = extract_module(text)

    if fresh is None:
        return {"verdict": "DIVERGENT", "spec": spec, "sample": sample,
                "framing": framing, "seed": seed,
                "note": "replay produced no extractable module; original did",
                "stored_sha256": hashlib.sha256(stored.encode()).hexdigest(),
                "replay_sha256": None}

    stored_sha = hashlib.sha256(stored.encode()).hexdigest()
    fresh_sha = hashlib.sha256(fresh.encode()).hexdigest()
    if stored_sha == fresh_sha:
        return {"verdict": "IDENTICAL", "spec": spec, "sample": sample,
                "framing": framing, "seed": seed, "stored_sha256": stored_sha,
                "replay_sha256": fresh_sha,
                "provider_seed_echo": meta.get("provider_seed_echo")}

    diff = "\n".join(difflib.unified_diff(
        stored.splitlines(), fresh.splitlines(),
        fromfile=f"stored/{cand_rel}", tofile="replay", lineterm=""))
    return {"verdict": "DIVERGENT", "spec": spec, "sample": sample,
            "framing": framing, "seed": seed, "stored_sha256": stored_sha,
            "replay_sha256": fresh_sha,
            "provider_seed_echo": meta.get("provider_seed_echo"),
            "diff": diff}


def run_replay_cli(run_dir, spec, sample, framing=None, corpus=None, model=None):
    sample = int(sample) if str(sample).isdigit() else sample
    report = replay(run_dir, spec, sample, framing, corpus, model)
    diff = report.pop("diff", None)
    print(json.dumps(report, indent=2))
    if diff:
        print("\n" + diff)
    return 0 if report["verdict"] == "IDENTICAL" else 1
