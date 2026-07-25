"""RFT corpus preparation: S2 collapse-check, S5 family tagging, harmony SFT
formatting.

These are the three items the 2026-07-10 quality audit deferred but flagged as
MUST-FIX before the next fine-tune / Gate-2 report:

  1. collapse_report -- are survivor specs structurally simpler than the
     holdout population (a sign RFT is rewarding trivial-but-valid specs)?
  2. tag_family -- deterministic keyword taxonomy so we can see which problem
     families the corpus covers vs. the holdout, and catch blind spots.
  3. to_harmony_sft / build_sft_file -- render survivor rows through the
     gpt-oss harmony chat template. The 2026-07-11 eval finding: plain-text
     SFT breaks harmony channel discipline. The critical property is that the
     assistant target lives in the FINAL channel, not the raw text -- that is
     exactly the discipline the last SFT run broke.

HARD METRICS ONLY. No LLM-judge anywhere in this module.
"""
from __future__ import annotations

import glob
import json
import re
import statistics
from pathlib import Path
from typing import Iterable

from harness.adequacy import structural_features, complexity_score

from harness import w4_corpus

# S2: survivor median complexity < COLLAPSE_RATIO * holdout median => flag.
# Design default -- revisit before freeze once we have more survivor volume.
COLLAPSE_RATIO = 0.5

# S5: fixed, documented taxonomy. Order matters -- first match wins. Keep this
# list in sync with the keyword groups below.
TAXONOMY_ORDER = [
    "consensus",
    "commit_protocols",
    "mutex_locks",
    "queues_buffers",
    "caches_memory",
    "clocks_time",
    "replication_storage",
    "network_channels",
    "counters_registers",
    "other",
]

_FAMILY_KEYWORDS = {
    "consensus": ["paxos", "raft", "quorum", "ballot", "leader elect"],
    "commit_protocols": ["two-phase", "two phase", "2pc", "transaction commit", "tcommit"],
    "mutex_locks": ["mutual exclusion", "mutex", "lock", "critical section", "peterson", "bakery"],
    "queues_buffers": ["queue", "fifo", "buffer", "producer", "consumer"],
    "caches_memory": ["cache", "coherence", "memory model"],
    "clocks_time": ["clock", "timestamp", "lamport", "vector clock"],
    "replication_storage": ["replica", "log replication", "kv", "storage", "percolator"],
    "network_channels": ["message", "channel", "gossip", "broadcast", "byzantine"],
    "counters_registers": ["counter", "register", "increment"],
}


def tag_family(nl_or_spec_text: str) -> str:
    """Deterministic keyword-based family classifier (S5). Case-insensitive
    substring match; first matching family in TAXONOMY_ORDER wins."""
    text = (nl_or_spec_text or "").lower()
    for family in TAXONOMY_ORDER:
        if family == "other":
            continue
        for kw in _FAMILY_KEYWORDS[family]:
            if kw in text:
                return family
    return "other"


# ---------------------------------------------------------------------------
# Survivor loading (shared by all three CLI subcommands)
# ---------------------------------------------------------------------------

def _resolve_dirs(survivor_dirs: Iterable) -> list[Path]:
    """Expand glob patterns (strings) and Path objects into a flat, deduped
    list of existing directories."""
    out: list[Path] = []
    seen = set()
    for entry in survivor_dirs:
        entry_str = str(entry)
        matches = glob.glob(entry_str) if any(c in entry_str for c in "*?[") else [entry_str]
        if not matches and not glob.has_magic(entry_str):
            matches = [entry_str]
        for m in matches:
            p = Path(m)
            if p.is_dir() and p not in seen:
                seen.add(p)
                out.append(p)
    return out


_W4_SHARD_RE = re.compile(r"^w4-opus-shard(\d+)$")


def load_survivors(survivor_dirs: Iterable, apply_exclusions: bool | None = None) -> list[dict]:
    """Load survived rows from w2_survivors.jsonl in each dir. Robust to
    missing files / empty dirs / malformed lines (skipped, not raised).

    W4 shard dirs are delegated to w4_corpus.load_effective(), so this returns
    byte-identical accounting to tools/w4_audit.py: excluded_seed_keys dropped,
    de-duplicated by seed_key in NUMERIC shard order, keep-last corrections
    honored, and rows with no explicit "survived" key treated as survivors.
    Rendering the W4 dirs without that produced 3 excluded keys, 65 duplicate
    seed_keys, an order-dependent choice of which duplicate won (glob order is
    lexical: shard1, shard10, shard100...), and dropped the 84 rows that carry
    no "survived" field -- 3,965 rows against the audit's 4,040.

    Non-W4 dirs keep the legacy path untouched. They have no exclusions ledger
    and no seed_key uniqueness contract: de-duplicating w2-gen-* would silently
    cut the frozen 260-survivor v2_sft2 corpus to 196.

    apply_exclusions: None (default) = auto-detect per directory. True/False
    force the W4 or legacy path for every directory.
    """
    dirs = _resolve_dirs(survivor_dirs)
    w4_shards, other_dirs = [], []
    for d in dirs:
        m = _W4_SHARD_RE.match(d.name)
        if m and apply_exclusions is not False:
            w4_shards.append((int(m.group(1)), d))
        else:
            other_dirs.append(d)
    if apply_exclusions is True and other_dirs:
        raise ValueError(
            "apply_exclusions=True but these dirs are not W4 shard dirs and have "
            f"no exclusions ledger: {[str(d) for d in other_dirs]}"
        )

    rows: list[dict] = []
    if w4_shards:
        runs_dirs = {d.parent for _, d in w4_shards}
        max_shard = max(s for s, _ in w4_shards)
        wanted = {d for _, d in w4_shards}
        for runs_dir in sorted(runs_dirs):
            for r in w4_corpus.load_effective(upto_shard=max_shard, runs_dir=runs_dir):
                if runs_dir / f"w4-opus-shard{r['_shard']}" in wanted:
                    rows.append(r)

    for d in other_dirs:
        f = d / "w2_survivors.jsonl"
        if not f.exists():
            continue
        with open(f) as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    row = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if row.get("survived"):
                    rows.append(row)
    return rows


# ---------------------------------------------------------------------------
# Holdout loading
# ---------------------------------------------------------------------------

def _canonical_spec_path(spec_num) -> Path:
    """Default resolver for a holdout spec's canonical .tla text. Overridden
    in tests via monkeypatch to point at a fixture dir instead of the real
    tla_benchmark checkout."""
    return Path("/Users/eric/GitHub/tla_benchmark/data/tla_files") / f"{spec_num}.tla"


def load_holdout_texts(holdout_corpus) -> dict:
    """holdout_corpus: path to a manifest json with a 'holdout_specs' list of
    spec numbers (e.g. corpus/holdout_30.json). Returns {spec_num: text} for
    specs whose canonical file is found on disk (missing files skipped)."""
    manifest = json.loads(Path(holdout_corpus).read_text())
    specs = manifest.get("holdout_specs", [])
    out = {}
    for n in specs:
        p = _canonical_spec_path(n)
        if p.exists():
            out[n] = p.read_text()
    return out


# ---------------------------------------------------------------------------
# S2 collapse-check
# ---------------------------------------------------------------------------

def _dist_stats(values: list[float]) -> dict:
    if not values:
        return {"median": None, "p25": None, "p75": None, "mean": None, "n": 0}
    values = sorted(values)
    return {
        "median": statistics.median(values),
        "p25": values[max(0, int(len(values) * 0.25) - 1)] if len(values) > 1 else values[0],
        "p75": values[min(len(values) - 1, int(len(values) * 0.75))],
        "mean": round(statistics.mean(values), 3),
        "n": len(values),
    }


_FEATURE_KEYS = [
    "num_variables", "num_definitions", "extends_depth", "num_disjuncts",
    "num_conjuncts", "temporal_op_count", "noncomment_loc", "comment_ratio",
]


def collapse_report(survivor_dirs: list, holdout_corpus) -> dict:
    """S2: compare complexity distributions of survivors vs. holdout-30
    canonical specs. Returns a JSON-able dict; collapse_flag = True if
    survivor median complexity_score < COLLAPSE_RATIO * holdout median."""
    survivors = load_survivors(survivor_dirs)
    holdout_texts = load_holdout_texts(holdout_corpus)

    survivor_scores = []
    survivor_feature_vals = {k: [] for k in _FEATURE_KEYS}
    for row in survivors:
        feats = row.get("features") or structural_features(row.get("spec_text", ""))
        score = row.get("complexity_score")
        if score is None:
            score = complexity_score(feats)
        survivor_scores.append(score)
        for k in _FEATURE_KEYS:
            if k in feats:
                survivor_feature_vals[k].append(feats[k])

    holdout_scores = []
    holdout_feature_vals = {k: [] for k in _FEATURE_KEYS}
    for text in holdout_texts.values():
        feats = structural_features(text)
        holdout_scores.append(complexity_score(feats))
        for k in _FEATURE_KEYS:
            holdout_feature_vals[k].append(feats[k])

    features_report = {}
    for k in _FEATURE_KEYS:
        s_stats = _dist_stats(survivor_feature_vals[k])
        h_stats = _dist_stats(holdout_feature_vals[k])
        ratio = None
        if s_stats["median"] is not None and h_stats["median"]:
            ratio = round(s_stats["median"] / h_stats["median"], 3) if h_stats["median"] else None
        features_report[k] = {"survivors": s_stats, "holdout": h_stats, "median_ratio": ratio}

    s_complexity = _dist_stats(survivor_scores)
    h_complexity = _dist_stats(holdout_scores)

    collapse_flag = False
    if s_complexity["median"] is not None and h_complexity["median"]:
        collapse_flag = s_complexity["median"] < COLLAPSE_RATIO * h_complexity["median"]

    return {
        "collapse_ratio_threshold": COLLAPSE_RATIO,
        "collapse_flag": collapse_flag,
        "survivor_count": len(survivors),
        "holdout_count": len(holdout_texts),
        "complexity_score": {"survivors": s_complexity, "holdout": h_complexity},
        "features": features_report,
    }


# ---------------------------------------------------------------------------
# S5 family tagging
# ---------------------------------------------------------------------------

def tag_corpus(survivor_dirs: list, holdout_corpus) -> dict:
    """Per-family counts for survivors and holdout + family overlap list.
    Also returns per-row tags for CLI to emit as JSONL."""
    survivors = load_survivors(survivor_dirs)
    holdout_texts = load_holdout_texts(holdout_corpus)

    survivor_tags = []
    survivor_counts: dict = {}
    for row in survivors:
        text = (row.get("nl") or "") + " " + (row.get("spec_text") or "")
        fam = tag_family(text)
        survivor_tags.append({"seed_key": row.get("seed_key"), "family": fam})
        survivor_counts[fam] = survivor_counts.get(fam, 0) + 1

    holdout_tags = []
    holdout_counts: dict = {}
    for spec_num, text in holdout_texts.items():
        fam = tag_family(text)
        holdout_tags.append({"spec": spec_num, "family": fam})
        holdout_counts[fam] = holdout_counts.get(fam, 0) + 1

    overlap = sorted(set(survivor_counts) & set(holdout_counts))

    return {
        "survivor_family_counts": survivor_counts,
        "holdout_family_counts": holdout_counts,
        "family_overlap": overlap,
        "survivor_tags": survivor_tags,
        "holdout_tags": holdout_tags,
    }


# ---------------------------------------------------------------------------
# Harmony SFT formatter
# ---------------------------------------------------------------------------

try:
    import openai_harmony  # type: ignore
    _HAVE_HARMONY = True
except ImportError:
    openai_harmony = None
    _HAVE_HARMONY = False


def _render_manual_harmony(user_text: str, target_text: str) -> str:
    """Faithful manual rendering of the gpt-oss harmony format when
    openai_harmony isn't installed. The critical property under test: the
    assistant target lives in the FINAL channel, wrapped by
    '<|channel|>final<|message|>' ... '<|return|>'."""
    return (
        "<|start|>user<|message|>" + user_text + "<|end|>"
        "<|start|>assistant<|channel|>final<|message|>" + target_text + "<|return|>"
    )


def _render_harmony(user_text: str, target_text: str) -> str:
    if _HAVE_HARMONY:
        # openai_harmony's official renderer -- delegate if present, but the
        # manual path is the one exercised in this environment (package not
        # installed). Kept generic so the module works either way.
        try:
            from openai_harmony import (
                Conversation, Message, Role, load_harmony_encoding,
                HarmonyEncodingName,
            )
            enc = load_harmony_encoding(HarmonyEncodingName.HARMONY_GPT_OSS)
            convo = Conversation.from_messages([
                Message.from_role_and_content(Role.USER, user_text),
                Message.from_role_and_content(Role.ASSISTANT, target_text).with_channel("final"),
            ])
            tokens = enc.render_conversation(convo)
            return enc.decode(tokens)
        except Exception:
            pass
    return _render_manual_harmony(user_text, target_text)


def _target_block(row: dict) -> str:
    spec_text = row.get("spec_text", "")
    cfg_text = row.get("cfg_text", "")
    return f"```tla\n{spec_text}\n```\n```cfg\n{cfg_text}\n```"


def to_harmony_sft(survivor_row: dict) -> dict:
    """Convert a w2 survivor row into a harmony-rendered training example.
    Returns {"text": <rendered>, "seed_key": ..., "family": ...}."""
    user_text = survivor_row.get("nl") or ""
    target_text = _target_block(survivor_row)
    rendered = _render_harmony(user_text, target_text)
    fam_source = user_text + " " + (survivor_row.get("spec_text") or "")
    return {
        "text": rendered,
        "seed_key": survivor_row.get("seed_key"),
        "family": tag_family(fam_source),
    }


def build_sft_file(survivor_dirs: list, out_path, min_tier: int | None = None,
                   apply_exclusions: bool | None = None) -> int:
    """Write harmony-rendered JSONL for survivors across survivor_dirs.
    Returns the number of rows written. Robust to empty/missing dirs (writes
    an empty file, returns 0).

    min_tier filters on the w4_corpus quality grade (3=diamond, 2=gold,
    1=silver, 0=bronze); None keeps every row. Each emitted example carries
    "tier_name" and "arm" so a train can stratify without re-deriving them.
    """
    survivors = load_survivors(survivor_dirs, apply_exclusions=apply_exclusions)
    if min_tier is not None:
        survivors = w4_corpus.grade_corpus(survivors)
        survivors = [r for r in survivors if r["tier"] >= min_tier]
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    n = 0
    with open(out_path, "w") as f:
        for row in survivors:
            example = to_harmony_sft(row)
            if "tier_name" in row:
                example["tier_name"] = row["tier_name"]
                example["arm"] = row["arm"]
            f.write(json.dumps(example) + "\n")
            n += 1
    return n


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

DEFAULT_HOLDOUT = Path("corpus/holdout_30.json")


def _fmt_stats(stats: dict) -> str:
    if stats["median"] is None:
        return "n=0"
    return f"n={stats['n']} med={stats['median']:.2f} p25={stats['p25']:.2f} p75={stats['p75']:.2f} mean={stats['mean']:.2f}"


def _print_collapse_table(report: dict) -> None:
    print(f"survivors={report['survivor_count']} holdout={report['holdout_count']} "
          f"collapse_flag={report['collapse_flag']} (threshold ratio={report['collapse_ratio_threshold']})")
    print(f"complexity_score  survivors[{_fmt_stats(report['complexity_score']['survivors'])}]  "
          f"holdout[{_fmt_stats(report['complexity_score']['holdout'])}]")
    for k, v in report["features"].items():
        print(f"  {k:20s} survivors[{_fmt_stats(v['survivors'])}]  holdout[{_fmt_stats(v['holdout'])}]  ratio={v['median_ratio']}")


def _print_family_table(result: dict) -> None:
    print("survivor family counts:", result["survivor_family_counts"])
    print("holdout family counts:", result["holdout_family_counts"])
    print("family overlap:", result["family_overlap"])


def main(argv=None):
    import argparse

    parser = argparse.ArgumentParser(prog="python3 -m harness.corpus_prep")
    parser.add_argument("mode", choices=["collapse", "family", "sft"])
    parser.add_argument("--survivor-dirs", nargs="+", required=True,
                         help="Glob(s) of run dirs containing w2_survivors.jsonl")
    parser.add_argument("--holdout", default=str(DEFAULT_HOLDOUT))
    parser.add_argument("--out", default=None)
    parser.add_argument("--min-tier", type=int, default=None,
                        help="sft mode: keep rows at or above this w4_corpus tier "
                             "(3=diamond, 2=gold, 1=silver, 0=bronze)")
    args = parser.parse_args(argv)

    if args.mode == "collapse":
        report = collapse_report(args.survivor_dirs, args.holdout)
        out_path = Path(args.out) if args.out else Path("results/analysis/collapse_report.json")
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(report, indent=2))
        _print_collapse_table(report)
        print(f"wrote {out_path}")
    elif args.mode == "family":
        result = tag_corpus(args.survivor_dirs, args.holdout)
        out_path = Path(args.out) if args.out else Path("results/analysis/family_tags.json")
        out_path.parent.mkdir(parents=True, exist_ok=True)
        summary = {k: v for k, v in result.items() if k not in ("survivor_tags", "holdout_tags")}
        out_path.write_text(json.dumps(summary, indent=2))
        survivor_tags_path = out_path.parent / "survivor_family_tags.jsonl"
        with open(survivor_tags_path, "w") as f:
            for row in result["survivor_tags"]:
                f.write(json.dumps(row) + "\n")
        holdout_tags_path = out_path.parent / "holdout_family_tags.jsonl"
        with open(holdout_tags_path, "w") as f:
            for row in result["holdout_tags"]:
                f.write(json.dumps(row) + "\n")
        _print_family_table(result)
        print(f"wrote {out_path}, {survivor_tags_path}, {holdout_tags_path}")
    elif args.mode == "sft":
        out_path = Path(args.out) if args.out else Path("results/analysis/sft_harmony.jsonl")
        n = build_sft_file(args.survivor_dirs, out_path, min_tier=args.min_tier)
        print(f"wrote {n} rows -> {out_path}")


if __name__ == "__main__":
    main()


# ---------------------------------------------------------------------------
# W2.6 repair-shaped SFT (PLAN.md Stage-2 Round 3, Amendment 16)
# ---------------------------------------------------------------------------

def to_repair_harmony_sft(triple: dict) -> dict:
    """Convert an accepted repair_harvest triple into a harmony-rendered
    training example whose USER side is the SAME repair prompt the eval and
    the harvest used (gen_eval.build_repair_prompt: broken module + error
    evidence) and whose TARGET is the verified minimal fix. Training on the
    exact eval prompt shape is the point -- the v2_sft2 corpus taught
    generation format to a repair task (Amendment 16 cause #1)."""
    from .gen_eval import build_repair_prompt
    user_text = build_repair_prompt(triple["broken_text"], triple["error_evidence"])
    target_text = f"```tla\n{triple['fixed_text']}\n```"
    return {
        "text": _render_harmony(user_text, target_text),
        "seed_key": triple.get("seed_key"),
        "spec_sha": triple.get("spec_sha"),
        "diff_ratio": triple.get("diff_ratio"),
        "family": tag_family(triple.get("fixed_text") or ""),
    }


def build_repair_sft_file(triples_path, out_path, max_per_spec: int = 3) -> int:
    """Render harvest_triples.jsonl to a harmony SFT file. max_per_spec caps
    duplicates of the same (spec, corruption) so one spec's k accepted samples
    don't dominate the corpus (the fixes are near-identical by construction --
    the diff-minimality gate guarantees it)."""
    from collections import defaultdict
    out_path = Path(out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    per_spec = defaultdict(int)
    n = 0
    with open(triples_path) as fin, open(out_path, "w") as fout:
        for line in fin:
            if not line.strip():
                continue
            t = json.loads(line)
            if per_spec[t["spec_sha"]] >= max_per_spec:
                continue
            per_spec[t["spec_sha"]] += 1
            fout.write(json.dumps(to_repair_harmony_sft(t)) + "\n")
            n += 1
    return n
