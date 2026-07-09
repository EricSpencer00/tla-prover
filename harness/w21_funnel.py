"""W2.1 funnel driver — chattla-corpora-v2 from the regenerated raw scrape.

Stages (each resumable; state lives under the run dir):
  dedup     exact-dup removal (normalized hash) over raw .tla files
  decontam  near-dup decontamination vs 206-corpus + tlaplus/examples
  sany      serial nice-19 SANY sweep over survivors (resumable ledger)
  assemble  tier directories + per-tier manifests + reports

Usage:
  python -m harness.w21_funnel <stage> --run-dir results/runs/w21-funnel-20260708 \
      --raw /Users/eric/GitHub/tla-dataset-pipeline/data/raw [--limit N]

Tiering (PLAN.md W2.1; SANY as the cheap quality gate — TLC/vacuity/judge
tiers are follow-on passes, disclosed in the summary):
  tier1_sany_cfg   SANY pass AND a sibling .cfg exists in the same source dir
  tier2_sany       SANY pass, no cfg
  discard_sany     SANY fail/timeout
  discard_dup      exact normalized duplicate of an earlier raw file
  discard_contam   near-dup of a canonical spec (Jaccard >= 0.65)
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
from pathlib import Path

from .corpora import (
    NEAR_DUP_THRESHOLD,
    SHINGLE_K,
    content_sha256,
    nearest_similarity,
    normalize_tla,
    normalized_hash,
    shingle_set,
)

BENCH = Path("/Users/eric/GitHub/tla_benchmark/data/tla_files")
EXAMPLES = Path("/Users/eric/GitHub/prove-TLA/tools/tlaplus-examples")
HOLDOUT = json.load(open(Path(__file__).parent.parent / "corpus" / "holdout_30.json"))["holdout_specs"]


def _read(p: Path) -> str:
    return p.read_text(errors="replace")


def load_canonical():
    canon = {}
    for f in sorted(BENCH.glob("*.tla")):
        canon[f"bench:{f.stem}"] = shingle_set(normalize_tla(_read(f)), SHINGLE_K)
    for f in sorted(EXAMPLES.rglob("*.tla")):
        canon[f"examples:{f.relative_to(EXAMPLES)}"] = shingle_set(normalize_tla(_read(f)), SHINGLE_K)
    return canon


def stage_dedup(raw: Path, run_dir: Path):
    seen: dict[str, str] = {}
    out = run_dir / "dedup.jsonl"
    with open(out, "w") as fh:
        for f in sorted(raw.rglob("*.tla")):
            rel = str(f.relative_to(raw))
            nh = normalized_hash(_read(f))
            rec = {"path": rel, "sha256": content_sha256(f), "normalized_hash": nh}
            if nh in seen:
                rec["verdict"] = "dup"
                rec["dup_of"] = seen[nh]
            else:
                rec["verdict"] = "unique"
                seen[nh] = rel
            fh.write(json.dumps(rec) + "\n")
    print(f"dedup: {len(seen)} unique of {sum(1 for _ in open(out))} .tla files -> {out}")


def stage_decontam(raw: Path, run_dir: Path):
    canon = load_canonical()
    print(f"canonical shingle sets: {len(canon)}")
    uniq = [json.loads(l) for l in open(run_dir / "dedup.jsonl") if json.loads(l)["verdict"] == "unique"]
    out = run_dir / "decontam.jsonl"
    done = set()
    if out.exists():
        done = {json.loads(l)["path"] for l in open(out)}
    with open(out, "a") as fh:
        for i, rec in enumerate(uniq):
            if rec["path"] in done:
                continue
            q = shingle_set(normalize_tla(_read(raw / rec["path"])), SHINGLE_K)
            name, score = nearest_similarity(q, canon)
            verdict = "contaminated" if score >= NEAR_DUP_THRESHOLD else "clean"
            fh.write(json.dumps({"path": rec["path"], "sha256": rec["sha256"],
                                 "nearest_canonical": name, "similarity": round(score, 4),
                                 "verdict": verdict}) + "\n")
            if (i + 1) % 200 == 0:
                fh.flush()
                print(f"  {i+1}/{len(uniq)}")
    n = sum(1 for _ in open(out))
    c = sum(1 for l in open(out) if json.loads(l)["verdict"] == "contaminated")
    print(f"decontam: {n} scored, {c} contaminated -> {out}")


def stage_sany(raw: Path, run_dir: Path, limit: int | None):
    os.nice(19)
    from .runner import check_sany
    survivors = [json.loads(l) for l in open(run_dir / "decontam.jsonl") if json.loads(l)["verdict"] == "clean"]
    out = run_dir / "sany.jsonl"
    done = {json.loads(l)["path"] for l in open(out)} if out.exists() else set()
    todo = [r for r in survivors if r["path"] not in done]
    if limit:
        todo = todo[:limit]
    print(f"sany: {len(done)} done, {len(todo)} this chunk, {len(survivors)} total")
    with open(out, "a") as fh:
        for rec in todo:
            f = raw / rec["path"]
            st, _, dt = check_sany(f, f.parent, 60)
            fh.write(json.dumps({"path": rec["path"], "sany": st, "dt_s": round(dt, 2)}) + "\n")
            fh.flush()
    print(f"sany chunk complete -> {out} ({sum(1 for _ in open(out))} rows)")


def stage_assemble(raw: Path, run_dir: Path, corpus_dir: Path):
    dedup = {r["path"]: r for r in map(json.loads, open(run_dir / "dedup.jsonl"))}
    decon = {r["path"]: r for r in map(json.loads, open(run_dir / "decontam.jsonl"))}
    sany = {r["path"]: r for r in map(json.loads, open(run_dir / "sany.jsonl"))}
    corpus_dir.mkdir(parents=True, exist_ok=True)
    manifests = {t: open(corpus_dir / f"manifest_{t}.jsonl", "w") for t in
                 ("tier1_sany_cfg", "tier2_sany", "discard_sany", "discard_dup", "discard_contam")}
    counts: dict[str, int] = {}
    for path, drec in dedup.items():
        if drec["verdict"] == "dup":
            tier, extra = "discard_dup", {"dup_of": drec["dup_of"]}
        else:
            c = decon[path]
            if c["verdict"] == "contaminated":
                tier, extra = "discard_contam", {"nearest_canonical": c["nearest_canonical"],
                                                 "similarity": c["similarity"]}
            else:
                s = sany[path]
                if s["sany"] == "pass":
                    has_cfg = any((raw / path).parent.glob("*.cfg"))
                    tier = "tier1_sany_cfg" if has_cfg else "tier2_sany"
                    extra = {"sany_dt_s": s["dt_s"], "has_cfg": has_cfg}
                else:
                    tier, extra = "discard_sany", {"sany": s["sany"]}
        counts[tier] = counts.get(tier, 0) + 1
        c2 = decon.get(path, {})
        row = {"source": f"data/raw/{path}", "module": Path(path).stem,
               "content_sha256": drec["sha256"], "tier": tier,
               "decontam_verdict": c2.get("verdict", "n/a (dup removed first)"),
               "nearest_canonical": c2.get("nearest_canonical"),
               "nearest_similarity": c2.get("similarity"), **extra}
        manifests[tier].write(json.dumps(row) + "\n")
        if tier.startswith("tier"):
            dst = corpus_dir / tier / path
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(raw / path, dst)
            for cfg in (raw / path).parent.glob("*.cfg"):
                shutil.copy2(cfg, dst.parent / cfg.name)
    for fh in manifests.values():
        fh.close()
    print(json.dumps(counts, indent=2))
    (run_dir / "tier_counts.json").write_text(json.dumps(counts, indent=2))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("stage", choices=["dedup", "decontam", "sany", "assemble"])
    ap.add_argument("--run-dir", required=True, type=Path)
    ap.add_argument("--raw", required=True, type=Path)
    ap.add_argument("--corpus-dir", type=Path,
                    default=Path("/Users/eric/GitHub/prove-TLA/data/chattla-corpora-v2"))
    ap.add_argument("--limit", type=int)
    a = ap.parse_args()
    a.run_dir.mkdir(parents=True, exist_ok=True)
    if a.stage == "dedup":
        stage_dedup(a.raw, a.run_dir)
    elif a.stage == "decontam":
        stage_decontam(a.raw, a.run_dir)
    elif a.stage == "sany":
        stage_sany(a.raw, a.run_dir, a.limit)
    else:
        stage_assemble(a.raw, a.run_dir, a.corpus_dir)


if __name__ == "__main__":
    main()
