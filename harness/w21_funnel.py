"""W2.1 funnel driver — chattla-corpora-v2 from the regenerated raw scrape.

Stages (each resumable; state lives under the run dir):
  dedup     exact-dup removal (normalized hash) over raw .tla files
  decontam  near-dup decontamination vs 206-corpus + tlaplus/examples
  sany      serial nice-19 SANY sweep over survivors (resumable ledger)
  tlc       templated bounded TLC + vacuity traps over tier1_sany_cfg
            (separate run dir, e.g. results/runs/w21-tlc-<date>; reads the
            committed tier1 manifest, NOT the sany stage's own run dir)
  assemble  tier directories + per-tier manifests + reports

Usage:
  python -m harness.w21_funnel <stage> --run-dir results/runs/w21-funnel-20260708 \
      --raw /Users/eric/GitHub/tla-dataset-pipeline/data/raw [--limit N]

  python -m harness.w21_funnel tlc --run-dir results/runs/w21-tlc-20260709 \
      --raw /Users/eric/GitHub/tla-dataset-pipeline/data/raw \
      --manifest data/chattla-corpora-v2/manifest_tier1_sany_cfg.jsonl \
      [--limit N] [--timeout SECONDS]

Tiering (PLAN.md W2.1; SANY as the cheap quality gate — TLC/vacuity/judge
tiers are follow-on passes, disclosed in the summary):
  tier1_sany_cfg   SANY pass AND a sibling .cfg exists in the same source dir
  tier2_sany       SANY pass, no cfg
  discard_sany     SANY fail/timeout
  discard_dup      exact normalized duplicate of an earlier raw file
  discard_contam   near-dup of a canonical spec (Jaccard >= 0.65)

  tier3 verdicts (sub-tier of tier1_sany_cfg, PLAN.md "templated bounded TLC
  -> vacuity traps"; nothing in tier1 is deleted, files are marked):
    tier3_tlc_pass      bounded TLC pass, non-vacuous -> promotable
    tier3_tlc_vacuous   bounded TLC pass but trivially so (vacuity trap:
                        0/1-state run, no invariant/property configured, or
                        a syntactically-TRUE invariant) -> demoted
    tier3_tlc_fail      TLC ran and found a real invariant/deadlock/liveness
                        violation or errored -> stays tier1, marked
    tier3_tlc_timeout   did not finish within the bounded budget -> stays
                        tier1, marked
    tier3_tlc_no_cfg    no usable sibling .cfg found at sweep time -> stays
                        tier1, marked
    tier3_tlc_no_module no MODULE header found in the file -> stays tier1
"""
from __future__ import annotations

import argparse
import json
import os
import re
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


# --- tier3: templated bounded TLC + vacuity traps -------------------------
#
# Tier1 files are arbitrary scraped repos, not corpus population-tagged
# specs -- there is no reference "expected runtime" the way runner.py's
# oracle sweep has via corpus/configs/policy.json. The "template" (PLAN.md
# W2.1) is therefore a single fixed budget applied uniformly: a short
# wall-clock cap (BOUNDED_TLC_TIMEOUT_S) *and* a state-space depth cap via
# TLC's -dfid (iterative-deepening DFS bounded search), so a file with a
# large/unbounded reachable state space returns a bounded verdict (timeout
# or partial-depth pass) instead of silently running full BFS to the wall
# on every file in a 779-file sweep. -dfid also naturally handles specs with
# no explicit state constraint in their .cfg (most scraped tier1 cfgs won't
# have one) without per-file tuning.
BOUNDED_TLC_TIMEOUT_S = 90
BOUNDED_TLC_DEPTH = 15


def bounded_tlc_flags():
    """extra_flags for runner.check_tlc: bounded iterative-deepening DFS.
    -dfid requires single-worker mode (TLC rejects -dfid with >1 worker,
    https://github.com/tlaplus/tlaplus/issues/548); check_tlc hardcodes
    "-workers 2" ahead of extra_flags, so "-workers 1" here as a LATER flag
    is required to override it -- confirmed empirically that TLC honors the
    last -workers value given (found while smoke-testing tier1 sample: every
    real tlaplus/tlaplus MC.tla file was erroring immediately without this)."""
    return ["-dfid", str(BOUNDED_TLC_DEPTH), "-workers", "1"]


def classify_tier3(status: str, vac: list[str]) -> str:
    """Map a runner.check_tlc (status, vacuity) result to a tier3 verdict.
    Vacuity trap: a nominal TLC pass with a vacuity flag (trivial invariant,
    0/1-state run, no invariant/property configured) is demoted separately
    from a genuine pass so it doesn't inflate the training-quality tier."""
    if status == "no_cfg":
        return "tier3_tlc_no_cfg"
    if status == "timeout":
        return "tier3_tlc_timeout"
    if status == "pass":
        return "tier3_tlc_vacuous" if vac else "tier3_tlc_pass"
    return "tier3_tlc_fail"


def _run_one_tlc(rel_path: str, raw: Path, timeout: int) -> dict:
    """Run bounded TLC on one tier1 file (in its own dir, sibling .cfg reused)."""
    from .runner import check_tlc, module_name

    f = raw / rel_path
    text = f.read_text(errors="replace")
    mod = module_name(text)
    if not mod:
        return {"path": rel_path, "tier3": "tier3_tlc_no_module", "tlc_status": "no_module",
                "vacuity": [], "dt_s": 0.0}
    cfg_candidates = list(f.parent.glob("*.cfg"))
    # prefer a same-stem cfg (module.cfg) if present, else the first sibling cfg
    cfg_file = next((c for c in cfg_candidates if c.stem == mod or c.stem == f.stem), None) \
        or (cfg_candidates[0] if cfg_candidates else None)
    if cfg_file is None:
        return {"path": rel_path, "tier3": "tier3_tlc_no_cfg", "tlc_status": "no_cfg",
                "vacuity": [], "dt_s": 0.0}
    cfg_text = cfg_file.read_text(errors="replace")
    # TLC needs SPEC.tla / SPEC.cfg name-matched in its workdir; f's own
    # basename may differ from the declared module name, and the sibling
    # .cfg may be named for the file rather than the module -- write both
    # under the module name if not already present (do not overwrite an
    # existing same-name file that isn't ours).
    workdir = f.parent
    if not (workdir / f"{mod}.cfg").exists():
        (workdir / f"{mod}.cfg").write_text(cfg_text)
    if not (workdir / f"{mod}.tla").exists():
        (workdir / f"{mod}.tla").write_text(text)
    status, vac, out, dt = check_tlc(mod, cfg_text, workdir, timeout,
                                     extra_flags=bounded_tlc_flags())
    m_states = None
    sm = re.search(r"(\d+) distinct states found", out)
    if sm:
        m_states = int(sm.group(1))
    return {"path": rel_path, "tier3": classify_tier3(status, vac), "tlc_status": status,
            "vacuity": vac, "dt_s": round(dt, 2), "states_found": m_states}


def stage_tlc(raw: Path, run_dir: Path, manifest_path: Path, limit: int | None,
               timeout: int = BOUNDED_TLC_TIMEOUT_S):
    """Resumable Rule-8 sweep: bounded TLC + vacuity traps over tier1_sany_cfg.
    Serial, nice-19 (caller sets os.nice(19) as sany stage does), per-file
    timeout, appends to run_dir/tlc.jsonl, skipping rows already recorded so
    a restart after a reboot picks up where it left off."""
    rows = [json.loads(l) for l in open(manifest_path)]
    todo_all = [r["source"].removeprefix("data/raw/") for r in rows]
    out = run_dir / "tlc.jsonl"
    done = {json.loads(l)["path"] for l in open(out)} if out.exists() else set()
    todo = [p for p in todo_all if p not in done]
    if limit:
        todo = todo[:limit]
    print(f"tlc: {len(done)} done, {len(todo)} this chunk, {len(todo_all)} total tier1 files")
    with open(out, "a") as fh:
        for i, rel_path in enumerate(todo):
            rec = _run_one_tlc(rel_path, raw, timeout)
            fh.write(json.dumps(rec) + "\n")
            fh.flush()
            if (i + 1) % 25 == 0:
                print(f"  {i+1}/{len(todo)}")
    n = sum(1 for _ in open(out))
    print(f"tlc chunk complete -> {out} ({n} rows)")


def stage_assemble(raw: Path, run_dir: Path, corpus_dir: Path):
    dedup = {r["path"]: r for r in map(json.loads, open(run_dir / "dedup.jsonl"))}
    decon = {r["path"]: r for r in map(json.loads, open(run_dir / "decontam.jsonl"))}
    sany = {r["path"]: r for r in map(json.loads, open(run_dir / "sany.jsonl"))}
    # TLC tier rows are optional: present once stage_tlc has swept tier1.
    # Restarted sweeps append duplicate rows; last write wins.
    tlc_file = run_dir / "tlc.jsonl"
    tlc = {r["path"]: r for r in map(json.loads, open(tlc_file))} if tlc_file.exists() else {}
    corpus_dir.mkdir(parents=True, exist_ok=True)
    manifests = {t: open(corpus_dir / f"manifest_{t}.jsonl", "w") for t in
                 ("tier1_sany_cfg", "tier2_sany", "discard_sany", "discard_dup", "discard_contam")
                 + (("tier3_tlc",) if tlc else ())}
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
                    t3 = tlc.get(path)
                    if t3:
                        extra.update(tier3=t3["tier3"], tlc_status=t3["tlc_status"],
                                     tlc_vacuity=t3.get("vacuity"),
                                     tlc_states_found=t3.get("states_found"))
                        if t3["tier3"] == "tier3_tlc_pass":
                            tier = "tier3_tlc"
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
    ap.add_argument("stage", choices=["dedup", "decontam", "sany", "tlc", "assemble"])
    ap.add_argument("--run-dir", required=True, type=Path)
    ap.add_argument("--raw", required=True, type=Path)
    ap.add_argument("--corpus-dir", type=Path,
                    default=Path("/Users/eric/GitHub/prove-TLA/data/chattla-corpora-v2"))
    ap.add_argument("--manifest", type=Path,
                    default=Path("/Users/eric/GitHub/prove-TLA/data/chattla-corpora-v2/manifest_tier1_sany_cfg.jsonl"),
                    help="tier1 manifest to sweep (tlc stage)")
    ap.add_argument("--limit", type=int)
    ap.add_argument("--timeout", type=int, default=BOUNDED_TLC_TIMEOUT_S)
    a = ap.parse_args()
    a.run_dir.mkdir(parents=True, exist_ok=True)
    if a.stage == "dedup":
        stage_dedup(a.raw, a.run_dir)
    elif a.stage == "decontam":
        stage_decontam(a.raw, a.run_dir)
    elif a.stage == "sany":
        stage_sany(a.raw, a.run_dir, a.limit)
    elif a.stage == "tlc":
        try:
            os.nice(19)
        except PermissionError:
            pass  # already at/above nice 19 (e.g. launched under `nice -n 19` externally)
        stage_tlc(a.raw, a.run_dir, a.manifest, a.limit, a.timeout)
    else:
        stage_assemble(a.raw, a.run_dir, a.corpus_dir)


if __name__ == "__main__":
    main()
