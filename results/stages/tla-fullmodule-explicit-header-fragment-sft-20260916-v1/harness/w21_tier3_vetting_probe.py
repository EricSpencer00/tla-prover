"""W2.1 tier3-recovery lever vetting probes (small-sample, empirical).

NOT part of the frozen W2.1 funnel and does NOT touch corpus/, PLAN.md, or
the committed corpora-v2 manifests. Reads results/runs/w21-tlc-20260709 and
data/chattla-corpora-v2/manifest_*.jsonl (read-only), runs bounded TLC on a
small deterministic sample per lever, and appends evidence rows (Rule 8) to
results/runs/w21-tier3-recovery-vetting/rows.jsonl.

Serial, nice-19, foreground. Run with:
  python -m harness.w21_tier3_vetting_probe <lever> [--limit N]
levers: template_cfg, sibling_cfg, dep_staging, vacuity_novac, vacuity_states
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import shutil
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
RAW = Path("/Users/eric/GitHub/tla-dataset-pipeline/data/raw")
CORPUS_DIR = REPO / "data" / "chattla-corpora-v2"
OUT_DIR = REPO / "results" / "runs" / "w21-tier3-recovery-vetting"
SEED = 20260709

from .runner import check_tlc, module_name  # noqa: E402
from .w21_funnel import BOUNDED_TLC_TIMEOUT_S, bounded_tlc_flags, classify_tier3  # noqa: E402
from .tier3_recovery import (  # noqa: E402
    cfg_matches_module,
    find_matching_sibling_cfg,
    missing_module_names,
    template_cfg_for_module,
    template_cfg_symmetric_sets,
)


def _append_row(row: dict):
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    with open(OUT_DIR / "rows.jsonl", "a") as fh:
        fh.write(json.dumps(row) + "\n")


def _sample(items: list, n: int, seed: int = SEED) -> list:
    rnd = random.Random(seed)
    items = sorted(items)  # deterministic base order before shuffling
    idx = list(range(len(items)))
    rnd.shuffle(idx)
    return [items[i] for i in idx[:n]]


def _run_tlc_in_workdir(mod: str, cfg_text: str, workdir: Path, timeout: int):
    return check_tlc(mod, cfg_text, workdir, timeout, extra_flags=bounded_tlc_flags())


# --- Lever 1: template cfg for tier2 (no-cfg) files ------------------------

def probe_template_cfg(limit: int, timeout: int):
    rows = [json.loads(l) for l in open(CORPUS_DIR / "manifest_tier2_sany.jsonl")]
    paths = [r["source"].removeprefix("data/raw/") for r in rows]
    sample = _sample(paths, limit)
    print(f"[template_cfg] sample={len(sample)} of {len(paths)} tier2 files")
    for rel in sample:
        f = RAW / rel
        text = f.read_text(errors="replace")
        mod = module_name(text)
        row = {"lever": "template_cfg", "path": rel, "module": mod}
        if not mod:
            row["outcome"] = "no_module_header"
            _append_row(row)
            continue
        cfg_text, bound_constants = template_cfg_symmetric_sets(text)
        if not cfg_text:
            row["outcome"] = "no_spec_or_init_next"
            _append_row(row)
            continue
        row["bound_constants"] = bound_constants
        row["generated_cfg"] = cfg_text
        workdir = f.parent
        (workdir / f"{mod}.tla").write_text(text)
        (workdir / f"{mod}.templated.cfg").write_text(cfg_text)
        try:
            status, vac, out, dt = _run_tlc_in_workdir(mod, cfg_text, workdir, timeout)
        except Exception as e:  # noqa: BLE001
            row["outcome"] = f"exception:{e}"
            _append_row(row)
            continue
        tier3 = classify_tier3(status, vac)
        row.update(tlc_status=status, vacuity=vac, dt_s=round(dt, 2), tier3=tier3,
                   outcome="recovered_nonvacuous" if tier3 == "tier3_tlc_pass" else
                   ("recovered_vacuous" if tier3 == "tier3_tlc_vacuous" else "not_recovered"))
        _append_row(row)
        print(f"  {rel}: {status} vac={vac} -> {row['outcome']}")


# --- Lever 2: smarter cfg pairing for tier3_tlc_fail ------------------------

def probe_sibling_cfg(limit: int, timeout: int):
    manifest = [json.loads(l) for l in open(CORPUS_DIR / "manifest_tier1_sany_cfg.jsonl")]
    fails = [r for r in manifest if r.get("tier3") == "tier3_tlc_fail"]
    paths = [r["source"].removeprefix("data/raw/") for r in fails]
    sample = _sample(paths, limit)
    print(f"[sibling_cfg] sample={len(sample)} of {len(paths)} tier3_tlc_fail files")
    for rel in sample:
        f = RAW / rel
        text = f.read_text(errors="replace")
        mod = module_name(text)
        row = {"lever": "sibling_cfg", "path": rel, "module": mod}
        if not mod:
            row["outcome"] = "no_module_header"
            _append_row(row)
            continue
        cfg_candidates = list(f.parent.glob("*.cfg"))
        used_cfg = next((c for c in cfg_candidates if c.stem == mod or c.stem == f.stem), None) \
            or (cfg_candidates[0] if cfg_candidates else None)
        if used_cfg is None:
            row["outcome"] = "no_cfg_candidates"
            _append_row(row)
            continue
        row["used_cfg"] = str(used_cfg.relative_to(RAW))
        row["n_sibling_cfgs"] = len(cfg_candidates)
        row["used_cfg_matches"] = cfg_matches_module(used_cfg.read_text(errors="replace"), text)
        better = find_matching_sibling_cfg(text, used_cfg, cfg_candidates)
        if better is None:
            row["outcome"] = "no_better_sibling" if row["used_cfg_matches"] else "no_matching_sibling_found"
            _append_row(row)
            continue
        row["swapped_to_cfg"] = str(better.relative_to(RAW))
        cfg_text = better.read_text(errors="replace")
        workdir = f.parent
        (workdir / f"{mod}.tla").write_text(text)
        try:
            status, vac, out, dt = _run_tlc_in_workdir(mod, cfg_text, workdir, timeout)
        except Exception as e:  # noqa: BLE001
            row["outcome"] = f"exception:{e}"
            _append_row(row)
            continue
        tier3 = classify_tier3(status, vac)
        row.update(tlc_status=status, vacuity=vac, dt_s=round(dt, 2), tier3=tier3,
                   outcome="recovered_nonvacuous" if tier3 == "tier3_tlc_pass" else
                   ("recovered_vacuous" if tier3 == "tier3_tlc_vacuous" else "still_failed"))
        _append_row(row)
        print(f"  {rel}: swapped -> {status} vac={vac} -> {row['outcome']}")


# --- Lever 3: dependency staging for missing-module fails -------------------

def probe_dep_staging(limit: int, timeout: int):
    manifest = [json.loads(l) for l in open(CORPUS_DIR / "manifest_tier1_sany_cfg.jsonl")]
    fails = [r for r in manifest if r.get("tier3") == "tier3_tlc_fail"]
    candidates = []
    for r in fails:
        rel = r["source"].removeprefix("data/raw/")
        f = RAW / rel
        text = f.read_text(errors="replace")
        # cheap pre-filter: does this file EXTEND/INSTANCE a name that is
        # NOT a standard module and has no .tla with that name as a sibling?
        ext = re.findall(r"^\s*EXTENDS\s+(.+)$", text, re.M)
        names = set()
        for line in ext:
            names |= {n.strip() for n in re.split(r"[,\s]+", line) if n.strip()}
        sibling_stems = {p.stem for p in f.parent.glob("*.tla")}
        std = {"Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "Bags",
               "TLC", "TLCExt", "Randomization", "RealTime", "Toolbox", "Json"}
        missing = names - std - sibling_stems - {module_name(text) or ""}
        if missing:
            candidates.append((rel, sorted(missing)))
    sample = _sample(candidates, min(limit, len(candidates)))
    print(f"[dep_staging] sample={len(sample)} of {len(candidates)} candidate missing-EXTENDS files "
          f"(of {len(fails)} total tier3_tlc_fail)")
    for rel, missing_extends in sample:
        f = RAW / rel
        text = f.read_text(errors="replace")
        mod = module_name(text)
        row = {"lever": "dep_staging", "path": rel, "module": mod,
               "missing_extends_guess": missing_extends}
        # search the whole raw tree (same repo first) for a .tla whose module
        # name matches one of the missing names -- cheap, deterministic, and
        # mirrors what runner._write_local_deps does for the frozen corpus.
        repo_root = rel.split("/")[0] + "/" + rel.split("/")[1] if "/" in rel else rel
        search_root = RAW / repo_root if (RAW / repo_root).exists() else RAW
        staged = []
        for name in missing_extends:
            hit = None
            for cand in search_root.rglob("*.tla"):
                if cand == f:
                    continue
                try:
                    ctext = cand.read_text(errors="replace")
                except Exception:  # noqa: BLE001
                    continue
                if module_name(ctext) == name:
                    hit = cand
                    break
            if hit:
                staged.append((name, str(hit.relative_to(RAW))))
        row["staged_deps_found"] = staged
        if not staged:
            row["outcome"] = "no_dep_found_in_repo"
            _append_row(row)
            continue
        cfg_candidates = list(f.parent.glob("*.cfg"))
        used_cfg = next((c for c in cfg_candidates if c.stem == mod or c.stem == f.stem), None) \
            or (cfg_candidates[0] if cfg_candidates else None)
        if used_cfg is None or mod is None:
            row["outcome"] = "no_cfg_or_module"
            _append_row(row)
            continue
        cfg_text = used_cfg.read_text(errors="replace")
        workdir = f.parent
        copied = []
        for name, dep_rel in staged:
            dst = workdir / f"{name}.tla"
            if not dst.exists():
                shutil.copy2(RAW / dep_rel, dst)
                copied.append(str(dst))
        (workdir / f"{mod}.tla").write_text(text)
        try:
            status, vac, out, dt = _run_tlc_in_workdir(mod, cfg_text, workdir, timeout)
        except Exception as e:  # noqa: BLE001
            row["outcome"] = f"exception:{e}"
            row["copied_dep_files"] = copied
            _append_row(row)
            continue
        finally:
            for c in copied:
                Path(c).unlink(missing_ok=True)
        tier3 = classify_tier3(status, vac)
        row.update(tlc_status=status, vacuity=vac, dt_s=round(dt, 2), tier3=tier3,
                   copied_dep_files=copied,
                   outcome="recovered_nonvacuous" if tier3 == "tier3_tlc_pass" else
                   ("recovered_vacuous" if tier3 == "tier3_tlc_vacuous" else "still_failed"))
        _append_row(row)
        print(f"  {rel}: staged {[n for n,_ in staged]} -> {status} -> {row['outcome']}")


# --- Lever 4a: vacuity rescue, no_invariant_or_property_in_cfg -------------

def probe_vacuity_novac(limit: int, timeout: int):
    tlc_rows = {}
    for l in open(REPO / "results" / "runs" / "w21-tlc-20260709" / "tlc.jsonl"):
        r = json.loads(l)
        tlc_rows[r["path"]] = r  # last-write-wins
    cands = [p for p, r in tlc_rows.items()
             if r.get("tier3") == "tier3_tlc_vacuous"
             and "no_invariant_or_property_in_cfg" in (r.get("vacuity") or [])]
    sample = _sample(cands, min(limit, len(cands)))
    print(f"[vacuity_novac] sample={len(sample)} of {len(cands)} no_invariant_or_property_in_cfg files")
    for rel in sample:
        f = RAW / rel
        text = f.read_text(errors="replace")
        mod = module_name(text)
        row = {"lever": "vacuity_novac", "path": rel, "module": mod}
        if not mod:
            row["outcome"] = "no_module_header"
            _append_row(row)
            continue
        cfg_candidates = list(f.parent.glob("*.cfg"))
        used_cfg = next((c for c in cfg_candidates if c.stem == mod or c.stem == f.stem), None) \
            or (cfg_candidates[0] if cfg_candidates else None)
        if used_cfg is None:
            row["outcome"] = "no_cfg"
            _append_row(row)
            continue
        base_cfg = used_cfg.read_text(errors="replace")
        from .tier3_recovery import parse_module
        facts = parse_module(text)
        if not facts["invariant_name"]:
            row["outcome"] = "no_typeok_like_invariant_in_module"
            _append_row(row)
            continue
        injected_cfg = base_cfg.rstrip() + f"\nINVARIANT {facts['invariant_name']}\n"
        row["injected_invariant"] = facts["invariant_name"]
        workdir = f.parent
        (workdir / f"{mod}.tla").write_text(text)
        try:
            status, vac, out, dt = _run_tlc_in_workdir(mod, injected_cfg, workdir, timeout)
        except Exception as e:  # noqa: BLE001
            row["outcome"] = f"exception:{e}"
            _append_row(row)
            continue
        tier3 = classify_tier3(status, vac)
        row.update(tlc_status=status, vacuity=vac, dt_s=round(dt, 2), tier3=tier3,
                   outcome="recovered_nonvacuous" if tier3 == "tier3_tlc_pass" else
                   ("still_vacuous_other_reason" if tier3 == "tier3_tlc_vacuous" else "not_recovered"))
        _append_row(row)
        print(f"  {rel}: injected {facts['invariant_name']} -> {status} vac={vac} -> {row['outcome']}")


# --- Lever 4b: vacuity rescue, only_1_distinct_states ----------------------

def probe_vacuity_states(limit: int, timeout: int):
    tlc_rows = {}
    for l in open(REPO / "results" / "runs" / "w21-tlc-20260709" / "tlc.jsonl"):
        r = json.loads(l)
        tlc_rows[r["path"]] = r
    cands = [p for p, r in tlc_rows.items()
             if r.get("tier3") == "tier3_tlc_vacuous"
             and any(v.startswith("only_1_distinct_states") for v in (r.get("vacuity") or []))]
    sample = _sample(cands, min(limit, len(cands)))
    print(f"[vacuity_states] sample={len(sample)} of {len(cands)} only_1_distinct_states files")
    for rel in sample:
        f = RAW / rel
        text = f.read_text(errors="replace")
        mod = module_name(text)
        row = {"lever": "vacuity_states", "path": rel, "module": mod}
        if not mod:
            row["outcome"] = "no_module_header"
            _append_row(row)
            continue
        cfg_text, bound = template_cfg_symmetric_sets(text, set_size=5, int_max=6)
        if not cfg_text:
            row["outcome"] = "no_spec_or_init_next"
            _append_row(row)
            continue
        row["bound_constants"] = bound
        row["generated_cfg"] = cfg_text
        workdir = f.parent
        (workdir / f"{mod}.tla").write_text(text)
        try:
            status, vac, out, dt = _run_tlc_in_workdir(mod, cfg_text, workdir, timeout)
        except Exception as e:  # noqa: BLE001
            row["outcome"] = f"exception:{e}"
            _append_row(row)
            continue
        tier3 = classify_tier3(status, vac)
        row.update(tlc_status=status, vacuity=vac, dt_s=round(dt, 2), tier3=tier3,
                   outcome="recovered_nonvacuous" if tier3 == "tier3_tlc_pass" else
                   ("still_vacuous" if tier3 == "tier3_tlc_vacuous" else "not_recovered"))
        _append_row(row)
        print(f"  {rel}: larger-const template -> {status} vac={vac} -> {row['outcome']}")


LEVERS = {
    "template_cfg": probe_template_cfg,
    "sibling_cfg": probe_sibling_cfg,
    "dep_staging": probe_dep_staging,
    "vacuity_novac": probe_vacuity_novac,
    "vacuity_states": probe_vacuity_states,
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("lever", choices=list(LEVERS) + ["all"])
    ap.add_argument("--limit", type=int, default=25)
    ap.add_argument("--timeout", type=int, default=BOUNDED_TLC_TIMEOUT_S)
    a = ap.parse_args()
    try:
        os.nice(19)
    except PermissionError:
        pass
    if a.lever == "all":
        for name, fn in LEVERS.items():
            fn(a.limit, a.timeout)
    else:
        LEVERS[a.lever](a.limit, a.timeout)


if __name__ == "__main__":
    main()
